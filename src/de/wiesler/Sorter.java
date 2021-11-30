package de.wiesler;

public class Sorter {
    private static class PartitionResult {
        public int num_buckets;
        public boolean equal_buckets;

        public PartitionResult(int num_buckets, boolean equal_buckets) {
            this.num_buckets = num_buckets;
            this.equal_buckets = equal_buckets;
        }
    }

    private static class SampleResult {
        public int num_samples;
        public int num_buckets;
        public int step;

        public SampleResult(int num_samples, int num_buckets, int step) {
            this.num_samples = num_samples;
            this.num_buckets = num_buckets;
            this.step = step;
        }
    }

    private static SampleResult sample(int[] values, int start, int end, Storage storage) {
        int n = end - start;
        int log_buckets = Constants.log_buckets(n);
        int num_buckets = 1 << log_buckets;
        int step = Functions.max(1, Constants.oversampling_factor(n));
        int num_samples = Functions.min(step * num_buckets - 1, n / 2);

        Functions.select_n(values, start, end, num_samples);

        sort(values, start, start + num_samples, storage);

        return new SampleResult(num_samples, num_buckets, step);
    }

    public static void cleanup(
            final int[] values,
            final int begin,
            final int end,
            final Buffers buffers,
            final int[] bucket_starts,
            final BucketPointers bucket_pointers,
            final int num_buckets,
            final int[] overflow,
            final int overflow_bucket
    ) {
        final boolean is_last_level = end - begin <= Constants.SINGLE_LEVEL_THRESHOLD;
        final int max_offset = begin + Permute.max_offset(end - begin);

        for (int bucket = 0; bucket < num_buckets; ++bucket) {
            final int start = bucket_starts[bucket];
            final int stop = bucket_starts[bucket + 1];
            final int write = bucket_pointers.write(bucket);

            int head_start = start;
            int head_stop = Functions.min(Buffers.align_to_next_block_in(begin, start), stop);

            int tail_start;
            int tail_stop;

            // Overflow happened:
            // - write to an offset >= max_offset was stopped
            // - bucket pointer write increment returns the old value => write - BUFFER_SIZE >= max_offset
            // - this block is in the overflow buffer
            if (overflow_bucket != -1 && bucket == overflow_bucket && write >= Buffers.BUFFER_SIZE && write - Buffers.BUFFER_SIZE >= max_offset) {
                // Overflow

                // Overflow buffer has been written => write pointer must be at end of bucket
                // This gives stop <= write
                assert (Buffers.align_to_next_block_in(begin, stop) == write);

                tail_start = write - Buffers.BUFFER_SIZE;
                tail_stop = stop;

                int head_len = head_stop - head_start;

                // There must be space for at least block size elements
                assert (Buffers.BUFFER_SIZE <= (tail_stop - tail_start) + head_len);

                // Fill head: head.len() <= Buffers.BUFFER_SIZE
                assert (head_start + head_len <= head_stop);
                System.arraycopy(overflow, 0, values, head_start, head_len);
                head_start = head_stop;

                // Write remaining elements into tail
                int tail_elements = Buffers.BUFFER_SIZE - head_len;
                assert (start <= tail_start && tail_start + tail_elements <= tail_stop);
                System.arraycopy(overflow, head_len, values, tail_start, tail_elements);
                tail_start += tail_elements;
            } else if (stop < write) {
                if (Buffers.BUFFER_SIZE < stop - start) {
                    // Final block has been written
                    assert (Buffers.align_to_next_block_in(begin, stop) == write);

                    int overflow_len = write - stop;

                    // Must fit, no other empty space left
                    assert (overflow_len <= head_stop - head_start);

                    // Write overflow of last block to head
                    System.arraycopy(values, stop, values, head_start, overflow_len);
                    head_start += overflow_len;

                    // Tail is empty
                } else {
                    // Bucket is smaller than a block => head is the full block, no tail
                }

                tail_start = stop;
                tail_stop = stop;
            } else {
                // Default case: No overflow, write <= stop
                // This can't happen for buckets smaller than a block since they are never written to

                tail_start = write;
                tail_stop = stop;
            }

            // Write remaining elements from buffer to head and tail
            buffers.distribute(
                    bucket,
                    values,
                    head_start,
                    head_stop - head_start,
                    tail_start,
                    tail_stop - tail_start
            );

            if (stop - start <= 2 * Constants.BASE_CASE_SIZE || is_last_level) {
                base_case_sort(values, start, stop);
            }
        }
    }

    private static PartitionResult partition(int[] values, int begin, int end, int[] bucket_starts, Storage storage) {
        Classifier classifier;
        {
            SampleResult sample = sample(values, begin, end, storage);
            int num_samples = sample.num_samples;
            int num_buckets = sample.num_buckets;
            int step = sample.step;
            classifier = Classifier.from_sorted_samples(values, begin, begin + num_samples, storage.splitters, storage.tree, num_buckets, step);
        }

        if (classifier == null) {
            return null;
        }

        Buffers buffers = new Buffers();
        int first_empty_position = classifier.classify_locally(values, begin, end, bucket_starts, buffers);

        BucketPointers bucket_pointers = new BucketPointers();
        for (int bucket = 0; bucket < classifier.num_buckets(); ++bucket) {
            int start = Buffers.align_to_next_block_in(begin, bucket_starts[bucket]);
            int stop = Buffers.align_to_next_block_in(begin, bucket_starts[bucket + 1]);
            bucket_pointers.init(bucket, start, stop, first_empty_position);
        }

        int overflow_bucket = -1;
        for (int bucket = classifier.num_buckets(); bucket-- > 0; ) {
            int bucket_size = bucket_starts[bucket + 1] - bucket_starts[bucket];
            if (Buffers.BUFFER_SIZE < bucket_size) {
                overflow_bucket = bucket;
                break;
            }
        }

        int[] overflow = storage.overflow;
        Permute.permute(values, begin, end, classifier, bucket_pointers, storage.swap_1, storage.swap_2, overflow);

        cleanup(values,
                begin,
                end,
                buffers,
                bucket_starts,
                bucket_pointers,
                classifier.num_buckets(),
                overflow,
                overflow_bucket);

        return new PartitionResult(classifier.num_buckets(), classifier.equal_buckets());
    }

    private static void sample_sort(int[] values, int start, int end, Storage storage) {
        int[] bucket_starts = new int[Constants.MAX_BUCKETS + 1];
        PartitionResult partition = partition(values, start, end, bucket_starts, storage);

        if (partition == null) {
            fallback_sort(values, start, end);
            return;
        }

        int num_buckets = partition.num_buckets;
        boolean equal_buckets = partition.equal_buckets;

        if (end - start <= Constants.SINGLE_LEVEL_THRESHOLD) {
            return;
        }

        for (int i = 0; i < num_buckets; i += 1 + Constants.toInt(equal_buckets)) {
            int inner_start = bucket_starts[i];
            int inner_end = bucket_starts[i + 1];
            if (inner_end - inner_start > 2 * Constants.BASE_CASE_SIZE) {
                sample_sort(values, inner_start, inner_end, storage);
            }
        }

        if (equal_buckets) {
            int inner_start = bucket_starts[num_buckets - 1];
            int inner_end = bucket_starts[num_buckets];
            if (inner_end - inner_start > 2 * Constants.BASE_CASE_SIZE) {
                sample_sort(values, inner_start, inner_end, storage);
            }
        }
    }

    public static void sort(int[] values, int start, int end, Storage storage) {
        if (end - start <= 2 * Constants.BASE_CASE_SIZE) {
            base_case_sort(values, start, end);
        } else {
            sample_sort(values, start, end, storage);
        }
    }

    private static void fallback_sort(int[] values, int start, int end) {
        java.util.Arrays.sort(values, start, end);
    }

    private static void base_case_sort(int[] values, int start, int end) {
        fallback_sort(values, start, end);
    }

    /*@ public normal_behaviour
      @  ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
      @  ensures (\forall int i; 0<=i && i<values.length-1; values[i] <= values[i+1]);
      @  assignable values[*];
      @*/
    public static void sort(int[] values) {
        sort(values, 0, values.length, new Storage());
    }
}
