package de.wiesler;

public class Classifier {
    public static final int STORAGE_SIZE = (1 << Constants.LOG_MAX_BUCKETS);

    private final Tree tree;
    private final int num_buckets;
    private final int[] sorted_splitters;
    private final boolean equal_buckets;

    public Classifier(int[] sorted_splitters, int[] tree, int log_buckets, boolean equal_buckets) {
        assert (log_buckets <= Constants.LOG_MAX_BUCKETS + 1);
        int num_buckets = 1 << log_buckets;

        int num_splitters = num_buckets - 1;
        sorted_splitters[num_splitters] = sorted_splitters[num_splitters - 1];
        if (equal_buckets) {
            num_buckets = 2 * num_buckets;
        }

        this.tree = new Tree(sorted_splitters, tree, log_buckets);
        this.sorted_splitters = sorted_splitters;
        this.num_buckets = num_buckets;
        this.equal_buckets = equal_buckets;
    }

    public static Classifier from_sorted_samples(
            int[] values,
            int start,
            int end,
            int[] splitters,
            int[] tree,
            int num_buckets,
            int step
    ) {
        int splitter = start + step - 1;
        int offset = 0;
        // Select num_buckets - 1 splitters with step size step, make unique
        splitters[offset] = values[splitter];
        for (int i = 2; i < num_buckets; ++i) {
            splitter += step;
            if (Constants.cmp(splitters[offset], values[splitter])) {
                offset += 1;
                splitters[offset] = values[splitter];
            }
        }

        if (offset == 0) {
            return null;
        }

        // Check for duplicate splitters
        int splitter_count = offset + 1;
        int max_splitters = num_buckets - 1;
        boolean use_equal_buckets = (max_splitters - splitter_count) >= Constants.EQUAL_BUCKETS_THRESHOLD;

        // Fill the array to the next power of two
        int log_buckets = Constants.log2(splitter_count) + 1;
        int actual_num_buckets = 1 << log_buckets;
        assert (actual_num_buckets <= splitters.length);
        assert (splitter_count < actual_num_buckets);

        for (int i = splitter_count; i < actual_num_buckets; ++i) {
            splitters[i] = values[splitter];
        }

        return new Classifier(splitters, tree, log_buckets, use_equal_buckets);
    }

    public int num_buckets() {
        return this.num_buckets;
    }

    public boolean equal_buckets() {
        return this.equal_buckets;
    }

    public int classify(int value) {
        int index = this.tree.classify(value);
        int bucket;
        if (this.equal_buckets) {
            int bucket_index = index - this.num_buckets / 2;
            boolean equal_to_splitter = !Constants.cmp(value, this.sorted_splitters[bucket_index]);
            bucket = 2 * index + Constants.toInt(equal_to_splitter) - this.num_buckets;
        } else {
            bucket = index - this.num_buckets;
        }
        assert (bucket < this.num_buckets);
        return bucket;
    }

    public void classify_all(int[] values, int begin, int end, int[] indices) {
        assert (this.num_buckets == 1 << (this.tree.log_buckets() + Constants.toInt(this.equal_buckets)));
        this.tree.classify_all(values, begin, end, indices);
        if (this.equal_buckets) {
            for (int i = 0; i < indices.length; ++i) {
                final int value = values[begin + i];
                final int index = indices[i];
                final int bucket = index - this.num_buckets / 2;
                final boolean equal_to_splitter = !Constants.cmp(value, this.sorted_splitters[bucket]);
                indices[i] = 2 * index + Constants.toInt(equal_to_splitter);
            }
        }
        for (int i = 0; i < indices.length; ++i) {
            indices[i] -= this.num_buckets;
            assert (indices[i] < this.num_buckets);
        }
    }


    public int classify_locally(int[] values, int begin, int end, int[] bucket_starts, Buffers buffers) {
        int write = begin;

        {
            final int BATCH_SIZE = 16;
            int i = begin;
            if (end - begin > BATCH_SIZE) {
                int cutoff = end - BATCH_SIZE;
                final int[] indices = new int[BATCH_SIZE];
                while (i <= cutoff) {
                    this.classify_all(values, i, i + BATCH_SIZE, indices);

                    for (int j = 0; j < indices.length; ++j) {
                        int bucket = indices[j];
                        int value = values[i + j];
                        if (buffers.push(value, bucket, values, write, end)) {
                            write += Buffers.BUFFER_SIZE;
                            bucket_starts[bucket] += Buffers.BUFFER_SIZE;
                        }
                    }

                    i += BATCH_SIZE;
                }
            }

            for (; i < end; ++i) {
                int value = values[i];
                int bucket = this.classify(value);
                if (buffers.push(value, bucket, values, write, end)) {
                    write += Buffers.BUFFER_SIZE;
                    bucket_starts[bucket] += Buffers.BUFFER_SIZE;
                }
            }
        }

        {
            // bucket_starts contains the bucket counts without buffer contents
            // Calculate bucket starts
            int sum = 0;
            for (int i = 0; i < this.num_buckets; ++i) {
                // Add the partially filled buffers
                int size = bucket_starts[i] + buffers.len(i);

                // Exclusive prefix sum
                bucket_starts[i] = sum;
                sum += size;
            }
            bucket_starts[this.num_buckets] = sum;

            assert (sum == end - begin);
        }
        return write;
    }
}
