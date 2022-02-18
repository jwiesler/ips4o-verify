package de.wiesler;

public final class Cleanup {
    /*@ public normal_behaviour
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets);
      @
      @ ensures (\forall int b; \result < b < num_buckets; bucket_starts[b + 1] - bucket_starts[b] <= Buffers.BUFFER_SIZE);
      @
      @ assignable \strictly_nothing;
      @*/
    private static int find_overflow_bucket(final int[] bucket_starts, final int num_buckets) {
        int overflow_bucket = -1;

        /*@ loop_invariant 0 <= bucket && bucket <= num_buckets;
          @ loop_invariant (\forall int b; bucket <= b < num_buckets; bucket_starts[b + 1] - bucket_starts[b] <= Buffers.BUFFER_SIZE);
          @
          @ assignable \strictly_nothing;
          @
          @ decreases bucket;
          @*/
        for (int bucket = num_buckets; bucket-- > 0; ) {
            int bucket_size = bucket_starts[bucket + 1] - bucket_starts[bucket];
            if (Buffers.BUFFER_SIZE < bucket_size) {
                overflow_bucket = bucket;
                break;
            }
        }
        return overflow_bucket;
    }

    /*@ // For all buckets:
      @ // * Permutation of: (\old(written blocks) + buffer content) <-> (full block content)
      @ // * Bucket pointers have exactly enough space for buffer content (+ overflow)
      @ // Overflow happens <=> buffer is the last buffer with size >= 1 block and aligning this block leads to out of bounds
      @ public normal_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires Functions.isValidBucketStarts(bucket_starts, classifier.num_buckets);
      @ requires bucket_starts[classifier.num_buckets] == end - begin;
      @ requires classifier.num_buckets == buffers.buckets && classifier.num_buckets == bucket_pointers.num_buckets;
      @ requires \invariant_for(buffers) && \invariant_for(bucket_pointers) && \invariant_for(classifier);
      @
      @ requires \disjoint(values[*], bucket_starts[*], overflow[*], bucket_pointers.buffer[*], buffers.indices[*], buffers.buffer[*], classifier.footprint);
      @ requires overflow.length == Buffers.BUFFER_SIZE;
      @
      @ requires (\forall int b; 0 <= b < bucket_pointers.num_buckets;
      @     // All elements are read
      @     bucket_pointers.toReadCountOfBucket(b) == 0 &&
      @     // All written elements are classified as b
      @     classifier.isClassOfSeq(bucket_pointers.writtenElementsOfBucket(values, begin, b), b) &&
      @     (int) bucket_pointers.aligned_bucket_starts[b] == Buffers.blockAligned(bucket_starts[b]) &&
      @     // Remaining elements: bucket size == buffer length + written elements
      @     bucket_starts[b + 1] - bucket_starts[b] == buffers.bufferAt(b).length + bucket_pointers.writtenCountOfBucket(b) &&
      @     // Buffer length, just the remainder module BUFFER_SIZE that is never 0 for nonempty buckets
      @     buffers.bufferAt(b).length ==
      @         ((bucket_starts[b + 1] - bucket_starts[b] >= Buffers.BUFFER_SIZE && (bucket_starts[b + 1] - bucket_starts[b]) % Buffers.BUFFER_SIZE == 0) ?
      @             Buffers.BUFFER_SIZE : ((bucket_starts[b + 1] - bucket_starts[b]) % Buffers.BUFFER_SIZE))
      @ );
      @
      @ ensures (\forall int b; 0 <= b < bucket_pointers.num_buckets;
      @     classifier.isClassOfSeq(\dl_seq_def_workaround(begin + bucket_starts[b], begin + bucket_starts[b + 1], values), b) &&
      @     Sorter.smallBucketIsSorted(values, begin, end, bucket_starts[b], bucket_starts[b + 1])
      @ );
      @
      @ assignable values[begin..end - 1];
      @*/
    public static void cleanup(
            final int[] values,
            final int begin,
            final int end,
            final Buffers buffers,
            final int[] bucket_starts,
            final BucketPointers bucket_pointers,
            final Classifier classifier,
            final int[] overflow
    ) {
        final int num_buckets = classifier.num_buckets();
        final int overflow_bucket = find_overflow_bucket(bucket_starts, num_buckets);

        final boolean is_last_level = end - begin <= Constants.SINGLE_LEVEL_THRESHOLD;
        final int max_offset = Buffers.align_to_previous_block(end - begin);

        /*@ loop_invariant 0 <= bucket <= num_buckets;
          @ loop_invariant (\forall int b; bucket <= b < bucket_pointers.num_buckets;
          @     classifier.isClassOfSeq(bucket_pointers.writtenElementsOfBucket(values, begin, b), b)
          @     // the remaining conditions are never changed
          @ );
          @
          @ loop_invariant (\forall int b; 0 <= b < bucket;
          @     classifier.isClassOfSeq(\dl_seq_def_workaround(begin + bucket_starts[b], begin + bucket_starts[b + 1], values), b) &&
          @     Sorter.smallBucketIsSorted(values, begin, end, bucket_starts[b], bucket_starts[b + 1])
          @ );
          @ loop_invariant \invariant_for(classifier) && \invariant_for(bucket_pointers) && \invariant_for(buffers);
          @
          @ assignable values[begin..end - 1];
          @
          @ decreases num_buckets - bucket;
          @*/
        for (int bucket = 0; bucket < num_buckets; ++bucket) {
            final int relative_start = bucket_starts[bucket];
            final int relative_stop = bucket_starts[bucket + 1];
            final int relative_write = bucket_pointers.write(bucket);
            final int start = begin + relative_start;
            final int stop = begin + relative_stop;
            final int write = begin + relative_write;

            /*@ normal_behaviour
              @ ensures 0 <= bucket_starts[bucket] <= bucket_starts[bucket + 1] <= bucket_starts[num_buckets] &&
              @     (\forall int b; 0 <= b < num_buckets && b != bucket;
              @         (b < bucket ==> 0 <= bucket_starts[b] <= bucket_starts[b + 1] <= bucket_starts[bucket]) &&
              @         (b > bucket ==> bucket_starts[bucket + 1] <= bucket_starts[b] <= bucket_starts[b + 1] <= bucket_starts[num_buckets]));
              @ ensures Buffers.blockAligned(bucket_starts[bucket]) <= relative_write <= Buffers.blockAligned(bucket_starts[bucket + 1]);
              @
              @ assignable \strictly_nothing;
              @*/
            {;;}

            final int head_start = start;
            int head_stop;

            int tail_start;
            final int tail_stop = stop;

            /*@ normal_behaviour
              @ requires begin <= start <= stop <= end;
              @
              @ ensures \invariant_for(classifier) && \invariant_for(bucket_pointers) && \invariant_for(buffers);
              @
              @ ensures start <= head_start <= head_stop <= tail_start <= tail_stop <= stop <= end <= values.length;
              @ ensures tail_start - head_stop == bucket_pointers.writtenCountOfBucket(bucket);
              @ ensures classifier.isClassOfSeq(\dl_seq_def_workaround(head_stop, tail_start, values), bucket);
              @
              @ assignable values[start..stop - 1];
              @*/
            {
                // Overflow happened:
                // - block was written at least once
                // - write was out of bounds

                if (relative_stop - relative_start <= Buffers.BUFFER_SIZE) {
                    // Nothing written
                    // Valid: use precondition and split on the buffer length
                    //@ assert bucket_pointers.writtenCountOfBucket(bucket) == 0;

                    // Bucket is at most one block large => head is the full block, no tail
                    head_stop = stop;
                    tail_start = stop;
                    // verified
                } else {
                    final int aligned_relative_start = Buffers.align_to_next_block(relative_start);
                    head_stop = begin + aligned_relative_start;

                    // Valid: use precondition and observer dependency
                    //@ assert head_start <= head_stop <= tail_stop && aligned_relative_start == (int) bucket_pointers.aligned_bucket_starts[bucket];

                    if (stop < write) {
                        // Final block has been written
                        // Write pointer must be at aligned end of bucket

                        // Valid: use contract from nextWrite and blockAlign
                        //@ assert relative_write == Buffers.blockAligned(relative_stop);

                        if (end < write) {
                            // Overflow: write is out of bounds, content is in overflow
                            tail_start = write - Buffers.BUFFER_SIZE;

                            // Valid: Use contract of blockAligned
                            //@ assert head_start <= head_stop <= tail_start <= tail_stop;

                            int tail_len = tail_stop - tail_start;

                            // There must be space for all elements
                            // Valid: Precondition and observer
                            //@ assert Buffers.BUFFER_SIZE + buffers.bufferAt(bucket).length == (tail_stop - tail_start) + (head_stop - head_start);

                            // Fill tail
                            Functions.copy_nonoverlapping(overflow, 0, values, tail_start, tail_len);
                            tail_start = tail_stop;

                            // Write remaining elements to end of head
                            int head_elements = Buffers.BUFFER_SIZE - tail_len;
                            head_stop -= head_elements;
                            Functions.copy_nonoverlapping(overflow, tail_len, values, head_stop, head_elements);
                            // TODO classOfSeq
                            // rest verified
                        } else {
                            // Normal overflow: write is in bounds and content is after the end of the bucket
                            int overflow_len = write - stop;

                            //@ assert head_start <= head_stop <= stop <= stop + overflow_len <= end;

                            // Must fit, no other empty space left
                            // Follows from precondition and lots of observers
                            //@ assert overflow_len + buffers.bufferAt(bucket).length == head_stop - head_start;
                            // Follows from previous and buffer length >= 0
                            //@ assert head_start <= head_stop - overflow_len;

                            // Write overflow of last block to [head_stop - overflow_len..head_stop)
                            head_stop -= overflow_len;

                            Functions.copy_nonoverlapping(values, stop, values, head_stop, overflow_len);

                            // Tail is empty
                            tail_start = tail_stop;
                            // TODO classOfSeq
                            // rest verified (all the dependency contracts)
                        }
                    } else {
                        // No overflow, write <= stop
                        tail_start = write;

                        // Valid: Just use definition of writtenElementsOfBucket
                        //@ assert \dl_seq_def_workaround(head_stop, tail_start, values) == bucket_pointers.writtenElementsOfBucket(values, begin, bucket);
                        // verified: use equality, observer
                    }
                }

                //@ assert \invariant_for(classifier) && \invariant_for(bucket_pointers) && \invariant_for(buffers);
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

            /*@ normal_behaviour
              @ requires classifier.isClassOfSeq(\dl_seq_def_workaround(begin + bucket_starts[bucket], begin + bucket_starts[bucket + 1], values), bucket);
              @
              @ ensures classifier.isClassOfSeq(\dl_seq_def_workaround(begin + bucket_starts[bucket], begin + bucket_starts[bucket + 1], values), bucket);
              @ ensures Sorter.smallBucketIsSorted(values, begin, end, bucket_starts[bucket], bucket_starts[bucket + 1]);
              @
              @ assignable values[start..stop - 1];
              @*/
            {
                if (stop - start <= 2 * Constants.BASE_CASE_SIZE || is_last_level) {
                    Sorter.fallback_sort(values, start, stop);
                }
            }

            //@ assert \invariant_for(classifier) && \invariant_for(bucket_pointers) && \invariant_for(buffers);
        }
    }
}
