package de.wiesler;

public class Cleanup {
    /*@ public normal_behaviour
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets);
      @ 
      @ ensures (\forall int b; 0 <= b < num_buckets; b <= \result || bucket_starts[b + 1] - bucket_starts[b] <= Buffers.BUFFER_SIZE);
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
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets);
      @ requires bucket_starts[num_buckets] == end - begin;
      @ requires num_buckets == buffers.buckets && num_buckets == bucket_pointers.num_buckets;
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
            final int num_buckets,
            final int[] overflow
    ) {
        final int overflow_bucket = find_overflow_bucket(bucket_starts, num_buckets);

        final boolean is_last_level = end - begin <= Constants.SINGLE_LEVEL_THRESHOLD;
        final int max_offset = Buffers.align_to_previous_block(end - begin);

        /*@ loop_invariant 0 <= bucket && bucket <= num_buckets;
          @ // later values are unchanged
          @ loop_invariant (\forall int i; begin + bucket_starts[bucket] <= i < end; values[i] == \old(values[i]));
          @ 
          @ loop_invariant (\forall int b; 0 <= b < num_buckets; 
          @     bucket_pointers.write(bucket) <= bucket_starts[bucket + 1]
          @ );
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

            int head_start = begin + relative_start;
            int head_stop = begin + Functions.min(Buffers.align_to_next_block(relative_start), relative_stop);

            int tail_start;
            int tail_stop;

            /*@ normal_behaviour
              @ requires Functions.isValidSubSlice(values, begin, end, start, stop);
              @ 
              @ ensures Functions.isValidSubSlice(values, start, stop, head_start, head_stop);
              @ ensures Functions.isValidSubSlice(values, start, stop, tail_start, tail_stop);
              @ ensures head_stop - head_start + tail_stop - tail_start == buffers.bufferAt(bucket).length;
              @ 
              @ ensures bucket != overflow_bucket ==> (\forall int i; head_stop <= i < write; values[i] == \old(values)[i]);
              @ 
              @ assignable values[start..stop - 1];
              @*/
            {
                // Overflow happened:
                // - write to an offset >= max_offset was stopped
                // - bucket pointer write increment returns the old value => write - BUFFER_SIZE >= max_offset
                // - this block is in the overflow buffer
                if (overflow_bucket != -1 && bucket == overflow_bucket && relative_write >= Buffers.BUFFER_SIZE && relative_write - Buffers.BUFFER_SIZE >= max_offset) {
                    // Overflow

                    // Overflow buffer has been written => write pointer must be at end of bucket
                    // This gives stop <= write
                    //@ assert (Buffers.align_to_next_block(relative_stop) == relative_write);

                    tail_start = write - Buffers.BUFFER_SIZE;
                    tail_stop = stop;

                    int head_len = head_stop - head_start;

                    // There must be space for at least block size elements
                    //@ assert (Buffers.BUFFER_SIZE <= (tail_stop - tail_start) + head_len);

                    // Fill head: head.len() <= Buffers.BUFFER_SIZE
                    //@ assert (head_start + head_len <= head_stop);
                    Functions.copy(overflow, 0, values, head_start, head_len);
                    head_start = head_stop;

                    // Write remaining elements into tail
                    int tail_elements = Buffers.BUFFER_SIZE - head_len;
                    //@ assert (start <= tail_start && tail_start + tail_elements <= tail_stop);
                    Functions.copy(overflow, head_len, values, tail_start, tail_elements);
                    tail_start += tail_elements;
                } else if (stop < write) {
                    if (Buffers.BUFFER_SIZE < stop - start) {
                        // Final block has been written
                        //@ assert (Buffers.align_to_next_block(relative_stop) == relative_write);

                        int overflow_len = write - stop;

                        // Must fit, no other empty space left
                        //@ assert (overflow_len <= head_stop - head_start);

                        // Write overflow of last block to head
                        Functions.copy(values, stop, values, head_start, overflow_len);
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
                Sorter.base_case_sort(values, start, stop);
            }
        }
    }
}