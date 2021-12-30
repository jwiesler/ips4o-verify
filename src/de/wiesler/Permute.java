package de.wiesler;

public class Permute {
    private static int classify_and_read_block(
            int bucket,
            int[] values,
            int begin,
            int end,
            Classifier classifier,
            BucketPointers bucket_pointers,
            int[] buffer
    ) {
        int read = bucket_pointers.decrement_read(bucket);
        if (read < 0) {
            return -1;
        }

        Functions.copy_block_to_buffer(values, begin, end, begin + read, buffer);
        int first_value = buffer[0];
        return classifier.classify(first_value);
    }

    private static int swap_block(
            int target_bucket,
            int[] values,
            int begin,
            int end,
            Classifier classifier,
            int max_offset,
            BucketPointers bucket_pointers,
            int[] current_swap,
            int[] other_swap,
            int[] overflow
    ) {
        while (true) {
            BucketPointers.Increment increment = bucket_pointers.increment_write(target_bucket);
            boolean occupied = increment.occupied;
            int write = begin + increment.position;

            if (occupied) {
                int new_target = classifier.classify(values[write]);

                // Swap only if this block is not already in the right bucket
                if (new_target != target_bucket) {
                    // Copy to other swap
                    Functions.copy_block_to_buffer(values, begin, end, write, other_swap);
                    // Copy in current swap
                    Functions.copy_block_from_buffer(values, begin, end, current_swap, write);
                    return new_target;
                }
            } else {
                // Destination block is empty

                if (write >= max_offset) {
                    // Out-of-bounds; write to overflow buffer instead
                    Functions.copy_buffer_to(current_swap, overflow);
                } else {
                    // Write block
                    Functions.copy_block_from_buffer(values, begin, end, current_swap, write);
                }

                return -1;
            }
        }
    }

    // requires len > 0
    public static int max_offset(int len) {
        // First block offset *not* to write to:
        // - if the length is already block aligned, the max offset is the offset to the end
        //    |---|---|---|
        //                ^
        //                |
        //             max/len
        // - else we align the length to the next block
        //    |---|---|---|
        //            ^  ^
        //           /   |
        //         max  len

        int aligned_len = Buffers.align_to_next_block(len);
        int max_offset;
        if (len == aligned_len) {
            max_offset = aligned_len;
        } else {
            max_offset = aligned_len - Buffers.BUFFER_SIZE;
        }
        return max_offset;
    }

    /*@ public normal_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ // aliasing
      @ // bucket pointers readable content is block classified
      @ 
      @ // blocks from the readable content are distributed to the buckets
      @ // bucket pointers contain the per bucket remaining space
      @ // overflow contains the overflowing bucket iff an overflow happens
      @
      @ assignable values[begin..end - 1];
      @ assignable bucket_pointers.*;
      @ assignable swap_1[*], swap_2[*], overflow[*];
      @*/
    public static void permute(
            final int[] values,
            final int begin,
            final int end,
            final Classifier classifier,
            final BucketPointers bucket_pointers,
            final int[] swap_1,
            final int[] swap_2,
            final int[] overflow
    ) {
        final int max_offset = begin + max_offset(end - begin);
        final int num_buckets = classifier.num_buckets();

        for (int bucket = 0; bucket < num_buckets; ++bucket) {
            boolean first_is_current_swap = true;

            while (true) {
                int target_bucket = classify_and_read_block(
                        bucket,
                        values,
                        begin,
                        end,
                        classifier,
                        bucket_pointers,
                        first_is_current_swap ? swap_1 : swap_2
                );
                if (target_bucket < 0) {
                    break;
                }

                while (true) {
                    int new_target = swap_block(
                            target_bucket,
                            values,
                            begin,
                            end,
                            classifier,
                            max_offset,
                            bucket_pointers,
                            first_is_current_swap ? swap_1 : swap_2,
                            first_is_current_swap ? swap_2 : swap_1,
                            overflow
                    );
                    if (new_target < 0) {
                        break;
                    }
                    first_is_current_swap = !first_is_current_swap;
                    target_bucket = new_target;
                }
            }
        }
    }
}
