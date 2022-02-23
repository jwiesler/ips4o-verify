package de.wiesler;

public final class Permute {
    // Places the block in current_swap into target_bucket
    // Might skip blocks in current_swap if they are occupied and already in the right bucket
    //
    // If the target is occupied it is copied to other_swap and current_swap is placed in its position => result >= 0 && result == new_target
    // Else it is placed there or in the overflow buffer => result == -1
    //
    // Permutation between:
    // * the occupied area of each bucket
    // * the written area of each bucket
    // * current_swap
    // * overflow if written
    // and
    // * the new occupied area of each bucket
    // * the new written area of each bucket
    // * other_swap
    // * overflow if written now or before
    /*@ public normal_behaviour
      @ requires \invariant_for(bucket_pointers);
      @ requires \invariant_for(classifier);
      @ requires classifier.num_buckets == bucket_pointers.num_buckets;
      @ requires current_swap.length == Buffers.BUFFER_SIZE && other_swap.length == Buffers.BUFFER_SIZE && overflow.length == Buffers.BUFFER_SIZE;
      @
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires 0 <= target_bucket < classifier.num_buckets;
      @
      @ requires \disjoint(current_swap[*], other_swap[*], overflow[*]);
      @
      @ // The buffer is classified as target_bucket
      @ requires classifier.isClassOfSeq(\dl_seq_def_workaround(0, Buffers.BUFFER_SIZE, current_swap), target_bucket);
      @
      @ ensures (\forall int b; 0 <= b < classifier.num_buckets;
      @     (countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) ==
      @         (\old(countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier)) +
      @         b == target_bucket ? Buffers.BUFFER_SIZE : 0)) &&
      @     // All written elements are classified as b
      @     classifier.isClassOfSeq(bucket_pointers.writtenElementsOfBucket(values, begin, end), b)
      @ );
      @
      @ // only decreases elements to read
      @ ensures (\forall int b; 0 <= b < classifier.num_buckets; bucket_pointers.toReadCountOfBucket(b) <= \old(bucket_pointers.toReadCountOfBucket(b)));
      @
      @ ensures \invariant_for(bucket_pointers) && \invariant_for(classifier);
      @
      @ assignable values[begin..end - 1];
      @ assignable bucket_pointers.buffer[*];
      @ assignable other_swap[*], overflow[*];
      @*/
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
        /*@ loop_invariant true;
          @
          @ loop_invariant \invariant_for(bucket_pointers) && \invariant_for(classifier);
          @
          @ assignable values[begin..end - 1];
          @ assignable bucket_pointers.buffer[*];
          @ assignable other_swap[*], overflow[*];
          @*/
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

    /*@ public normal_behaviour
      @ requires \invariant_for(bucket_pointers);
      @ requires \invariant_for(classifier);
      @ requires classifier.num_buckets == bucket_pointers.num_buckets;
      @ requires swap_1.length == Buffers.BUFFER_SIZE && swap_2.length == Buffers.BUFFER_SIZE && overflow.length == Buffers.BUFFER_SIZE;
      @
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires 0 <= target_bucket < classifier.num_buckets;
      @
      @ // swap_1 is classified as target_bucket
      @ requires classifier.isClassOfSeq(\dl_seq_def_workaround(0, Buffers.BUFFER_SIZE, swap_1), target_bucket);
      @
      @ ensures (\forall int b; 0 <= b < classifier.num_buckets;
      @     (countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) ==
      @         (\old(countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier)) +
      @         (b == target_bucket ? Buffers.BUFFER_SIZE : 0))) &&
      @     classifier.isClassifiedBlocksRangeSeq(bucket_pointers.elementsToReadOfBucket(values, begin, b)) &&
      @     // All written elements are classified as b
      @     classifier.isClassOfSeq(bucket_pointers.writtenElementsOfBucket(values, begin, b), b)
      @ );
      @ // only decreases elements to read
      @ ensures (\forall int b; 0 <= b < classifier.num_buckets; bucket_pointers.toReadCountOfBucket(b) <= \old(bucket_pointers.toReadCountOfBucket(b)));
      @
      @ ensures \invariant_for(bucket_pointers) && \invariant_for(classifier);
      @
      @ assignable values[begin..end - 1];
      @ assignable bucket_pointers.buffer[*];
      @ assignable swap_1[*], swap_2[*], overflow[*];
      @*/
    private static void place_block(
            int target_bucket,
            final int[] values,
            final int begin,
            final int end,
            final Classifier classifier,
            final int max_offset,
            final BucketPointers bucket_pointers,
            final int[] swap_1,
            final int[] swap_2,
            final int[] overflow
    ) {
        boolean first_is_current_swap = true;

        /*@ loop_invariant (\forall int b; 0 <= b < classifier.num_buckets;
          @     (countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) ==
          @         (\old(countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier)) +
          @         b == target_bucket ? Buffers.BUFFER_SIZE : 0)) &&
          @     classifier.isClassifiedBlocksRangeSeq(bucket_pointers.elementsToReadOfBucket(values, begin, b)) &&
          @     // All written elements are classified as b
          @     classifier.isClassOfSeq(bucket_pointers.writtenElementsOfBucket(values, begin, b), b)
          @ );
          @ // The buffer is classified as target_bucket
          @ loop_invariant classifier.isClassOfSeq(\dl_seq_def_workaround(0, Buffers.BUFFER_SIZE, first_is_current_swap ? swap_1 : swap_2), target_bucket);
          @ // only decreases elements to read
          @ loop_invariant (\forall int b; 0 <= b < classifier.num_buckets; bucket_pointers.toReadCountOfBucket(b) <= \old(bucket_pointers.toReadCountOfBucket(b)));
          @ loop_invariant \invariant_for(bucket_pointers) && \invariant_for(classifier);
          @
          @ assignable values[begin..end - 1];
          @ assignable bucket_pointers.buffer[*];
          @ assignable swap_1[*], swap_2[*], overflow[*];
          @*/
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

    /*@ model_behaviour
      @ requires 0 <= bucket < bucket_pointers.num_buckets;
      @ requires bucket_pointers.num_buckets == classifier.num_buckets;
      @ static model int countBucketElementsInAllReadAreas(int[] values, int begin, int end, int bucket, BucketPointers bucket_pointers, Classifier classifier) {
      @     return (\sum int b; 0 <= b < classifier.num_buckets;
      @         classifier.countClassOfSeqEq(bucket_pointers.elementsToReadOfBucket(values, begin, bucket), bucket)
      @     );
      @ }
      @*/

    /*@ model_behaviour
      @ requires 0 <= bucket < bucket_pointers.num_buckets;
      @ requires bucket_pointers.num_buckets == classifier.num_buckets;
      @ static model int countBucketElementsEverywhere(int[] values, int begin, int end, int bucket, BucketPointers bucket_pointers, Classifier classifier) {
      @     return countBucketElementsInAllReadAreas(values, begin, end, bucket, bucket_pointers, classifier) + bucket_pointers.writtenCountOfBucket(bucket);
      @ }
      @*/

    /*@ model_behaviour
      @ requires 0 <= bucket < bucket_pointers.num_buckets;
      @ requires bucket_pointers.num_buckets == classifier.num_buckets;
      @ static model boolean readAreaBlockClassified(int[] values, int begin, int end, int bucket, BucketPointers bucket_pointers, Classifier classifier) {
      @     return classifier.isClassifiedBlocksRangeSeq(bucket_pointers.elementsToReadOfBucket(values, begin, bucket));
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires \invariant_for(bucket_pointers);
      @ requires \invariant_for(classifier);
      @ requires classifier.num_buckets == bucket_pointers.num_buckets;
      @ requires swap_1.length == Buffers.BUFFER_SIZE && swap_2.length == Buffers.BUFFER_SIZE && overflow.length == Buffers.BUFFER_SIZE;
      @ requires \disjoint(values[*], swap_1[*], swap_2[*], overflow[*], classifier.footprint, bucket_pointers.buffer[*]);
      @
      @ requires (int) bucket_pointers.aligned_bucket_starts[0] == 0 && (int) bucket_pointers.aligned_bucket_starts[classifier.num_buckets] == Buffers.blockAligned(end - begin);
      @
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires (\forall int b; 0 <= b < classifier.num_buckets;
      @     countBucketElementsInAllReadAreas(values, begin, end, b, bucket_pointers, classifier) <= bucket_pointers.remainingWriteCountOfBucket(b) &&
      @     classifier.isClassifiedBlocksRangeSeq(bucket_pointers.elementsToReadOfBucket(values, begin, b)) &&
      @     bucket_pointers.writtenCountOfBucket(b) == 0
      @ );
      @
      @ ensures (\forall int b; 0 <= b < classifier.num_buckets;
      @     // Blocks are maintained
      @          countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) ==
      @     \old(countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier)) &&
      @     // All elements are read
      @     bucket_pointers.toReadCountOfBucket(b) == 0 &&
      @     // All written elements are classified as b
      @     classifier.isClassOfSeq(bucket_pointers.writtenElementsOfBucket(values, begin, b), b)
      @ );
      @
      @ ensures \invariant_for(bucket_pointers) && \invariant_for(classifier);
      @
      @ assignable values[begin..end - 1];
      @ assignable bucket_pointers.buffer[*];
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
        final int max_offset = begin + Buffers.align_to_previous_block(end - begin);
        final int num_buckets = classifier.num_buckets();

        /*@ loop_invariant 0 <= bucket <= num_buckets;
          @ loop_invariant \invariant_for(bucket_pointers) && \invariant_for(classifier);
          @
          @ loop_invariant (\forall int b; 0 <= b < bucket; bucket_pointers.toReadCountOfBucket(b) == 0);
          @ loop_invariant (\forall int b; 0 <= b < classifier.num_buckets;
          @     // Remaining space maintained
          @     countBucketElementsInAllReadAreas(values, begin, end, b, bucket_pointers, classifier) <= bucket_pointers.remainingWriteCountOfBucket(b) &&
          @     // Blocks are maintained
          @          countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) ==
          @     \old(countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier)) &&
          @     classifier.isClassifiedBlocksRangeSeq(bucket_pointers.elementsToReadOfBucket(values, begin, b)) &&
          @     // All written elements are classified as b
          @     classifier.isClassOfSeq(bucket_pointers.writtenElementsOfBucket(values, begin, b), b)
          @ );
          @
          @ assignable values[begin..end - 1];
          @ assignable bucket_pointers.buffer[*];
          @ assignable swap_1[*], swap_2[*], overflow[*];
          @
          @ decreases (\sum int b; 0 <= b < classifier.num_buckets; bucket_pointers.toReadCountOfBucket(b));
          @*/
        for (int bucket = 0; bucket < num_buckets; ++bucket) {
            /*@ loop_invariant \invariant_for(bucket_pointers) && \invariant_for(classifier);
              @
              @ loop_invariant (\forall int b; 0 <= b < bucket; bucket_pointers.toReadCountOfBucket(b) == 0);
              @ loop_invariant (\forall int b; 0 <= b < classifier.num_buckets;
              @     countBucketElementsInAllReadAreas(values, begin, end, b, bucket_pointers, classifier) <= bucket_pointers.remainingWriteCountOfBucket(b) &&
              @     // Blocks are maintained
              @          countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) ==
              @     \old(countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier)) &&
              @     classifier.isClassifiedBlocksRangeSeq(bucket_pointers.elementsToReadOfBucket(values, begin, b)) &&
              @     // All written elements are classified as b
              @     classifier.isClassOfSeq(bucket_pointers.writtenElementsOfBucket(values, begin, b), b)
              @ );
              @
              @ assignable values[begin..end - 1];
              @ assignable bucket_pointers.buffer[*];
              @ assignable swap_1[*], swap_2[*], overflow[*];
              @
              @ decreases bucket_pointers.toReadCountOfBucket(bucket);
              @*/
            while (true) {
                //@ ghost final int old_last_read = bucket_pointers.toReadCountOfBucket(bucket);
                int read = bucket_pointers.decrement_read(bucket);
                //@ assert old_last_read == 0 <==> read < 0;
                if (read < 0) {
                    break;
                }

                //@ assert begin + read + Buffers.BUFFER_SIZE <= end;

                Functions.copy_block_to_buffer(values, begin, end, begin + read, swap_1);
                int first_value = swap_1[0];
                int target_bucket = classifier.classify(first_value);

                place_block(
                    target_bucket,
                    values,
                    begin,
                    end,
                    classifier,
                    max_offset,
                    bucket_pointers,
                    swap_1,
                    swap_2,
                    overflow
                );
            }
        }
    }
}
