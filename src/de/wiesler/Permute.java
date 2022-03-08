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
      @ requires 0 <= begin <= end <= values.length;
      @ requires 0 <= target_bucket < classifier.num_buckets;
      @ requires (int) bucket_pointers.bucket_starts[classifier.num_buckets] == end - begin;
      @
      @ requires \disjoint(values[*], current_swap[*], other_swap[*], overflow[*], bucket_pointers.buffer[*], classifier.sorted_splitters[*], classifier.tree.tree[*]);
      @
      @ // The buffer is classified as target_bucket
      @ requires classifier.isClassOfSlice(current_swap, 0, Buffers.BUFFER_SIZE, target_bucket);
      @
      @ requires (\forall int b; 0 <= b < classifier.num_buckets;
      @     bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b) +
      @         (b == target_bucket ? Buffers.BUFFER_SIZE : 0)
      @         <= bucket_pointers.remainingWriteCountOfBucket(b) &&
      @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
      @     // All written elements are classified as b
      @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b)
      @ );
      @
      @ ensures (\forall int b; 0 <= b < classifier.num_buckets;
      @     countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) ==
      @         (\old(countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier)) +
      @             (b == target_bucket ? Buffers.BUFFER_SIZE : 0) -
      @             (b == \result ? Buffers.BUFFER_SIZE : 0)
      @         ) &&
      @     // All written elements are classified as b
      @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b) &&
      @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
      @     // only decreases elements to read
      @     bucket_pointers.toReadCountOfBucket(b) <= \old(bucket_pointers.toReadCountOfBucket(b))
      @ );
      @
      @ ensures \result != -1 ==> classifier.isClassOfSlice(other_swap, 0, Buffers.BUFFER_SIZE, \result);
      @
      @ ensures \invariant_for(bucket_pointers) && \invariant_for(classifier);
      @
      @ assignable values[begin..end - 1];
      @ assignable bucket_pointers.buffer[2 * target_bucket + 1];
      @ assignable other_swap[*], overflow[*];
      @*/
    private static int swap_block(
            int target_bucket,
            int[] values,
            int begin,
            int end,
            Classifier classifier,
            BucketPointers bucket_pointers,
            int[] current_swap,
            int[] other_swap,
            int[] overflow
    ) {
        // Todo: invariant for all buckets needed?
        /*@ loop_invariant (\forall int b; 0 <= b < classifier.num_buckets;
          @     bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b) +
          @         (b == target_bucket ? Buffers.BUFFER_SIZE : 0)
          @         <= bucket_pointers.remainingWriteCountOfBucket(b) &&
          @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
          @     // All written elements are classified as b
          @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b) &&
          @     bucket_pointers.toReadCountOfBucket(b) <= \old(bucket_pointers.toReadCountOfBucket(b))
          @ );
          @
          @ loop_invariant \invariant_for(bucket_pointers) && \invariant_for(classifier);
          @
          @ assignable bucket_pointers.buffer[2 * target_bucket + 1];
          @
          @ decreases bucket_pointers.toReadCountOfBucket(target_bucket);
          @*/
        while (true) {
            BucketPointers.Increment increment = bucket_pointers.increment_write(target_bucket);
            boolean occupied = increment.occupied;
            int write = begin + increment.position;

            //@ assert Buffers.isBlockAligned(increment.position) && begin <= write;

            if (occupied) {
                // Follows from contract of lastReadOf and definition of toReadCount
                //@ assert write + Buffers.BUFFER_SIZE <= end;
                int new_target = classifier.classify(values[write]);
                //@ assert classifier.isClassifiedBlocksRange(values, write, begin + bucket_pointers.lastReadOf(target_bucket));
                //@ assert classifier.isClassOfSlice(values, write, write + Buffers.BUFFER_SIZE, new_target);
                //@ assert classifier.isClassifiedBlocksRange(values, write + Buffers.BUFFER_SIZE, begin + bucket_pointers.lastReadOf(target_bucket));
                /*@ assert (\forall int b; 0 <= b < classifier.num_buckets;
                  @     bucket_pointers.toReadCountOfBucket(b) <= \old(bucket_pointers.toReadCountOfBucket(b)) &&
                  @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b)
                  @ );
                  @*/

                // Todo disjointness of the ranges
                // Write area is disjoint from all other read and write areas

                // Swap only if this block is not already in the right bucket
                if (new_target != target_bucket) {
                    // Copy to other swap
                    Functions.copy_nonoverlapping(values, write, other_swap, 0, Buffers.BUFFER_SIZE);
                    //@ assert classifier.isClassOfSliceCopy(values, write, other_swap, 0, Buffers.BUFFER_SIZE, new_target);

                    // Copy in current swap
                    Functions.copy_nonoverlapping(current_swap, 0, values, write, Buffers.BUFFER_SIZE);
                    //@ assert \invariant_for(classifier);

                    //@ assert classifier.isClassOfSliceCopy(current_swap, 0, values, write, Buffers.BUFFER_SIZE, target_bucket);

                    /*@ assert classifier.isClassOfSliceSplit(
                      @     values,
                      @     begin + bucket_pointers.bucketStart(target_bucket),
                      @     write,
                      @     write + Buffers.BUFFER_SIZE,
                      @     target_bucket
                      @ );
                      @*/
                    return new_target;
                }

                /*@ assert classifier.isClassOfSliceSplit(
                  @     values,
                  @     begin + bucket_pointers.bucketStart(target_bucket),
                  @     write,
                  @     write + Buffers.BUFFER_SIZE,
                  @     target_bucket
                  @ );
                  @*/
                {}
            } else {
                // Destination block is empty
                // elementsToReadOfBucketBlockClassified is true

                if (end < write + Buffers.BUFFER_SIZE) {
                    // Out-of-bounds; write to overflow buffer instead
                    Functions.copy_nonoverlapping(current_swap, 0, overflow, 0, Buffers.BUFFER_SIZE);
                    //@ assert classifier.isClassOfSliceCopy(current_swap, 0, overflow, 0, Buffers.BUFFER_SIZE, target_bucket);
                    // TODO show that this can't be happening for all other buckets (by disjointness)
                    {}
                } else {
                    // Write block
                    Functions.copy_nonoverlapping(current_swap, 0, values, write, Buffers.BUFFER_SIZE);
                    //@ assert classifier.isClassOfSliceCopy(current_swap, 0, values, write, Buffers.BUFFER_SIZE, target_bucket);
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
      @ requires classifier.isClassOfSlice(swap_1, 0, Buffers.BUFFER_SIZE, target_bucket);
      @ requires (\forall int b; 0 <= b < classifier.num_buckets;
      @     bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b) +
      @         (b == target_bucket ? Buffers.BUFFER_SIZE : 0)
      @         <= bucket_pointers.remainingWriteCountOfBucket(b) &&
      @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
      @     // All written elements are classified as b
      @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b)
      @ );
      @
      @ ensures (\forall int b; 0 <= b < classifier.num_buckets;
      @     (countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) ==
      @         (\old(countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier)) +
      @         (b == target_bucket ? Buffers.BUFFER_SIZE : 0))) &&
      @     bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b) <= bucket_pointers.remainingWriteCountOfBucket(b) &&
      @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
      @     // All written elements are classified as b
      @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b)
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
          @     bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b) +
          @         (b == target_bucket ? Buffers.BUFFER_SIZE : 0)
          @         <= bucket_pointers.remainingWriteCountOfBucket(b) &&
          @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
          @     // All written elements are classified as b
          @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b)
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
      @ static model int countBucketElementsEverywhere(int[] values, int begin, int end, int bucket, BucketPointers bucket_pointers, Classifier classifier) {
      @     return bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, bucket) + bucket_pointers.writtenCountOfBucket(bucket);
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
      @ // requires (int) bucket_pointers.aligned_bucket_starts[0] == 0 && (int) bucket_pointers.aligned_bucket_starts[classifier.num_buckets] == Buffers.blockAligned(end - begin);
      @
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires (\forall int b; 0 <= b < classifier.num_buckets;
      @     bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b) <= bucket_pointers.remainingWriteCountOfBucket(b) &&
      @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
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
      @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b)
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
        final int num_buckets = classifier.num_buckets();

        /*@ loop_invariant 0 <= bucket <= num_buckets;
          @ loop_invariant \invariant_for(bucket_pointers) && \invariant_for(classifier);
          @
          @ loop_invariant (\forall int b; 0 <= b < bucket; bucket_pointers.toReadCountOfBucket(b) == 0);
          @ loop_invariant (\forall int b; 0 <= b < classifier.num_buckets;
          @     // Remaining space maintained
          @     bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b) <= bucket_pointers.remainingWriteCountOfBucket(b) &&
          @     // Blocks are maintained
          @          countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) ==
          @     \old(countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier)) &&
          @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
          @     // All written elements are classified as b
          @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b)
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
              @     bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b) <= bucket_pointers.remainingWriteCountOfBucket(b) &&
              @     // Blocks are maintained
              @          countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) ==
              @     \old(countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier)) &&
              @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
              @     // All written elements are classified as b
              @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b)
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
                    bucket_pointers,
                    swap_1,
                    swap_2,
                    overflow
                );
            }
        }
    }
}
