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
      @ requires_free \invariant_free_for(bucket_pointers);
      @ requires \invariant_for(bucket_pointers);
      @ requires_free \invariant_free_for(classifier);
      @ requires \invariant_for(classifier);
      @ requires_free classifier.num_buckets == bucket_pointers.num_buckets;
      @ requires_free current_swap.length == Buffers.BUFFER_SIZE && other_swap.length == Buffers.BUFFER_SIZE && overflow.length == Buffers.BUFFER_SIZE;
      @
      @ requires_free 0 <= begin <= end <= values.length;
      @ requires_free end - begin <= Buffers.MAX_LEN;
      @ requires_free 0 <= target_bucket < classifier.num_buckets;
      @ requires_free (int) bucket_pointers.bucket_starts[classifier.num_buckets] == end - begin;
      @ requires_free bucket_pointers.first_empty_position <= end - begin;
      @
      @ requires_free \disjoint(values[*], current_swap[*], other_swap[*], overflow[*], bucket_pointers.buffer[*], classifier.sorted_splitters[*], classifier.tree.tree[*]);
      @
      @ // The buffer is classified as target_bucket
      @ requires_free classifier.isClassOfSlice(current_swap, 0, Buffers.BUFFER_SIZE, target_bucket);
      @
      @ requires_free (\forall int b; 0 <= b < classifier.num_buckets;
      @     // Enough space for bucket elements
      @     countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) +
      @         (b == target_bucket ? Buffers.BUFFER_SIZE : 0)
      @         <= bucket_pointers.bucketSize(b) &&
      @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
      @     // All written elements are classified as b
      @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b)
      @ );
      @
      @ ensures_free (\forall int b; 0 <= b < classifier.num_buckets;
      @     // Count of bucket elements is maintained
      @     countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) +
      @         (b == \result ? Buffers.BUFFER_SIZE : 0) ==
      @         (\old(countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier)) +
      @             (b == target_bucket ? Buffers.BUFFER_SIZE : 0)) &&
      @     // All written elements are classified as b
      @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b) &&
      @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
      @     // only decreases elements to read
      @     bucket_pointers.toReadCountOfBucket(b) <= \old(bucket_pointers.toReadCountOfBucket(b))
      @ );
      @
      @ ensures_free bucket_pointers.remainingWriteCountOfBucket(target_bucket) < \old(bucket_pointers.remainingWriteCountOfBucket(target_bucket));
      @
      @ ensures_free \result != -1 ==>
      @     classifier.isClassOfSlice(other_swap, 0, Buffers.BUFFER_SIZE, \result) &&
      @     0 <= \result < classifier.num_buckets;
      @
      @ ensures_free (\forall int element; true;
      @     bucket_pointers.countElement(values, begin, end, overflow, element) +
      @         (\result != -1 ? Functions.countElement(other_swap, 0, Buffers.BUFFER_SIZE, element) : 0) ==
      @         \old(bucket_pointers.countElement(values, begin, end, overflow, element)) +
      @         \old(Functions.countElement(current_swap, 0, Buffers.BUFFER_SIZE, element))
      @ );
      @
      @ ensures_free \invariant_free_for(bucket_pointers) && \invariant_free_for(classifier);
      @ ensures \invariant_for(bucket_pointers) && \invariant_for(classifier);
      @
      @ assignable_free values[begin..end - 1];
      @ assignable_free bucket_pointers.buffer[2 * target_bucket + 1];
      @ assignable_free other_swap[*], overflow[*];
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
        //@ assume bucket_pointers.bucketStart(classifier.num_buckets) == Buffers.blockAligned(end - begin) && bucket_pointers.disjointBucketsLemma(target_bucket);

        /*@ loop_invariant_free (\forall int b; 0 <= b < classifier.num_buckets;
          @     countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) ==
          @         \old(countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier))
          @ );
          @
          @ // current_swap isn't changed, we need to maintain only countElement
          @ loop_invariant_free (\forall int element; true;
          @     bucket_pointers.countElement(values, begin, end, overflow, element) ==
          @         \old(bucket_pointers.countElement(values, begin, end, overflow, element))
          @ );
          @
          @ loop_invariant_free bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, target_bucket);
          @ // All written elements are classified as b
          @ loop_invariant_free bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, target_bucket);
          @ loop_invariant_free bucket_pointers.toReadCountOfBucket(target_bucket) <= \old(bucket_pointers.toReadCountOfBucket(target_bucket));
          @ loop_invariant_free bucket_pointers.remainingWriteCountOfBucket(target_bucket) <= \old(bucket_pointers.remainingWriteCountOfBucket(target_bucket));
          @
          @ loop_invariant_free \invariant_for(bucket_pointers) && \invariant_for(classifier);
          @
          @ assignable_free bucket_pointers.buffer[2 * target_bucket + 1];
          @
          @ decreases bucket_pointers.remainingWriteCountOfBucket(target_bucket);
          @*/
        while (true) {
            //@ ghost \dl_Heap heapAtLoopBodyBegin = \dl_heap();

            //@ assume bucket_pointers.writtenCountOfBucket(target_bucket) + Buffers.BUFFER_SIZE <= bucket_pointers.bucketSize(target_bucket);
            Increment increment = bucket_pointers.increment_write(target_bucket);
            boolean occupied = increment.occupied;
            int write = begin + increment.position;

            /*@ assume
              @     Buffers.isBlockAligned(increment.position) &&
              @     begin <= write <= end &&
              @     bucket_pointers.lastReadOf(target_bucket) == \at(bucket_pointers.lastReadOf(target_bucket), heapAtLoopBodyBegin);
              @*/

            /*@ assume
              @     \old(bucket_pointers.disjointBucketsAreaLemma(values, begin, end, target_bucket, write, write + Buffers.BUFFER_SIZE)) &&
              @     \at(bucket_pointers.disjointBucketsAreaLemma(values, begin, end, target_bucket, write, write + Buffers.BUFFER_SIZE), heapAtLoopBodyBegin);
              @*/

            if (occupied) {
                // Follows from contract of lastReadOf and definition of toReadCount
                // other case is start == read which contradicts start <= write < read
                //@ assume \at(bucket_pointers.lastReadOf(target_bucket), heapAtLoopBodyBegin) - \at(bucket_pointers.nextWriteOf(target_bucket), heapAtLoopBodyBegin) >= Buffers.BUFFER_SIZE;
                /*@ assume \at(bucket_pointers.elementsToReadCountClassEqSplitBucket(
                  @         classifier,
                  @         values,
                  @         begin,
                  @         begin + bucket_pointers.nextWriteOf(target_bucket) + Buffers.BUFFER_SIZE,
                  @         end,
                  @         target_bucket,
                  @         true
                  @     ), heapAtLoopBodyBegin) &&
                  @     \at(bucket_pointers.elementsToReadCountElementSplitBucket(
                  @         values,
                  @         begin,
                  @         begin + bucket_pointers.nextWriteOf(target_bucket) + Buffers.BUFFER_SIZE,
                  @         end,
                  @         target_bucket,
                  @         true
                  @     ), heapAtLoopBodyBegin) &&
                  @     Buffers.isBlockAlignedSub(bucket_pointers.lastReadOf(target_bucket), \at(bucket_pointers.nextWriteOf(target_bucket), heapAtLoopBodyBegin));
                  @*/
                //@ assume write + Buffers.BUFFER_SIZE <= end && Buffers.isBlockAligned(bucket_pointers.lastReadOf(target_bucket) - \at(bucket_pointers.nextWriteOf(target_bucket), heapAtLoopBodyBegin));

                //@ assume \dl_inInt(values[write]);
                int new_target = classifier.classify(values[write]);
                //@ assume classifier.isClassifiedBlocksRange(values, write, begin + bucket_pointers.lastReadOf(target_bucket));
                //@ assume classifier.isClassifiedBlocksRangeSplit(values, write, write + Buffers.BUFFER_SIZE, begin + bucket_pointers.lastReadOf(target_bucket));
                //@ assume classifier.classOfClassifiedBlockFromFirst(values, write, write + Buffers.BUFFER_SIZE, new_target);
                //@ assume classifier.classOfClassifiedBlockFromFirst(values, write, write + Buffers.BUFFER_SIZE, new_target);
                //@ assume \at(classifier.countClassOfSliceEqLemma(values, write, write + Buffers.BUFFER_SIZE, new_target), heapAtLoopBodyBegin);

                //@ assume bucket_pointers.toReadCountOfBucket(target_bucket) <= \old(bucket_pointers.toReadCountOfBucket(target_bucket));
                //@ assume bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, target_bucket);

                // Todo disjointness of the ranges
                // Write area is disjoint from all other read and write areas

                // Swap only if this block is not already in the right bucket
                if (new_target != target_bucket) {
                    //@ ghost \dl_Heap heapBeforeWrite = \dl_heap();

                    // Copy to other swap
                    Functions.copy_nonoverlapping(values, write, other_swap, 0, Buffers.BUFFER_SIZE);
                    //@ assume \invariant_for(classifier);
                    //@ assume classifier.isClassOfSliceCopy(values, write, other_swap, 0, Buffers.BUFFER_SIZE, new_target);

                    // Copy in current swap
                    Functions.copy_nonoverlapping(current_swap, 0, values, write, Buffers.BUFFER_SIZE);

                    /*@ assume
                      @     \invariant_for(classifier) &&
                      @     \invariant_for(bucket_pointers) &&
                      @     bucket_pointers.lastReadOf(target_bucket) == \at(bucket_pointers.lastReadOf(target_bucket), heapBeforeWrite) &&
                      @     bucket_pointers.nextWriteOf(target_bucket) == \at(bucket_pointers.nextWriteOf(target_bucket), heapBeforeWrite);
                      @*/

                    //@ assume classifier.isClassOfSliceCopy(current_swap, 0, values, write, Buffers.BUFFER_SIZE, target_bucket);

                    /*@ assume
                      @     classifier.isClassOfSliceSplit(
                      @         values,
                      @         begin + bucket_pointers.bucketStart(target_bucket),
                      @         write,
                      @         write + Buffers.BUFFER_SIZE,
                      @         target_bucket
                      @     ) &&
                      @     bucket_pointers.writtenElementsCountElementSplitBucket(values, begin, end, overflow, target_bucket);
                      @*/

                    /*@ assume (\forall int b; 0 <= b < classifier.num_buckets;
                      @     bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b) +
                      @         (b == new_target ? Buffers.BUFFER_SIZE : 0) ==
                      @         \at(bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b), heapAtLoopBodyBegin) &&
                      @     bucket_pointers.writtenCountOfBucket(b) ==
                      @         \at(bucket_pointers.writtenCountOfBucket(b), heapAtLoopBodyBegin) +
                      @         (b == target_bucket ? Buffers.BUFFER_SIZE : 0)
                      @ );
                      @*/

                    /*@ assume (\forall int element; true;
                      @     bucket_pointers.elementsToReadCountElement(values, begin, end, element) +
                      @         Functions.countElement(other_swap, 0, Buffers.BUFFER_SIZE, element) ==
                      @         \at(bucket_pointers.elementsToReadCountElement(values, begin, end, element), heapAtLoopBodyBegin) &&
                      @     bucket_pointers.writtenElementsCountElement(values, begin, end, overflow, element) ==
                      @         \at(bucket_pointers.writtenElementsCountElement(values, begin, end, overflow, element), heapAtLoopBodyBegin) +
                      @         \old(Functions.countElement(current_swap, 0, Buffers.BUFFER_SIZE, element))
                      @ );
                      @*/
                    return new_target;
                }

                /*@ assume
                  @     classifier.isClassOfSliceSplit(
                  @         values,
                  @         begin + bucket_pointers.bucketStart(target_bucket),
                  @         write,
                  @         write + Buffers.BUFFER_SIZE,
                  @         target_bucket
                  @     ) &&
                  @     bucket_pointers.writtenElementsCountElementSplitBucket(values, begin, end, overflow, target_bucket);
                  @*/

                /*@ assume (\forall int b; 0 <= b < classifier.num_buckets;
                  @     bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b) +
                  @         (b == target_bucket ? Buffers.BUFFER_SIZE : 0) ==
                  @         \at(bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b), heapAtLoopBodyBegin) &&
                  @     bucket_pointers.writtenCountOfBucket(b) == \at(bucket_pointers.writtenCountOfBucket(b), heapAtLoopBodyBegin) +
                  @         (b == target_bucket ? Buffers.BUFFER_SIZE : 0)
                  @ );
                  @*/

                /*@ assume (\forall int element; true;
                  @     bucket_pointers.elementsToReadCountElement(values, begin, end, element) +
                  @         Functions.countElement(values, write, write + Buffers.BUFFER_SIZE, element) ==
                  @         \at(bucket_pointers.elementsToReadCountElement(values, begin, end, element), heapAtLoopBodyBegin) &&
                  @     bucket_pointers.writtenElementsCountElement(values, begin, end, overflow, element) ==
                  @         \at(bucket_pointers.writtenElementsCountElement(values, begin, end, overflow, element), heapAtLoopBodyBegin) +
                  @         Functions.countElement(values, write, write + Buffers.BUFFER_SIZE, element)
                  @ );
                  @*/
                {}
            } else {
                // Destination block is empty
                // Read area is empty
                //@ ghost \dl_Heap heapBeforeWrite = \dl_heap();

                /*@ normal_behaviour
                  @ ensures_free (\forall int b; 0 <= b < classifier.num_buckets;
                  @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b)
                  @ );
                  @ ensures_free (\forall int element; true;
                  @     bucket_pointers.writtenElementsCountElement(values, begin, end, overflow, element) ==
                  @         \at(bucket_pointers.writtenElementsCountElement(values, begin, end, overflow, element), heapAtLoopBodyBegin) +
                  @         \old(Functions.countElement(current_swap, 0, Buffers.BUFFER_SIZE, element))
                  @ );
                  @ ensures_free \invariant_free_for(classifier) && \invariant_free_for(bucket_pointers);
                  @ ensures \invariant_for(classifier) && \invariant_for(bucket_pointers);
                  @ assignable_free values[write..write + (write + Buffers.BUFFER_SIZE <= end ? Buffers.BUFFER_SIZE - 1 : 0)], overflow[*];
                  @*/
                {
                    if (end < write + Buffers.BUFFER_SIZE) {
                        //@ assume write + Buffers.BUFFER_SIZE == begin + Buffers.blockAligned(end - begin);
                        // Out-of-bounds; write to overflow buffer instead
                        Functions.copy_nonoverlapping(current_swap, 0, overflow, 0, Buffers.BUFFER_SIZE);
                        //@ assume \invariant_for(classifier) && \invariant_for(bucket_pointers);
                        //@ assume bucket_pointers.nextWriteOf(target_bucket) == \at(bucket_pointers.nextWriteOf(target_bucket), heapBeforeWrite);
                        // writtenCount >= 256 follows from increment_write
                        //@ assume classifier.isClassOfSliceCopy(current_swap, 0, overflow, 0, Buffers.BUFFER_SIZE, target_bucket);
                        //@ assume bucket_pointers.overflowBucketUniqueLemma(begin, end, target_bucket);
                        // TODO show that this can't be happening for all other buckets (by disjointness)
                        {}
                    } else {
                        // Write block
                        Functions.copy_nonoverlapping(current_swap, 0, values, write, Buffers.BUFFER_SIZE);
                        //@ assume \invariant_for(classifier) && \invariant_for(bucket_pointers);
                        //@ assume bucket_pointers.nextWriteOf(target_bucket) == \at(bucket_pointers.nextWriteOf(target_bucket), heapBeforeWrite);
                        //@ assume classifier.isClassOfSliceCopy(current_swap, 0, values, write, Buffers.BUFFER_SIZE, target_bucket);
                        /*@ assume classifier.isClassOfSliceSplit(
                          @     values,
                          @     begin + bucket_pointers.bucketStart(target_bucket),
                          @     write,
                          @     write + Buffers.BUFFER_SIZE,
                          @     target_bucket
                          @ );
                          @*/
                    }

                    //@ assume bucket_pointers.writtenElementsCountElementSplitBucket(values, begin, end, overflow, target_bucket);
                }
                /*@ assume
                  @     bucket_pointers.lastReadOf(target_bucket) == \at(bucket_pointers.lastReadOf(target_bucket), heapBeforeWrite) &&
                  @     bucket_pointers.nextWriteOf(target_bucket) == \at(bucket_pointers.nextWriteOf(target_bucket), heapBeforeWrite);
                  @*/

                /*@ assume (\forall int b; 0 <= b < classifier.num_buckets;
                  @     bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b) ==
                  @         \at(bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b), heapAtLoopBodyBegin) &&
                  @     bucket_pointers.writtenCountOfBucket(b) == \at(bucket_pointers.writtenCountOfBucket(b), heapAtLoopBodyBegin) +
                  @         (b == target_bucket ? Buffers.BUFFER_SIZE : 0)
                  @ );
                  @*/

                /*@ assume (\forall int element; true;
                  @     bucket_pointers.elementsToReadCountElement(values, begin, end, element) ==
                  @         \at(bucket_pointers.elementsToReadCountElement(values, begin, end, element), heapAtLoopBodyBegin)
                  @ );
                  @*/

                return -1;
            }
        }
    }

    /*@ public normal_behaviour
      @ requires_free \invariant_free_for(bucket_pointers);
      @ requires \invariant_for(bucket_pointers);
      @ requires_free \invariant_free_for(classifier);
      @ requires \invariant_for(classifier);
      @ requires_free classifier.num_buckets == bucket_pointers.num_buckets;
      @ requires_free swap_1.length == Buffers.BUFFER_SIZE && swap_2.length == Buffers.BUFFER_SIZE && overflow.length == Buffers.BUFFER_SIZE;
      @ requires_free \disjoint(values[*], swap_1[*], swap_2[*], overflow[*], bucket_pointers.buffer[*], classifier.sorted_splitters[*], classifier.tree.tree[*]);
      @
      @ requires_free 0 <= begin <= end <= values.length;
      @ requires_free end - begin <= Buffers.MAX_LEN;
      @ requires_free 0 <= target_bucket < classifier.num_buckets;
      @ requires_free (int) bucket_pointers.bucket_starts[classifier.num_buckets] == end - begin;
      @ requires_free bucket_pointers.first_empty_position <= end - begin;
      @
      @ // swap_1 is classified as target_bucket
      @ requires_free classifier.isClassOfSlice(swap_1, 0, Buffers.BUFFER_SIZE, target_bucket);
      @ requires_free (\forall int b; 0 <= b < classifier.num_buckets;
      @     countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) +
      @         (b == target_bucket ? Buffers.BUFFER_SIZE : 0)
      @         <= bucket_pointers.bucketSize(b) &&
      @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
      @     // All written elements are classified as b
      @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b)
      @ );
      @
      @ ensures_free (\forall int b; 0 <= b < classifier.num_buckets;
      @     (countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) ==
      @         (\old(countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier)) +
      @         (b == target_bucket ? Buffers.BUFFER_SIZE : 0))) &&
      @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
      @     // All written elements are classified as b
      @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b)
      @ );
      @ // only decreases elements to read
      @ ensures_free (\forall int b; 0 <= b < classifier.num_buckets; bucket_pointers.toReadCountOfBucket(b) <= \old(bucket_pointers.toReadCountOfBucket(b)));
      @
      @ ensures_free (\forall int element; true;
      @     bucket_pointers.countElement(values, begin, end, overflow, element) ==
      @         \old(
      @             bucket_pointers.countElement(values, begin, end, overflow, element) +
      @             Functions.countElement(swap_1, 0, Buffers.BUFFER_SIZE, element))
      @ );
      @
      @ ensures_free \invariant_free_for(bucket_pointers) && \invariant_free_for(classifier);
      @ ensures \invariant_for(bucket_pointers) && \invariant_for(classifier);
      @
      @ assignable_free values[begin..end - 1];
      @ assignable_free bucket_pointers.buffer[*];
      @ assignable_free swap_1[*], swap_2[*], overflow[*];
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
        //@ ghost int first_target_bucket = target_bucket;
        boolean first_is_current_swap = true;

        /*@ loop_invariant_free (\forall int b; 0 <= b < classifier.num_buckets;
          @     // The old countBucketElementsEverywhere is missing the BUFFER_SIZE elements of first_target_bucket that were in swap_1
          @     // The current countBucketElementsEverywhere is missing the BUFFER_SIZE elements of target_bucket that are in swap_1
          @     countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) +
          @         (b == target_bucket ? Buffers.BUFFER_SIZE : 0) ==
          @         (\old(countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier)) +
          @         (b == first_target_bucket ? Buffers.BUFFER_SIZE : 0)) &&
          @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
          @     // All written elements are classified as b
          @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b)
          @ );
          @ loop_invariant_free 0 <= target_bucket < classifier.num_buckets;
          @ // The buffer is classified as target_bucket
          @ loop_invariant_free classifier.isClassOfSlice(first_is_current_swap ? swap_1 : swap_2, 0, Buffers.BUFFER_SIZE, target_bucket);
          @ // only decreases elements to read
          @ loop_invariant_free (\forall int b; 0 <= b < classifier.num_buckets; bucket_pointers.toReadCountOfBucket(b) <= \old(bucket_pointers.toReadCountOfBucket(b)));
          @ loop_invariant_free \invariant_for(bucket_pointers) && \invariant_for(classifier);
          @
          @ loop_invariant_free (\forall int element; true;
          @     bucket_pointers.countElement(values, begin, end, overflow, element) +
          @         Functions.countElement(first_is_current_swap ? swap_1 : swap_2, 0, Buffers.BUFFER_SIZE, element) ==
          @         \old(bucket_pointers.countElement(values, begin, end, overflow, element)) +
          @         \old(Functions.countElement(swap_1, 0, Buffers.BUFFER_SIZE, element))
          @ );
          @
          @ assignable_free values[begin..end - 1];
          @ assignable_free bucket_pointers.buffer[*];
          @ assignable_free swap_1[*], swap_2[*], overflow[*];
          @
          @ decreases (\sum int b; 0 <= b < classifier.num_buckets; bucket_pointers.remainingWriteCountOfBucket(b));
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
            if (new_target == -1) {
                break;
            }
            first_is_current_swap = !first_is_current_swap;
            target_bucket = new_target;
        }
    }

    /*@ model_behaviour
      @ requires_free 0 <= bucket < bucket_pointers.num_buckets;
      @ requires_free bucket_pointers.num_buckets == classifier.num_buckets;
      @ static model int countBucketElementsEverywhere(int[] values, int begin, int end, int bucket, BucketPointers bucket_pointers, Classifier classifier) {
      @     return bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, bucket) + bucket_pointers.writtenCountOfBucket(bucket);
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires_free \invariant_free_for(bucket_pointers);
      @ requires \invariant_for(bucket_pointers);
      @ requires_free \invariant_free_for(classifier);
      @ requires \invariant_for(classifier);
      @ requires_free classifier.num_buckets == bucket_pointers.num_buckets;
      @ requires_free swap_1.length == Buffers.BUFFER_SIZE && swap_2.length == Buffers.BUFFER_SIZE && overflow.length == Buffers.BUFFER_SIZE;
      @ requires_free \disjoint(values[*], swap_1[*], swap_2[*], overflow[*], classifier.sorted_splitters[*], classifier.tree.tree[*], bucket_pointers.buffer[*]);
      @
      @ // requires (int) bucket_pointers.aligned_bucket_starts[0] == 0 && (int) bucket_pointers.aligned_bucket_starts[classifier.num_buckets] == Buffers.blockAligned(end - begin);
      @
      @ requires_free 0 <= begin <= end <= values.length;
      @ requires_free end - begin <= Buffers.MAX_LEN;
      @ requires_free (int) bucket_pointers.bucket_starts[classifier.num_buckets] == end - begin;
      @ requires_free bucket_pointers.first_empty_position <= end - begin;
      @ requires_free (\forall int b; 0 <= b < classifier.num_buckets;
      @     bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b) <= bucket_pointers.bucketSize(b) &&
      @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
      @     bucket_pointers.writtenCountOfBucket(b) == 0
      @ );
      @
      @ ensures_free (\forall int b; 0 <= b < classifier.num_buckets;
      @     // Blocks are maintained
      @          bucket_pointers.writtenCountOfBucket(b) ==
      @     \old(bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b)) &&
      @     // All elements are read
      @     bucket_pointers.toReadCountOfBucket(b) == 0 &&
      @     // All written elements are classified as b
      @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b)
      @ );
      @
      @ ensures_free (\forall int element; true;
      @     bucket_pointers.writtenElementsCountElement(values, begin, end, overflow, element) ==
      @         \old(bucket_pointers.elementsToReadCountElement(values, begin, end, element))
      @ );
      @
      @ ensures_free \invariant_free_for(bucket_pointers) && \invariant_free_for(classifier);
      @ ensures \invariant_for(bucket_pointers) && \invariant_for(classifier);
      @
      @ assignable_free values[begin..end - 1];
      @ assignable_free bucket_pointers.buffer[*];
      @ assignable_free swap_1[*], swap_2[*], overflow[*];
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
        //@ assume bucket_pointers.bucketStart(classifier.num_buckets) == Buffers.blockAligned(end - begin);
        final int num_buckets = classifier.num_buckets();

        /*@ loop_invariant_free 0 <= bucket <= num_buckets;
          @ loop_invariant_free \invariant_for(bucket_pointers) && \invariant_for(classifier);
          @
          @ loop_invariant_free (\forall int b; 0 <= b < bucket; bucket_pointers.toReadCountOfBucket(b) == 0);
          @ loop_invariant_free (\forall int b; 0 <= b < classifier.num_buckets;
          @     // Blocks are maintained
          @          countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) ==
          @     \old(bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b)) &&
          @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
          @     // All written elements are classified as b
          @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b)
          @ );
          @ loop_invariant_free (\forall int element; true;
          @     bucket_pointers.countElement(values, begin, end, overflow, element) ==
          @         \old(bucket_pointers.elementsToReadCountElement(values, begin, end, element))
          @ );
          @
          @ assignable_free values[begin..end - 1];
          @ assignable_free bucket_pointers.buffer[*];
          @ assignable_free swap_1[*], swap_2[*], overflow[*];
          @
          @ decreases num_buckets - bucket;
          @*/
        for (int bucket = 0; bucket < num_buckets; ++bucket) {
            /*@ loop_invariant_free \invariant_for(bucket_pointers) && \invariant_for(classifier);
              @
              @ loop_invariant_free (\forall int b; 0 <= b < bucket; bucket_pointers.toReadCountOfBucket(b) == 0);
              @ loop_invariant_free (\forall int b; 0 <= b < classifier.num_buckets;
              @     // Blocks are maintained
              @          countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) ==
              @     \old(bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b)) &&
              @     bucket_pointers.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b) &&
              @     // All written elements are classified as b
              @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b)
              @ );
              @ loop_invariant_free (\forall int element; true;
              @     bucket_pointers.countElement(values, begin, end, overflow, element) ==
              @         \old(bucket_pointers.elementsToReadCountElement(values, begin, end, element))
              @ );
              @
              @ assignable_free values[begin..end - 1];
              @ assignable_free bucket_pointers.buffer[*];
              @ assignable_free swap_1[*], swap_2[*], overflow[*];
              @
              @ decreases bucket_pointers.toReadCountOfBucket(bucket);
              @*/
            while (bucket_pointers.hasRemainingRead(bucket)) {
                //@ ghost \dl_Heap heapAtLoopBegin = \dl_heap();

                /*@ assume
                  @     bucket_pointers.elementsToReadCountClassEqSplitBucket(classifier, values, begin, begin + bucket_pointers.lastReadOf(bucket) - Buffers.BUFFER_SIZE, end, bucket, false) &&
                  @     bucket_pointers.elementsToReadCountElementSplitBucket(values, begin, begin + bucket_pointers.lastReadOf(bucket) - Buffers.BUFFER_SIZE, end, bucket, false);
                  @*/
                int read = bucket_pointers.decrement_read(bucket);

                //@ assume begin + read + Buffers.BUFFER_SIZE <= end;

                Functions.copy_nonoverlapping(values, begin + read, swap_1, 0, Buffers.BUFFER_SIZE);
                //@ assume \invariant_for(classifier) && \invariant_for(bucket_pointers);
                /*@ assume bucket_pointers.lastReadOf(bucket) == read &&
                  @     bucket_pointers.nextWriteOf(bucket) == \at(bucket_pointers.nextWriteOf(bucket), heapAtLoopBegin);
                  @*/
                /*@ assume bucket_pointers.nextWriteOf(bucket) <= read &&
                  @     bucket_pointers.toReadCountOfBucket(bucket) < \at(bucket_pointers.toReadCountOfBucket(bucket), heapAtLoopBegin);
                  @*/
                //@ assume Buffers.isBlockAlignedSub(read, bucket_pointers.nextWriteOf(bucket));
                //@ assume Buffers.isBlockAligned(read - bucket_pointers.nextWriteOf(bucket));
                //@ assume Buffers.isBlockAlignedAdd(read - bucket_pointers.nextWriteOf(bucket), Buffers.BUFFER_SIZE);
                //@ assume Buffers.isBlockAligned(read + Buffers.BUFFER_SIZE - bucket_pointers.nextWriteOf(bucket));

                //@ assume classifier.isClassifiedBlocksRange(values, begin + bucket_pointers.nextWriteOf(bucket), begin + read + Buffers.BUFFER_SIZE);
                //@ assume classifier.isClassifiedBlocksRangeSplit(values, begin + bucket_pointers.nextWriteOf(bucket), begin + read, begin + read + Buffers.BUFFER_SIZE);
                //@ assume classifier.isClassifiedBlock(values, begin + read, begin + read + Buffers.BUFFER_SIZE);
                int first_value = swap_1[0];
                //@ assume \dl_inInt(first_value);
                int target_bucket = classifier.classify(first_value);
                //@ assume classifier.classOfClassifiedBlockFromFirst(values, begin + read, begin + read + Buffers.BUFFER_SIZE, target_bucket);
                /*@ assume
                  @     classifier.isClassOfSlice(values, begin + read, begin + read + Buffers.BUFFER_SIZE, target_bucket) &&
                  @     classifier.isClassOfSliceCopy(values, begin + read, swap_1, 0, Buffers.BUFFER_SIZE, target_bucket);
                  @*/
                //@ assume classifier.countClassOfSliceEqLemma(values, begin + read, begin + read + Buffers.BUFFER_SIZE, target_bucket);

                /*@ assume (\forall int b; 0 <= b < classifier.num_buckets;
                  @     bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b) + (b == target_bucket ? Buffers.BUFFER_SIZE : 0) ==
                  @         \at(bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b), heapAtLoopBegin) &&
                  @     bucket_pointers.writtenCountOfBucket(b) == \at(bucket_pointers.writtenCountOfBucket(b), heapAtLoopBegin)
                  @ );
                  @*/

                /*@ assume (\forall int b; 0 <= b < classifier.num_buckets;
                  @     countBucketElementsEverywhere(values, begin, end, b, bucket_pointers, classifier) + (b == target_bucket ? Buffers.BUFFER_SIZE : 0) ==
                  @         \old(bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b))
                  @ );
                  @*/

                /*@ assume (\forall int element; true;
                  @     bucket_pointers.elementsToReadCountElement(values, begin, end, element) +
                  @         Functions.countElement(swap_1, 0, Buffers.BUFFER_SIZE, element) ==
                  @         \at(bucket_pointers.elementsToReadCountElement(values, begin, end, element), heapAtLoopBegin) &&
                  @     bucket_pointers.writtenElementsCountElement(values, begin, end, overflow, element) ==
                  @         \at(bucket_pointers.writtenElementsCountElement(values, begin, end, overflow, element), heapAtLoopBegin)
                  @ );
                  @*/
                /*@ assume (\forall int element; true;
                  @     bucket_pointers.countElement(values, begin, end, overflow, element) +
                  @         Functions.countElement(swap_1, 0, Buffers.BUFFER_SIZE, element) ==
                  @         \old(bucket_pointers.elementsToReadCountElement(values, begin, end, element))
                  @ );
                  @*/

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
