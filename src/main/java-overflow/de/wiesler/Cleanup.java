package de.wiesler;

public final class Cleanup {
    /*@ public model_behaviour
      @ requires \invariant_for(classifier);
      @
      @ accessible values[begin + bucket_begin..begin + bucket_end - 1], classifier.sorted_splitters[*], classifier.tree.tree[*];
      @
      @ static model boolean cleanedUpSlice(int[] values, int begin, int end, int bucket_begin, int bucket_end, Classifier classifier, int bucket) {
      @     return classifier.isClassOfSlice(values, begin + bucket_begin, begin + bucket_end, bucket) &&
      @         Sorter.smallBucketIsSorted(values, begin, end, bucket_begin, bucket_end);
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires_free 0 <= begin <= end <= values.length;
      @ requires_free end - begin <= Buffers.MAX_LEN;
      @ requires_free Functions.isValidBucketStarts(bucket_starts, classifier.num_buckets);
      @ requires_free bucket_starts[classifier.num_buckets] == end - begin;
      @ requires_free classifier.num_buckets == buffers.num_buckets && classifier.num_buckets == bucket_pointers.num_buckets;
      @ requires_free \invariant_free_for(buffers) && \invariant_free_for(bucket_pointers) && \invariant_free_for(classifier);
      @ requires \invariant_for(buffers) && \invariant_for(bucket_pointers) && \invariant_for(classifier);
      @
      @ requires_free \disjoint(values[*], bucket_starts[*], overflow[*], bucket_pointers.buffer[*], buffers.indices[*], buffers.buffer[*], classifier.sorted_splitters[*], classifier.tree.tree[*]);
      @ requires_free overflow.length == Buffers.BUFFER_SIZE;
      @
      @ requires_free (\forall int b; 0 <= b <= classifier.num_buckets;
      @     bucket_pointers.bucketStart(b) == Buffers.blockAligned(bucket_starts[b])
      @ );
      @ requires_free (\forall int b; 0 <= b < classifier.num_buckets;
      @     classifier.isClassOfSlice(buffers.buffer, b * Buffers.BUFFER_SIZE, b * Buffers.BUFFER_SIZE + buffers.bufferLen(b), b) &&
      @     // All elements are read
      @     bucket_pointers.toReadCountOfBucket(b) == 0 &&
      @     // All written elements are classified as b
      @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b) &&
      @     // Remaining elements: bucket size == buffer length + written elements
      @     bucket_starts[b + 1] - bucket_starts[b] == buffers.bufferLen(b) + bucket_pointers.writtenCountOfBucket(b) &&
      @     buffers.bufferLen(b) == Buffers.bufferSizeForBucketLen(bucket_starts[b + 1] - bucket_starts[b])
      @ );
      @
      @ ensures_free (\forall int b; 0 <= b < classifier.num_buckets;
      @     classifier.isClassOfSlice(values, begin + bucket_starts[b], begin + bucket_starts[b + 1], b) &&
      @     Sorter.smallBucketIsSorted(values, begin, end, bucket_starts[b], bucket_starts[b + 1])
      @ );
      @
      @ // Permutation property
      @ ensures_free (\forall int element; true;
      @     \old(bucket_pointers.writtenElementsCountElement(values, begin, end, overflow, element)) +
      @         \old(buffers.countElement(element)) ==
      @         Functions.countElement(values, begin, end, element)
      @ );
      @
      @ assignable_free values[begin..end - 1];
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
        //@ ghost \dl_Heap heapOld = \dl_heap();
        final int num_buckets = classifier.num_buckets();
        final boolean is_last_level = end - begin <= Constants.SINGLE_LEVEL_THRESHOLD;

        /*@ loop_invariant_free 0 <= bucket <= num_buckets;
          @ loop_invariant_free (\forall int b; 0 <= b < bucket;
          @     cleanedUpSlice(values, begin, end, \old(bucket_starts[b]), \old(bucket_starts[b + 1]), classifier, b)
          @ );
          @
          @ loop_invariant_free (\forall int element; true;
          @         (\sum int b; 0 <= b < bucket; \old(bucket_pointers.writtenElementsOfBucketCountElement(values, begin, end, overflow, b, element))) +
          @             (\sum int b; 0 <= b < bucket; \old(buffers.countElementInBucket(b, element))) ==
          @             Functions.countElement(values, begin, begin + \old(bucket_starts[bucket]), element)
          @ );
          @
          @ loop_invariant_free (\forall int b; bucket <= b < classifier.num_buckets;
          @     bucket_pointers.writtenElementsOfBucketClassified(classifier, values, begin, end, overflow, b) &&
          @     (\forall int element; true;
          @         \old(bucket_pointers.writtenElementsOfBucketCountElement(values, begin, end, overflow, b, element)) ==
          @              bucket_pointers.writtenElementsOfBucketCountElement(values, begin, end, overflow, b, element) &&
          @         \old(buffers.countElementInBucket(b, element)) ==
          @              buffers.countElementInBucket(b, element))
          @ );
          @
          @ loop_invariant_free \invariant_for(classifier) && \invariant_for(bucket_pointers) && \invariant_for(buffers);
          @
          @ assignable_free values[begin..end - 1];
          @
          @ decreases num_buckets - bucket;
          @*/
        for (int bucket = 0; bucket < num_buckets; ++bucket) {
            //@ assert \old(Functions.bucketStartsOrdering(bucket_starts, num_buckets, bucket));
            final int relative_start = bucket_starts[bucket];
            final int relative_stop = bucket_starts[bucket + 1];
            final int relative_write = bucket_pointers.write(bucket);
            //@ assert \dl_inInt(begin + relative_start) && \dl_inInt(begin + relative_stop);
            final int start = begin + relative_start;
            final int stop = begin + relative_stop;
            final int write = begin + relative_write;

            /*@ assume 0 <= bucket_starts[bucket] <= bucket_starts[bucket + 1] <= bucket_starts[num_buckets] &&
              @     Buffers.blockAligned(bucket_starts[num_buckets]) == bucket_pointers.bucketStart(num_buckets);
              @*/

            //@ assert \dl_inInt(begin + bucket_pointers.bucketStart(bucket)) && \dl_inInt(begin + bucket_pointers.bucketStart(bucket + 1));

            /*@ normal_behaviour
              @ ensures_free classifier.isClassOfSlice(values, start, stop, bucket);
              @ ensures_free (\forall int element; true;
              @     \at(bucket_pointers.writtenElementsOfBucketCountElement(values, begin, end, overflow, bucket, element), heapOld) +
              @         \at(buffers.countElementInBucket(bucket, element), heapOld) ==
              @     Functions.countElement(values, start, stop, element)
              @ );
              @
              @ assignable_free values[start..stop - 1];
              @*/
            {
                /*@ assume relative_write == \old(bucket_pointers.nextWriteOf(bucket)) &&
                  @     Buffers.blockAligned(bucket_starts[bucket]) == bucket_pointers.bucketStart(bucket) &&
                  @     Buffers.blockAligned(bucket_starts[bucket + 1]) == bucket_pointers.bucketStart(bucket + 1);
                  @*/
                //@ assume Buffers.blockAligned(bucket_starts[bucket]) <= relative_write <= Buffers.blockAligned(bucket_starts[bucket + 1]);

                final int head_start = start;
                int head_stop = -1;

                int tail_start = -1;
                final int tail_stop = stop;

                /*@ normal_behaviour
                  @ requires_free begin <= start <= stop <= end;
                  @
                  @ ensures_free \invariant_free_for(classifier) && \invariant_free_for(bucket_pointers);
                  @ ensures \invariant_for(classifier) && \invariant_for(bucket_pointers);
                  @
                  @ ensures_free start <= head_start <= head_stop <= tail_start <= tail_stop <= stop <= end <= values.length;
                  @ ensures_free tail_start - head_stop == \at(bucket_pointers.writtenCountOfBucket(bucket), heapOld);
                  @ ensures_free classifier.isClassOfSlice(values, head_stop, tail_start, bucket);
                  @ ensures_free (\forall int element; true;
                  @     Functions.countElement(values, head_stop, tail_start, element) ==
                  @         \at(bucket_pointers.writtenElementsOfBucketCountElement(values, begin, end, overflow, bucket, element), heapOld)
                  @ );
                  @
                  @ assignable_free values[start..stop - 1];
                  @*/
                {
                    // Overflow happened:
                    // - block was written at least once
                    // - write was out of bounds

                    if (relative_stop - relative_start <= Buffers.BUFFER_SIZE) {
                        // Nothing written
                        // Valid: use precondition and split on the buffer length
                        //@ assume \old(bucket_pointers.writtenCountOfBucket(bucket)) == 0;
                        //@ assume (\forall int element; true; \old(bucket_pointers.writtenElementsOfBucketCountElement(values, begin, end, overflow, bucket, element)) == 0);

                        // Bucket is at most one block large => head is the full block, no tail
                        head_stop = stop;
                        tail_start = stop;
                        // verified
                    } else {
                        final int aligned_relative_start = Buffers.align_to_next_block(relative_start);
                        //@ assume aligned_relative_start == Buffers.blockAligned(relative_start);
                        //@ assume aligned_relative_start == bucket_pointers.bucketStart(bucket);
                        head_stop = begin + aligned_relative_start;

                        // Valid: use precondition and observer dependency
                        //@ assume head_start <= head_stop <= tail_stop;

                        if (stop < write) {
                            // Final block has been written
                            // Write pointer must be at aligned end of bucket

                            // Valid: use contract from nextWrite and blockAlign
                            //@ assume relative_write == Buffers.blockAligned(relative_stop);

                            if (end < write) {
                                // Overflow: write is out of bounds, content is in overflow

                                tail_start = write - Buffers.BUFFER_SIZE;

                                // Valid: Use contract of blockAligned
                                //@ assume head_start <= head_stop <= tail_start <= tail_stop;

                                int tail_len = tail_stop - tail_start;

                                // There must be space for all elements
                                // Valid: Precondition and observer
                                //@ assume Buffers.BUFFER_SIZE + buffers.bufferLen(bucket) == (tail_stop - tail_start) + (head_stop - head_start);

                                // Fill tail
                                Functions.copy_nonoverlapping(overflow, 0, values, tail_start, tail_len);

                                // Write remaining elements to end of head
                                int head_elements = Buffers.BUFFER_SIZE - tail_len;
                                head_stop -= head_elements;
                                Functions.copy_nonoverlapping(overflow, tail_len, values, head_stop, head_elements);

                                //@ assume \invariant_for(classifier) && \invariant_for(bucket_pointers);

                                /*@ assume
                                  @     classifier.isClassOfSlice(overflow, 0, Buffers.BUFFER_SIZE, bucket) &&
                                  @     // Follows from writtenElementsOfBucketClassified
                                  @     classifier.isClassOfSlice(values, head_stop + head_elements, tail_start, bucket) &&
                                  @     classifier.isClassOfSliceSplit(overflow, 0, tail_len, Buffers.BUFFER_SIZE, bucket) &&
                                  @     classifier.isClassOfSliceSplit(values, head_stop, head_stop + head_elements, tail_start, bucket) &&
                                  @     classifier.isClassOfSliceSplit(values, head_stop, tail_start, tail_stop, bucket);
                                  @*/
                                /*@ assume
                                  @     classifier.isClassOfSliceCopy(overflow, 0, values, tail_start, tail_len, bucket) &&
                                  @     classifier.isClassOfSliceCopy(overflow, tail_len, values, head_stop, head_elements, bucket);
                                  @*/

                                /*@ assume (\forall int element; true;
                                  @     \old(bucket_pointers.writtenElementsOfBucketCountElement(values, begin, end, overflow, bucket, element)) ==
                                  @         Functions.countElement(values, head_stop + head_elements, tail_start, element) +
                                  @         Functions.countElement(overflow, 0, Buffers.BUFFER_SIZE, element)
                                  @ );
                                  @*/

                                /*@ assume
                                  @     // Split overflow buffer
                                  @     Functions.countElementSplit(overflow, 0, tail_len, Buffers.BUFFER_SIZE) &&
                                  @     // Split off tail
                                  @     Functions.countElementSplit(values, head_stop, tail_start, tail_stop) &&
                                  @     // Split off head
                                  @     Functions.countElementSplit(values, head_stop, head_stop + head_elements, tail_start);
                                  @*/

                                tail_start = tail_stop;
                                // rest verified
                            } else {
                                // Normal overflow: write is in bounds and content is after the end of the bucket
                                int overflow_len = write - stop;

                                //@ assume head_start <= head_stop <= stop <= stop + overflow_len <= end;

                                // Must fit, no other empty space left
                                // Follows from precondition and lots of observers
                                //@ assume overflow_len + buffers.bufferLen(bucket) == head_stop - head_start;
                                // Follows from previous and buffer length >= 0
                                //@ assume head_start <= head_stop - overflow_len;

                                // Write overflow of last block to [head_stop - overflow_len..head_stop)
                                head_stop -= overflow_len;

                                Functions.copy_nonoverlapping(values, stop, values, head_stop, overflow_len);

                                //@ assume \invariant_for(classifier) && \invariant_for(bucket_pointers);

                                //@ assume classifier.isClassOfSlice(values, head_stop + overflow_len, write, bucket);
                                //@ assume classifier.isClassOfSliceSplit(values, head_stop + overflow_len, stop, write, bucket);
                                //@ assume classifier.isClassOfSliceCopy(values, stop, values, head_stop, overflow_len, bucket);
                                //@ assume classifier.isClassOfSliceSplit(values, head_stop, head_stop + overflow_len, stop, bucket);

                                /*@ assume (\forall int element; true;
                                  @     \old(bucket_pointers.writtenElementsOfBucketCountElement(values, begin, end, overflow, bucket, element)) ==
                                  @         Functions.countElement(values, begin + bucket_pointers.bucketStart(bucket), begin + \old(bucket_pointers.nextWriteOf(bucket)), element)
                                  @ );
                                  @*/
                                //@ assume Functions.countElementSplit(values, head_stop + overflow_len, stop, write);
                                //@ assume Functions.countElementSplit(values, head_stop, head_stop + overflow_len, stop);

                                // Tail is empty
                                tail_start = tail_stop;
                                // rest verified (all the dependency contracts)
                            }
                        } else {
                            // No overflow, write <= stop
                            tail_start = write;

                            // verified: use equality
                        }
                    }

                    //@ assume \invariant_for(classifier) && \invariant_for(bucket_pointers);
                }

                int head_len = head_stop - head_start;
                int tail_len = tail_stop - tail_start;
                //@ assume buffers.bufferLen(bucket) == head_len + tail_len;
                // Write remaining elements from buffer to head and tail
                buffers.distribute(
                        bucket,
                        values,
                        head_start,
                        head_len,
                        tail_start,
                        tail_len
                );
                /*@ assume Functions.countElementSplit(values, head_start, head_stop, tail_stop) &&
                  @     Functions.countElementSplit(values, head_stop, tail_start, tail_stop) &&
                  @     buffers.bufferLen(bucket) == head_len + tail_len &&
                  @     \invariant_for(classifier);
                  @*/
                //@ ghost int bucketOffset = bucket * Buffers.BUFFER_SIZE;
                /*@ assume
                  @     classifier.isClassOfSlice(buffers.buffer, bucketOffset, bucketOffset + buffers.bufferLen(bucket), bucket) &&
                  @     classifier.isClassOfSliceSplit(buffers.buffer, bucketOffset, bucketOffset + head_len, bucketOffset + buffers.bufferLen(bucket), bucket);
                  @*/
                /*@ assume
                  @     classifier.isClassOfSliceCopy(buffers.buffer, bucketOffset, values, head_start, head_len, bucket) &&
                  @     classifier.isClassOfSliceCopy(buffers.buffer, bucketOffset + head_len, values, tail_start, tail_len, bucket) &&
                  @     classifier.isClassOfSliceSplit(values, head_start, head_stop, tail_stop, bucket) &&
                  @     classifier.isClassOfSliceSplit(values, head_stop, tail_start, tail_stop, bucket);
                  @*/
            }

            /*@ normal_behaviour
              @ ensures_free cleanedUpSlice(values, begin, end, \at(bucket_starts[bucket], heapOld), \at(bucket_starts[bucket + 1], heapOld), classifier, bucket);
              @ ensures_free (\forall int element; true;
              @     \at(bucket_pointers.writtenElementsOfBucketCountElement(values, begin, end, overflow, bucket, element), heapOld) +
              @         \at(buffers.countElementInBucket(bucket, element), heapOld) ==
              @     Functions.countElement(values, start, stop, element)
              @ );
              @
              @ assignable_free values[start..stop - 1];
              @*/
            {}

            /*@ assume \invariant_for(classifier) && \invariant_for(bucket_pointers) && \invariant_for(buffers) &&
              @     Functions.countElementSplit(values, begin, begin + \old(bucket_starts[bucket]), begin + \old(bucket_starts[bucket + 1])) &&
              @     (\forall int b; 0 <= b < num_buckets && b != bucket;
              @         (b < bucket ==> 0 <= \old(bucket_starts[b]) <= \old(bucket_starts[b + 1]) <= \old(bucket_starts[bucket])) &&
              @         (b > bucket ==> \old(bucket_starts[bucket + 1]) <= \old(bucket_starts[b]) <= \old(bucket_starts[b + 1]) <= \old(bucket_starts[num_buckets]) &&
              @             \old(bucket_starts[b]) <= bucket_pointers.bucketStart(b)
              @     ));
              @*/
        }
    }
}
