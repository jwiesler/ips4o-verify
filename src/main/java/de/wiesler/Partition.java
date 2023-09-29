package de.wiesler;

public final class Partition {
    /*@ public model_behaviour
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets);
      @ requires 0 <= begin <= end <= values.length;
      @
      @ ensures \result;
      @ static model boolean bucketCountsToTotalCount(int[] values, int begin, int end, int[] bucket_starts, int num_buckets) {
      @     return (\forall int bucket; 0 <= bucket <= num_buckets;
      @         (\forall int element; true;
      @             (\sum int b; 0 <= b < bucket; Functions.countElement(values, begin + bucket_starts[b], begin + bucket_starts[b + 1], element)) ==
      @                 Functions.countElement(values, begin, begin + bucket_starts[bucket], element)
      @         )
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @ static model boolean allBucketsClassified(int[] values, int begin, int end, Classifier classifier, int[] bucket_starts) {
      @     return (\forall int b; 0 <= b < classifier.num_buckets;
      @         classifier.isClassOfSlice(values, begin + bucket_starts[b], begin + bucket_starts[b + 1], b)
      @     );
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires end - begin <= Buffers.MAX_LEN;
      @ requires bucket_starts.length == Constants.MAX_BUCKETS + 1;
      @ requires (\forall int b; 0 <= b < bucket_starts.length; bucket_starts[b] == 0);
      @ requires end - begin > Constants.ACTUAL_BASE_CASE_SIZE;
      @ requires \invariant_for(storage) && \invariant_for(classifier);
      @
      @ requires \disjoint(
      @     values[*],
      @     bucket_starts[*],
      @     classifier.tree.tree[*],
      @     classifier.sorted_splitters[*],
      @     storage.bucket_pointers[*],
      @     storage.buffers_buffer[*],
      @     storage.buffers_indices[*],
      @     storage.swap_1[*],
      @     storage.swap_2[*],
      @     storage.overflow[*]
      @ );
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @ ensures Functions.isValidBucketStarts(bucket_starts, classifier.num_buckets);
      @ ensures bucket_starts[classifier.num_buckets] == end - begin;
      @ ensures allBucketsClassified(values, begin, end, classifier, bucket_starts);
      @ ensures Sorter.smallBucketsInRangeSorted(values, begin, end, bucket_starts, classifier.num_buckets, 0, classifier.num_buckets);
      @ ensures \invariant_for(storage) && \invariant_for(classifier);
      @
      @ assignable values[begin..end - 1];
      @ assignable bucket_starts[*];
      @ assignable storage.bucket_pointers[*];
      @ assignable storage.buffers_buffer[*];
      @ assignable storage.buffers_indices[*];
      @ assignable storage.swap_1[*];
      @ assignable storage.swap_2[*];
      @ assignable storage.overflow[*];
      @*/
    public static void partition(
        int[] values,
        int begin,
        int end,
        int[] bucket_starts,
        Classifier classifier,
        Storage storage
    ) {
        Buffers buffers = new Buffers(storage.buffers_buffer, storage.buffers_indices, classifier.num_buckets());
        int first_empty_position = classifier.classify_locally(values, begin, end, bucket_starts, buffers);
        //@ ghost \dl_Heap heapAfterClassify = \dl_heap();

        BucketPointers bucket_pointers = new BucketPointers(
            bucket_starts,
            classifier.num_buckets(),
            first_empty_position - begin,
            storage.bucket_pointers
        );

        /*@ assert
          @     \invariant_for(classifier) &&
          @     Buffers.blockAligned(end - begin) == bucket_pointers.bucketStart(bucket_pointers.num_buckets);
          @*/
        /*@ assert
          @     bucket_pointers.initialReadAreasCount(values, begin, end) &&
          @     bucket_pointers.initialReadAreasBlockClassified(classifier, values, begin, end) &&
          @     bucket_pointers.initialReadAreasCountBucketElements(classifier, values, begin, end);
          @*/
        /*@ assert (\forall int b; 0 <= b < classifier.num_buckets;
          @     \at(classifier.countClassOfSliceEq(values, begin, first_empty_position, b), heapAfterClassify) ==
          @         bucket_pointers.elementsToReadCountClassEq(classifier, values, begin, end, b)
          @ );
          @*/

        int[] overflow = storage.overflow;
        Permute.permute(values, begin, end, classifier, bucket_pointers, storage.swap_1, storage.swap_2, overflow);

        Cleanup.cleanup(values,
            begin,
            end,
            buffers,
            bucket_starts,
            bucket_pointers,
            classifier,
            overflow);

        //@ assert Functions.isValidBucketStarts(bucket_starts, classifier.num_buckets);
        //@ assert Partition.bucketCountsToTotalCount(values, begin, end, bucket_starts, classifier.num_buckets);
        //@ assert (\forall int element; true; Functions.countElement(values, begin, end, element) == \old(Functions.countElement(values, begin, end, element)));
    }
}
