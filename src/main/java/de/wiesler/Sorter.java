package de.wiesler;

public final class Sorter {
    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires Constants.ACTUAL_BASE_CASE_SIZE < end - begin <= Buffers.MAX_LEN;
      @ requires \invariant_for(storage);
      @ requires \disjoint(storage.allArrays, values[*]);
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @ ensures \result.isValidForLen(end - begin);
      @ ensures Functions.isSortedSlice(values, begin, begin + \result.num_samples);
      @ ensures \invariant_for(storage);
      @ ensures \fresh(\result);
      @
      @ // Calls sort directly => +0
      @ measured_by end - begin, 0;
      @
      @ assignable storage.allArrays;
      @ assignable values[begin..end - 1];
      @*/
    private static SampleParameters sample(int[] values, int begin, int end, Storage storage) {
        SampleParameters parameters = new SampleParameters(end - begin);
        /*@ normal_behaviour
          @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
          @ measured_by end - begin, 0;
          @ assignable \strictly_nothing;
          @*/
        {;;}

        Functions.select_n(values, begin, end, parameters.num_samples);
        /*@ normal_behaviour
          @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
          @ measured_by end - begin, 0;
          @ assignable \strictly_nothing;
          @*/
        {;;}
        //@ ghost \seq before_sort = \dl_seq_def_workaround(begin, end, values);
        sort(values, begin, begin + parameters.num_samples, storage);
        /*@ normal_behaviour
          @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), before_sort);
          @ measured_by end - begin, 0;
          @ assignable \strictly_nothing;
          @*/
        {;;}

        return parameters;
    }

    /*@ public model_behaviour
      @ requires true;
      @
      @ static model boolean isBucketPartitioned(int[] values, int begin, int end, int bucket_begin, int bucket_end) {
      @     return // for all bucket elements
      @         (\forall
      @             int i;
      @             begin + bucket_begin <= i < begin + bucket_end;
      @             // all subsequent elements are bigger
      @             (\forall int j; begin + bucket_end <= j < end; values[i] < values[j])
      @         );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && end - begin == bucket_starts[num_buckets];
      @
      @ // accessible values[begin..end - 1], bucket_starts[0..num_buckets + 1];
      @
      @ static model boolean allBucketsPartitioned(int[] values, int begin, int end, int[] bucket_starts, int num_buckets) {
      @     return (\forall int b; 0 <= b < num_buckets; Sorter.isBucketPartitioned(values, begin, end, bucket_starts[b], bucket_starts[b + 1]));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires \invariant_for(classifier);
      @ requires 0 <= begin <= end <= values.length;
      @ requires nonEmptyBucketsLemma(classifier, values, begin, end, bucket_starts);
      @ requires classifier.classOfTrans();
      @ requires Functions.isValidBucketStarts(bucket_starts, classifier.num_buckets) && end - begin == bucket_starts[classifier.num_buckets];
      @ requires Partition.allBucketsClassified(values, begin, end, classifier, bucket_starts);
      @
      @ ensures \result;
      @
      @ static model boolean allBucketsPartitionedLemma(Classifier classifier, int[] values, int begin, int end, int[] bucket_starts) {
      @     return allBucketsPartitioned(values, begin, end, bucket_starts, classifier.num_buckets);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires 0 <= lower && lower <= upper && upper <= num_buckets;
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && end - begin == bucket_starts[num_buckets];
      @
      @ // accessible values[begin..end - 1], bucket_starts[0..num_buckets + 1];
      @
      @ static model boolean allBucketsInRangeSorted(int[] values, int begin, int end, int[] bucket_starts, int num_buckets, int lower, int upper) {
      @     return (\forall int b; lower <= b < upper; Functions.isSortedSlice(values, begin + bucket_starts[b], begin + bucket_starts[b + 1]));
      @ }
      @*/

    /*@ public model_behaviour
      @ accessible values[begin..end - 1];
      @
      @ static model boolean isEqualityBucket(int[] values, int begin, int end) {
      @     return
      @         (\forall int i; begin <= i < end - 1; values[i] == values[i + 1]);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires 0 <= lower && lower <= upper && upper <= num_buckets;
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && end - begin == bucket_starts[num_buckets];
      @
      @ // accessible values[begin..end - 1], bucket_starts[lower..upper];
      @
      @ static model boolean equalityBucketsInRange(int[] values, int begin, int end, int[] bucket_starts, int num_buckets, int lower, int upper) {
      @     return
      @         (\forall int b;
      @             lower <= b < upper && b % 2 == 1;
      @             Sorter.isEqualityBucket(values, begin + bucket_starts[b], begin + bucket_starts[b + 1]));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires \invariant_for(classifier);
      @ requires 0 <= begin <= end <= values.length;
      @ requires Functions.isValidBucketStarts(bucket_starts, classifier.num_buckets) && end - begin == bucket_starts[classifier.num_buckets];
      @ requires Partition.allBucketsClassified(values, begin, end, classifier, bucket_starts);
      @
      @ ensures \result;
      @
      @ static model boolean equalityBucketsLemma(Classifier classifier, int[] values, int begin, int end, int[] bucket_starts) {
      @     return classifier.equal_buckets ==>
      @         Sorter.equalityBucketsInRange(values, begin, end, bucket_starts, classifier.num_buckets, 1, classifier.num_buckets - 1);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @ static model boolean smallBucketIsSorted(int[] values, int begin, int end, int bucket_begin, int bucket_end) {
      @     return true;
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires 0 <= lower <= upper <= num_buckets;
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && end - begin == bucket_starts[num_buckets];
      @ // accessible values[begin..end - 1], bucket_starts[lower..upper];
      @
      @ static model boolean smallBucketsInRangeSorted(int[] values, int begin, int end, int[] bucket_starts, int num_buckets, int lower, int upper) {
      @     return (\forall int b; lower <= b < upper; Sorter.smallBucketIsSorted(values, begin, end, bucket_starts[b], bucket_starts[b + 1]));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && len == bucket_starts[num_buckets];
      @
      @ accessible bucket_starts[0..num_buckets];
      @
      @ static model boolean notAllValuesInOneBucket(int[] bucket_starts, int num_buckets, int len) {
      @     return (\forall int b; 0 <= b < num_buckets; bucket_starts[b + 1] - bucket_starts[b] < len);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets);
      @ requires bucket_starts[num_buckets] == end - begin;
      @
      @ // Buckets are partitioned
      @ requires Sorter.allBucketsPartitioned(values, begin, end, bucket_starts, num_buckets);
      @
      @ // Buckets are sorted
      @ requires Sorter.allBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, 0, num_buckets);
      @
      @ requires bucketIndexFromOffset(bucket_starts, num_buckets, end - begin);
      @
      @ ensures \result;
      @
      @ static model boolean sortednessFromPartitionSorted(int[] values, int begin, int end, int[] bucket_starts, int num_buckets) {
      @     return Functions.isSortedSlice(values, begin, end);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets);
      @ requires bucket_starts[num_buckets] == len;
      @
      @ ensures \result;
      @ // (   nv >= 0
      @ //  -> nv <= num_buckets & i_0 < bucket_starts[nv]
      @ //  -> \exists int b; (0 <= b & b < nv & bucket_starts[b] <= i_0 & i_0 < bucket_starts[b + 1]))
      @
      @ static model boolean bucketIndexFromOffset(int[] bucket_starts, int num_buckets, int len) {
      @     return (\forall int i; 0 <= i < len; (\exists int b; 0 <= b < num_buckets; bucket_starts[b] <= i < bucket_starts[b + 1]));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires \invariant_for(classifier);
      @ requires Functions.isValidBucketStarts(bucket_starts, classifier.num_buckets) && end - begin == bucket_starts[classifier.num_buckets];
      @ requires bucketIndexFromOffset(bucket_starts, classifier.num_buckets, end - begin);
      @ requires Partition.allBucketsClassified(values, begin, end, classifier, bucket_starts);
      @
      @ ensures \result;
      @
      @ static model boolean nonEmptyBucketsLemma(Classifier classifier, int[] values, int begin, int end, int[] bucket_starts) {
      @     return (\forall int i; begin <= i < end;
      @         bucket_starts[classifier.classOf(values[i])] <= i - begin < bucket_starts[classifier.classOf(values[i]) + 1]
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && len == bucket_starts[num_buckets];
      @ requires (\forall int b; 0 <= b < num_buckets;
      @     (\exists int c; 0 <= c < num_buckets && b != c; bucket_starts[c] < bucket_starts[c + 1])
      @ );
      @
      @ ensures \result;
      @
      @ static model boolean notAllValuesInOneBucketLemma(int[] bucket_starts, int num_buckets, int len) {
      @     return notAllValuesInOneBucket(bucket_starts, num_buckets, len);
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires bucket_starts.length == Constants.MAX_BUCKETS + 1;
      @ requires (\forall int b; 0 <= b < bucket_starts.length; bucket_starts[b] == 0);
      @ requires end - begin > Constants.ACTUAL_BASE_CASE_SIZE;
      @ requires end - begin <= Buffers.MAX_LEN;
      @ requires \invariant_for(storage);
      @
      @ requires \disjoint(values[*], bucket_starts[*], storage.allArrays);
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @ ensures \result != null ==>
      @     \result.num_buckets % 2 == 0 &&
      @     Functions.isValidBucketStarts(bucket_starts, \result.num_buckets) &&
      @     bucket_starts[\result.num_buckets] == end - begin &&
      @     // Buckets are partitioned
      @     Sorter.allBucketsPartitioned(values, begin, end, bucket_starts, \result.num_buckets) &&
      @     // Small buckets are sorted
      @     Sorter.smallBucketsInRangeSorted(values, begin, end, bucket_starts, \result.num_buckets, 0, \result.num_buckets) &&
      @     // Equality buckets at odd indices except the last bucket
      @     (\result.equal_buckets ==> Sorter.equalityBucketsInRange(values, begin, end, bucket_starts, \result.num_buckets, 1, \result.num_buckets - 1)) &&
      @     Sorter.notAllValuesInOneBucket(bucket_starts, \result.num_buckets, end - begin);
      @ ensures \invariant_for(storage);
      @
      @ // Calls sample which has +0 => +1
      @ measured_by end - begin, 1;
      @
      @ assignable values[begin..end - 1];
      @ assignable storage.allArrays;
      @ assignable bucket_starts[*];
      @*/
    private static /*@ nullable */ PartitionResult partition(
            int[] values,
            int begin,
            int end,
            int[] bucket_starts,
            Storage storage
    ) {
        /*@ normal_behaviour
          @ ensures \disjoint(
          @   values[*],
          @   bucket_starts[*],
          @   storage.tree[*],
          @   storage.splitters[*],
          @   storage.bucket_pointers[*],
          @   storage.buffers_buffer[*],
          @   storage.buffers_indices[*],
          @   storage.swap_1[*],
          @   storage.swap_2[*],
          @   storage.overflow[*]
          @ );
          @
          @ assignable \strictly_nothing;
          @
          @ measured_by end - begin, 1;
          @*/
        {;;}

        //@ ghost \seq oldValues = \dl_seq_def_workaround(begin, end, values);

        final SampleParameters sample = sample(values, begin, end, storage);
        final int num_samples = sample.num_samples;
        final int num_buckets = sample.num_buckets;
        final int step = sample.step;
        final int[] splitters = storage.splitters;

        //@ ghost \seq before_copy_unique = \dl_seq_def_workaround(begin, end, values);

        // Select num_buckets - 1 splitters
        final int num_splitters = Functions.copy_unique(values, begin, begin + num_samples, num_buckets - 1, step, splitters);

        //@ ghost \seq before_from_sorted_samples = \dl_seq_def_workaround(begin, end, values);
        /*@ normal_behaviour
          @ ensures before_from_sorted_samples == before_copy_unique;
          @ assignable \strictly_nothing;
          @ measured_by end - begin, 1;
          @*/
        {;;}
        /*@ normal_behaviour
          @ ensures \dl_seqPerm(before_from_sorted_samples, oldValues);
          @ assignable \strictly_nothing;
          @ measured_by end - begin, 1;
          @*/
        {;;}

        if (num_splitters <= 1) {
            return null;
        }

        // >= 2 unique splitters, therefore >= 3 buckets and >= 2 nonempty buckets
        final Classifier classifier = Classifier.from_sorted_samples(splitters, storage.tree, num_splitters, num_buckets);

        // Create this first, classifier is immutable and this removes heap mutations after partition
        final PartitionResult r = new PartitionResult(classifier.num_buckets(), classifier.equal_buckets());

        //@ ghost \seq valuesBeforePartition = \dl_seq_def_workaround(begin, end, values);
        /*@ normal_behaviour
          @ ensures valuesBeforePartition == before_from_sorted_samples;
          @ ensures \invariant_for(classifier);
          @ assignable \strictly_nothing;
          @ measured_by end - begin, 1;
          @*/
        {;;}
        /*@ normal_behaviour
          @ ensures \dl_seqPerm(valuesBeforePartition, oldValues);
          @ ensures (\exists int i; begin <= i < end; (\exists int j; begin <= j < end; classifier.classOf(values[i]) != classifier.classOf(values[j])));
          @ assignable \strictly_nothing;
          @ measured_by end - begin, 1;
          @*/
        {;;}
        Partition.partition(values, begin, end, bucket_starts, classifier, storage);

        //@ ghost \seq valuesAfterPartition = \dl_seq_def_workaround(begin, end, values);
        /*@ normal_behaviour
          @ ensures bucketIndexFromOffset(bucket_starts, classifier.num_buckets, end - begin);
          @ ensures (\exists int i; 0 <= i < valuesAfterPartition.length;
          @     (\exists int j; 0 <= j < valuesAfterPartition.length;
          @         classifier.classOf((int) valuesAfterPartition[i]) != classifier.classOf((int) valuesAfterPartition[j]))
          @ );
          @ assignable \strictly_nothing;
          @ measured_by end - begin, 1;
          @*/
        {;;}

        /*@ normal_behaviour
          @ ensures (\exists int i; begin <= i < end; (\exists int j; begin <= j < end; classifier.classOf(values[i]) != classifier.classOf(values[j])));
          @ ensures nonEmptyBucketsLemma(classifier, values, begin, end, bucket_starts);
          @ ensures equalityBucketsLemma(classifier, values, begin, end, bucket_starts);
          @ assignable \strictly_nothing;
          @ measured_by end - begin, 1;
          @*/
        {;;}

        /*@ normal_behaviour
          @ ensures notAllValuesInOneBucketLemma(bucket_starts, classifier.num_buckets, end - begin);
          @ ensures allBucketsPartitionedLemma(classifier, values, begin, end, bucket_starts);
          @ assignable \strictly_nothing;
          @ measured_by end - begin, 1;
          @*/
        {;;}

        // assignable: apply eq of allArrays

        return r;
    }

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires end - begin <= Buffers.MAX_LEN;
      @ requires 0 <= bucket && bucket < num_buckets;
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && bucket_starts[num_buckets] == end - begin;
      @ requires Sorter.allBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, 0, bucket);
      @
      @ // Stays partitioned
      @ requires Sorter.allBucketsPartitioned(values, begin, end, bucket_starts, num_buckets);
      @ // All subsequent buckets keep the sorting property
      @ requires Sorter.smallBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, bucket, num_buckets);
      @ // Equality buckets
      @ requires equal_buckets ==>
      @     (bucket % 2 == 0 || bucket == num_buckets - 1) &&
      @     // starting at the next bucket, ending before the last bucket
      @     Sorter.equalityBucketsInRange(values, begin, end, bucket_starts, num_buckets, bucket + 1, num_buckets - 1);
      @ requires Sorter.notAllValuesInOneBucket(bucket_starts, num_buckets, end - begin);
      @ requires \disjoint(storage.allArrays, values[*], bucket_starts[*]);
      @ requires \invariant_for(storage);
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @
      @ // Previous stay sorted, current is now sorted
      @ ensures Sorter.allBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, 0, bucket + 1);
      @ // Stays partitioned
      @ ensures Sorter.allBucketsPartitioned(values, begin, end, bucket_starts, num_buckets);
      @ // All subsequent buckets keep the sorting property
      @ ensures Sorter.smallBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, bucket + 1, num_buckets);
      @ // Equality buckets at odd indices except the last bucket
      @ ensures equal_buckets ==>
      @     Sorter.equalityBucketsInRange(values, begin, end, bucket_starts, num_buckets, bucket + 1, num_buckets - 1);
      @ ensures \invariant_for(storage);
      @
      @ assignable values[begin..end - 1];
      @ assignable storage.allArrays;
      @
      @ measured_by end - begin, 1;
      @*/
    private static void sample_sort_recurse_on(int[] values, int begin, int end, Storage storage, int[] bucket_starts, int num_buckets, boolean equal_buckets, int bucket) {
        int inner_begin = begin + bucket_starts[bucket];
        int inner_end = begin + bucket_starts[bucket + 1];

        /*@ normal_behaviour
          @ ensures Functions.bucketStartsOrdering(bucket_starts, num_buckets, bucket);
          @ assignable \strictly_nothing;
          @ measured_by end - begin, 1;
          @*/
        {;;}
        /*@ normal_behaviour
          @ ensures 0 <= bucket_starts[bucket] <= bucket_starts[bucket + 1] <= bucket_starts[num_buckets] &&
          @     (\forall int b; 0 <= b < num_buckets && b != bucket;
          @         (b < bucket ==> 0 <= bucket_starts[b] <= bucket_starts[b + 1] <= bucket_starts[bucket]) &&
          @         (b > bucket ==> bucket_starts[bucket + 1] <= bucket_starts[b] <= bucket_starts[b + 1] <= bucket_starts[num_buckets]));
          @ assignable \strictly_nothing;
          @ measured_by end - begin, 1;
          @*/
        {;;}
        /*@ normal_behaviour
          @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin + bucket_starts[bucket], inner_end, values), \old(\dl_seq_def_workaround(begin + bucket_starts[bucket], begin + bucket_starts[bucket + 1], values)));
          @ ensures Functions.isSortedSlice(values, begin + bucket_starts[bucket], inner_end);
          @ assignable values[inner_begin..inner_end - 1], storage.allArrays;
          @ measured_by end - begin, 1;
          @*/
        {
            if (inner_end - inner_begin > Constants.ACTUAL_BASE_CASE_SIZE) {
                sample_sort(values, inner_begin, inner_end, storage);
            } else {
                base_case_sort(values, inner_begin, inner_end);
            }
        }
        /*@ normal_behaviour
          @ ensures \dl_seq_def_workaround(begin, inner_begin, values) == \old(\dl_seq_def_workaround(begin, begin + bucket_starts[bucket], values));
          @ ensures \dl_seq_def_workaround(inner_end, end, values) == \old(\dl_seq_def_workaround(begin + bucket_starts[bucket + 1], end, values));
          @ assignable \strictly_nothing;
          @ measured_by end - begin, 1;
          @*/
        {;;}
        /*@ normal_behaviour
          @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, inner_begin, values), \old(\dl_seq_def_workaround(begin, begin + bucket_starts[bucket], values)));
          @ ensures \dl_seqPerm(\dl_seq_def_workaround(inner_end, end, values), \old(\dl_seq_def_workaround(begin + bucket_starts[bucket + 1], end, values)));
          @ assignable \strictly_nothing;
          @ measured_by end - begin, 1;
          @*/
        {;;}
    }

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires end - begin > Constants.ACTUAL_BASE_CASE_SIZE;
      @ requires end - begin <= Buffers.MAX_LEN;
      @ requires \invariant_for(storage);
      @ requires \disjoint(storage.allArrays, values[*]);
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @ ensures Functions.isSortedSlice(values, begin, end);
      @ ensures \invariant_for(storage);
      @
      @ // partition has +1, sample_sort_recurse +0 => +2
      @ measured_by end - begin, 2;
      @
      @ assignable values[begin..end - 1];
      @ assignable storage.allArrays;
      @*/
    private static void sample_sort(int[] values, int begin, int end, Storage storage) {
        int[] bucket_starts = Storage.createArray(Constants.MAX_BUCKETS + 1);

        /*@ normal_behaviour
          @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
          @ ensures \disjoint(\all_fields(values), \all_fields(bucket_starts), storage.allArrays);
          @ ensures \disjoint(storage.*, storage.allArrays);
          @
          @ assignable \strictly_nothing;
          @
          @ measured_by end - begin, 2;
          @*/
        {;;}

        PartitionResult partition = partition(values, begin, end, bucket_starts, storage);

        if (partition == null) {
            fallback_sort(values, begin, end);
            return;
        }

        int num_buckets = partition.num_buckets;
        boolean equal_buckets = partition.equal_buckets;

        /*@ normal_behaviour
          @ // this is needed in many places and harder to deduce
          @ requires \disjoint(\all_fields(values), \all_fields(bucket_starts), storage.allArrays, storage.*);
          @
          @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
          @ ensures Sorter.allBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, 0, num_buckets);
          @ ensures Sorter.allBucketsPartitioned(values, begin, end, bucket_starts, num_buckets);
          @
          @ assignable values[begin..end - 1];
          @ assignable storage.allArrays;
          @
          @ measured_by end - begin, 2;
          @*/
        {
            /*@ loop_invariant 0 <= bucket && bucket <= num_buckets;
              @ loop_invariant equal_buckets ==> bucket % 2 == 0;
              @ loop_invariant \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
              @
              @ loop_invariant Sorter.allBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, 0, bucket < num_buckets || !equal_buckets ? bucket : num_buckets - 1);
              @ // Stays partitioned
              @ loop_invariant Sorter.allBucketsPartitioned(values, begin, end, bucket_starts, num_buckets);
              @ // All subsequent buckets keep the small sorted property (especially the last one if equal_buckets)
              @ loop_invariant Sorter.smallBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, bucket < num_buckets || !equal_buckets ? bucket : num_buckets - 1, num_buckets);
              @ loop_invariant equal_buckets ==>
              @     bucket % 2 == 0 && bucket != num_buckets - 1 &&
              @     // starting at the next bucket, ending before the last bucket
              @     Sorter.equalityBucketsInRange(values, begin, end, bucket_starts, num_buckets, bucket + 1, num_buckets - 1);
              @
              @ decreases num_buckets - bucket;
              @
              @ assignable values[begin..end - 1];
              @ assignable storage.allArrays;
              @*/
            for (int bucket = 0; bucket < num_buckets; bucket += 1 + Constants.toInt(equal_buckets)) {
                sample_sort_recurse_on(values, begin, end, storage, bucket_starts, num_buckets, equal_buckets, bucket);
            }

            if (equal_buckets) {
                sample_sort_recurse_on(values, begin, end, storage, bucket_starts, num_buckets, equal_buckets, num_buckets - 1);
            }
        }

        /*@ normal_behaviour
          @ ensures sortednessFromPartitionSorted(values, begin, end, bucket_starts, num_buckets);
          @
          @ assignable \strictly_nothing;
          @
          @ measured_by end - begin, 2;
          @*/
        {;;}
    }

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @ ensures (\forall int element; true;
      @     Functions.countElement(values, begin, end, element) ==
      @         \old(Functions.countElement(values, begin, end, element))
      @ );
      @ ensures Functions.isSortedSlice(values, begin, end);
      @
      @ assignable values[begin..end - 1];
      @*/
    public static void fallback_sort(int[] values, int begin, int end) {
        insertion_sort(values, begin, end);
    }

    /*@ model_behaviour
      @   requires 0 <= idx < seq.length;
      @   ensures (\forall int x; 0 <= x < seq.length; 
      @              \result[x] == (x == idx ? value : seq[x]));
      @   ensures \result.length == seq.length;
      @ static no_state model \seq seqUpd(\seq seq, int idx, int value) {
      @   return \seq_concat(\seq_concat(
      @     \seq_sub(seq, 0, idx),
      @     \seq_singleton(value)),
      @     \seq_sub(seq, idx+1, seq.length));
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @
      @ ensures Functions.isSortedSlice(values, begin, end);
      @
      @ assignable values[begin..end - 1];
      @*/
    public static void insertion_sort(int[] values, int begin, int end) {
        if (end - begin < 2) return;
        int k = begin + 1;

        /*@ loop_invariant \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), 
          @                       \old(\dl_seq_def_workaround(begin, end, values)));
          @ loop_invariant begin < k <= end;
          @ loop_invariant (\forall int x; k <= x < end; values[x] == \old(values[x]));
          @ loop_invariant Functions.isSortedSlice(values, begin, k);
          @ assignable values[begin..end - 1];
          @ decreases end - k;
          @*/
        for (; k < end; ++k) {
            int value = values[k];
            int hole = k;

            /*@ loop_invariant hole == i + 1;
              @ loop_invariant begin-1 <= i < k;
              @ loop_invariant i == k - 1 || Functions.isSortedSlice(values, begin, k+1);
              @ loop_invariant Functions.isSortedSlice(values, begin, k);
              @ loop_invariant \dl_seqPerm(
              @    seqUpd(\dl_seq_def_workaround(begin, end, values), hole - begin, value), 
              @    \old(\dl_seq_def_workaround(begin, end, values)));
              @ loop_invariant value <= values[hole];
              @ assignable values[begin..k];
              @ decreases i + 1;
             */
            for(int i = k - 1; i >= begin && value < values[i]; i--) {
                values[hole] = values[i];
                hole = i;
            }

            values[hole] = value;
        }
    }

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @ ensures Functions.isSortedSlice(values, begin, end);
      @
      @ assignable values[begin..end - 1];
      @*/
    private static void base_case_sort(int[] values, int begin, int end) {
        fallback_sort(values, begin, end);
    }

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires end - begin <= Buffers.MAX_LEN;
      @ requires \invariant_for(storage);
      @ requires \disjoint(storage.allArrays, values[*]);
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @ ensures Functions.isSortedSlice(values, begin, end);
      @ ensures \invariant_for(storage);
      @
      @ // sample_sort has +2 => +3
      @ measured_by end - begin, 3;
      @
      @ assignable values[begin..end - 1];
      @ assignable storage.allArrays;
      @*/
    public static void sort(int[] values, int begin, int end, Storage storage) {
        if (end - begin <= Constants.ACTUAL_BASE_CASE_SIZE) {
            base_case_sort(values, begin, end);
        } else {
            sample_sort(values, begin, end, storage);
        }
    }

    /*@ public normal_behaviour
      @ requires values.length <= Buffers.MAX_LEN;
      @
      @ ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
      @ ensures Functions.isSortedSlice(values, 0, values.length);
      @
      @ assignable values[*];
      @*/
    public static void sort(int[] values) {
        Storage storage = new Storage();
        //@ assert \disjoint(storage.allArrays, values);
        sort(values, 0, values.length, storage);
    }
}
