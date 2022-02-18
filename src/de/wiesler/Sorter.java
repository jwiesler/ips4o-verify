package de.wiesler;

public final class Sorter {
    private static class PartitionResult {
        public final int num_buckets;
        public final boolean equal_buckets;

        public PartitionResult(int num_buckets, boolean equal_buckets) {
            this.num_buckets = num_buckets;
            this.equal_buckets = equal_buckets;
        }
    }

    private static class SampleResult {
        public final int num_samples;
        public final int num_buckets;
        public final int step;

        public /*@ strictly_pure */ SampleResult(int num_samples, int num_buckets, int step) {
            this.num_samples = num_samples;
            this.num_buckets = num_buckets;
            this.step = step;
        }
    }

    /*@ public model_behaviour
      @ requires n >= 1;
      @ accessible \nothing;
      @ static model boolean isValidSampleResultForLen(SampleResult r, int n) {
      @     return
      @         2 <= r.num_samples <= n / 2 &&
      @         // This states the same as the previous line but is somehow hard to deduce
      @         r.num_samples < n &&
      @         1 <= r.step &&
      @         2 <= r.num_buckets <= 1 << Constants.LOG_MAX_BUCKETS &&
      @         r.num_buckets % 2 == 0 &&
      @         // there are enough samples to perform num_buckets selections with the given step size
      @         r.step * r.num_buckets - 1 <= r.num_samples;
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires n >= Constants.BASE_CASE_SIZE;
      @
      @ ensures isValidSampleResultForLen(\result, n);
      @ ensures \fresh(\result);
      @
      @ assignable \nothing;
      @*/
    private static SampleResult sample_parameters(int n) {
        int log_buckets = Constants.log_buckets(n);
        int num_buckets = 1 << log_buckets;
        //@ assert num_buckets * Constants.BASE_CASE_SIZE <= n;
        int step = Functions.max(1, Constants.oversampling_factor(n));
        //@ assert (1 << step) <= n / 5;
        //@ assert 0 < step * num_buckets - 1 && step * num_buckets - 1 <= n / 2;
        int num_samples = Functions.min(step * num_buckets - 1, n / 2);

        return new SampleResult(num_samples, num_buckets, step);
    }

    /*@ public normal_behaviour
      @ requires Storage.brandOf(values) == Storage.VALUES;
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires end - begin >= Constants.BASE_CASE_SIZE;
      @ requires \invariant_for(storage);
      @ requires \disjoint(storage.allArrays, values[*]);
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @ ensures isValidSampleResultForLen(\result, end - begin);
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
    private static SampleResult sample(int[] values, int begin, int end, Storage storage) {
        SampleResult result = sample_parameters(end - begin);

        Functions.select_n(values, begin, end, result.num_samples);
        sort(values, begin, begin + result.num_samples, storage);

        return result;
    }

    /*@ public model_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires bucket_begin <= bucket_end;
      @ requires begin <= begin + bucket_begin <= end;
      @ requires begin <= begin + bucket_end <= end;
      @
      @ accessible values[begin..end - 1];
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
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && end - begin == bucket_starts[num_buckets];
      @
      @ accessible values[begin..end - 1];
      @
      @ static model boolean allBucketsPartitioned(int[] values, int begin, int end, int[] bucket_starts, int num_buckets) {
      @     return (\forall int b; 0 <= b < num_buckets; Sorter.isBucketPartitioned(values, begin, end, bucket_starts[b], bucket_starts[b + 1]));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires 0 <= lower && lower <= upper && upper <= num_buckets;
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && end - begin == bucket_starts[num_buckets];
      @
      @ accessible values[begin..end - 1];
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
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires 0 <= lower && lower <= upper && upper <= num_buckets;
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && end - begin == bucket_starts[num_buckets];
      @
      @ accessible values[begin..end - 1];
      @
      @ static model boolean equalityBucketsInRange(int[] values, int begin, int end, int[] bucket_starts, int num_buckets, int lower, int upper) {
      @     return
      @         (\forall int b;
      @             lower <= b < upper && b % 2 == 1;
      @             Sorter.isEqualityBucket(values, begin + bucket_starts[b], begin + bucket_starts[b + 1]));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires Functions.isValidSubSlice(values, begin, end, begin + bucket_begin, begin + bucket_end);
      @
      @ accessible values[begin + bucket_begin..begin + bucket_end - 1];
      @
      @ static model boolean smallBucketIsSorted(int[] values, int begin, int end, int bucket_begin, int bucket_end) {
      @     return bucket_end - bucket_begin <= 2 * Constants.BASE_CASE_SIZE || end - begin <= Constants.SINGLE_LEVEL_THRESHOLD ==>
      @             Functions.isSortedSlice(values, begin + bucket_begin, begin + bucket_end);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires 0 <= lower && lower <= upper && upper <= num_buckets;
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && end - begin == bucket_starts[num_buckets];
      @
      @ accessible values[begin..end - 1];
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

    /*@ public normal_behaviour
      @ requires Storage.brandOf(values) == Storage.VALUES;
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires Storage.brandOf(bucket_starts) == Storage.BUCKET_STARTS;
      @ requires bucket_starts.length == Constants.MAX_BUCKETS + 1;
      @ requires (\forall int b; 0 <= b < bucket_starts.length; bucket_starts[b] == 0);
      @ requires end - begin >= Constants.BASE_CASE_SIZE;
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

        Classifier classifier;
        {
            SampleResult sample = sample(values, begin, end, storage);
            final int num_samples = sample.num_samples;
            final int num_buckets = sample.num_buckets;
            final int step = sample.step;
            final int[] splitters = storage.splitters;

            // Select num_buckets - 1 splitters
            int num_splitters = Functions.copy_unique(values, begin, begin + num_samples, num_buckets - 1, step, splitters);

            if (num_splitters <= 1) {
                return null;
            }

            // >= 2 unique splitters, therefore >= 3 buckets and >= 2 nonempty buckets
            classifier = Classifier.from_sorted_samples(splitters, storage.tree, num_splitters, num_buckets);
        }

        Buffers buffers = new Buffers(storage.buffers_buffer, storage.buffers_indices, classifier.num_buckets());
        int first_empty_position = classifier.classify_locally(values, begin, end, bucket_starts, buffers);

        BucketPointers bucket_pointers = new BucketPointers(
                bucket_starts,
                classifier.num_buckets(),
                first_empty_position - begin,
                storage.bucket_pointers
        );

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

        return new PartitionResult(classifier.num_buckets(), classifier.equal_buckets());
    }

    /*@ public normal_behaviour
      @ requires Storage.brandOf(values) == Storage.VALUES;
      @ requires Storage.brandOf(bucket_starts) == Storage.BUCKET_STARTS;
      @ requires Functions.isValidSlice(values, begin, end);
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
      @ requires \disjoint(storage.allArrays, values[*]);
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
        int inner_start = begin + bucket_starts[bucket];
        int inner_end = begin + bucket_starts[bucket + 1];

        if (inner_end - inner_start > 2 * Constants.BASE_CASE_SIZE) {
            /*@ normal_behaviour
              @ ensures \disjoint(bucket_starts[*], values[*], storage.*);
              @
              @ ensures Lemma.bucketStartsOrdering(bucket_starts, num_buckets, bucket) ==>
              @     0 <= bucket_starts[bucket] <= bucket_starts[bucket + 1] <= bucket_starts[num_buckets] &&
              @     (\forall int b; 0 <= b < num_buckets && b != bucket;
              @         (b < bucket ==> 0 <= bucket_starts[b] <= bucket_starts[b + 1] <= bucket_starts[bucket]) &&
              @         (b > bucket ==> bucket_starts[bucket + 1] <= bucket_starts[b] <= bucket_starts[b + 1] <= bucket_starts[num_buckets]));
              @
              @ assignable \strictly_nothing;
              @
              @ measured_by end - begin, 1;
              @*/
            {;;}
            sample_sort(values, inner_start, inner_end, storage);
        }
    }

    /*@ public normal_behaviour
      @ requires Storage.brandOf(values) == Storage.VALUES;
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires end - begin > 2 * Constants.BASE_CASE_SIZE;
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
        int[] bucket_starts = Storage.createBrandedArray(Constants.MAX_BUCKETS + 1, Storage.BUCKET_STARTS);

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
            if (end - begin > Constants.SINGLE_LEVEL_THRESHOLD) {
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
        }

        /*@ normal_behaviour
          @ ensures Lemma.sortednessFromPartitionSorted(values, begin, end, bucket_starts, num_buckets);
          @
          @ assignable \strictly_nothing;
          @
          @ measured_by end - begin, 2;
          @*/
        {;;}
    }

    /*@ public normal_behaviour
      @ requires Functions.isValidSlice(values, start, end);
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(start, end, values), \old(\dl_seq_def_workaround(start, end, values)));
      @ ensures Functions.isSortedSlice(values, start, end);
      @
      @ assignable values[start..end - 1];
      @*/
    public static void fallback_sort(int[] values, int start, int end) {
//        java.util.Arrays.sort(values, start, end);
    }

    /*@ public normal_behaviour
      @ requires Functions.isValidSlice(values, start, end);
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(start, end, values), \old(\dl_seq_def_workaround(start, end, values)));
      @ ensures Functions.isSortedSlice(values, start, end);
      @
      @ assignable values[start..end - 1];
      @*/
    private static void base_case_sort(int[] values, int start, int end) {
        fallback_sort(values, start, end);
    }

    /*@ public normal_behaviour
      @ requires Storage.brandOf(values) == Storage.VALUES;
      @ requires Functions.isValidSlice(values, start, end);
      @ requires \invariant_for(storage);
      @ requires \disjoint(storage.allArrays, values[*]);
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(start, end, values), \old(\dl_seq_def_workaround(start, end, values)));
      @ ensures Functions.isSortedSlice(values, start, end);
      @ ensures \invariant_for(storage);
      @
      @ // sample_sort has +2 => +3
      @ measured_by end - start, 3;
      @
      @ assignable values[start..end - 1];
      @ assignable storage.allArrays;
      @*/
    public static void sort(int[] values, int start, int end, Storage storage) {
        if (end - start <= 2 * Constants.BASE_CASE_SIZE) {
            base_case_sort(values, start, end);
        } else {
            sample_sort(values, start, end, storage);
        }
    }

    /*@ public normal_behaviour
      @ ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
      @ ensures Functions.isSortedSlice(values, 0, values.length);
      @
      @ assignable values[*];
      @*/
    public static void sort(int[] values) {
        Storage.brandArray(values, Storage.VALUES);
        Storage storage = new Storage();
        //@ assert \disjoint(storage.allArrays, values);
        sort(values, 0, values.length, storage);
    }
}
