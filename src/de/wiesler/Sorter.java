package de.wiesler;

public class Sorter {
    private static class PartitionResult {
        public int num_buckets;
        public boolean equal_buckets;

        public PartitionResult(int num_buckets, boolean equal_buckets) {
            this.num_buckets = num_buckets;
            this.equal_buckets = equal_buckets;
        }
    }

    private static class SampleResult {
        public int num_samples;
        public int num_buckets;
        public int step;

        public /*@ strictly_pure */ SampleResult(int num_samples, int num_buckets, int step) {
            this.num_samples = num_samples;
            this.num_buckets = num_buckets;
            this.step = step;
        }
    }

    /*@ public model_behaviour
      @ requires n >= 1;
      @ accessible r.*;
      @ static model boolean isValidSampleResultForLen(SampleResult r, int n) {
      @     return 
      @         Functions.isBetweenInclusive(r.num_samples, 2, n / 2) &&
      @         1 <= r.step &&
      @         Functions.isBetweenInclusive(r.num_buckets, 2, 1 << Constants.LOG_MAX_BUCKETS) &&
      @         // there are enough samples to perform num_buckets selections with the given step size
      @         r.step * r.num_buckets - 1 <= r.num_samples;
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires n >= Constants.BASE_CASE_SIZE;
      @
      @ ensures isValidSampleResultForLen(\result, n);
      @ 
      @ assignable \strictly_nothing;
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
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires end - begin >= Constants.BASE_CASE_SIZE;
      @
      @ ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
      @ ensures isValidSampleResultForLen(\result, end - begin);
      @ ensures Functions.isSortedSlice(values, begin, begin + \result.num_samples);
      @ 
      @ // Calls sort directly => +0
      @ measured_by end - begin, 0;
      @
      @ assignable storage.*;
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
      @ requires Functions.isBetweenInclusive(begin + bucket_begin, begin, end);
      @ requires Functions.isBetweenInclusive(begin + bucket_end, begin, end);
      @ 
      @ accessible values[begin..end - 1];
      @
      @ static model boolean isBucketPartitioned(int[] values, int begin, int end, int bucket_begin, int bucket_end) {
      @     return // for all bucket elements
      @         (\forall
      @             int i;
      @             begin + bucket_begin <= i < begin + bucket_end;
      @             // all previous elements are smaller
      @             (\forall int j; begin <= j < begin + bucket_begin; values[j] < values[i]) &&
      @             // all subsequent elements are bigger
      @             (\forall int j; begin + bucket_end <= j < end; values[i] < values[j])
      @         );
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

    /*@ public normal_behaviour
      @ requires bucket_starts.length == Constants.MAX_BUCKETS + 1;
      @ requires (\forall int b; 0 <= b < bucket_starts.length; bucket_starts[b] == 0);
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires end - begin >= Constants.BASE_CASE_SIZE;
      @
      @ ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
      @ ensures \result != null ==>
      @     \result.num_buckets % 2 == 0 &&
      @     Functions.isValidBucketStarts(bucket_starts, \result.num_buckets) &&
      @     bucket_starts[\result.num_buckets] == end - begin &&
      @     // Buckets are partitioned
      @     (\forall int b; 0 <= b < \result.num_buckets; Sorter.isBucketPartitioned(values, begin, end, bucket_starts[b], bucket_starts[b + 1])) &&
      @     // Small buckets are sorted
      @     (\forall int b; 0 <= b < \result.num_buckets; Sorter.smallBucketIsSorted(values, begin, end, bucket_starts[b], bucket_starts[b + 1])) &&
      @     // Equality buckets at odd indices except the last bucket
      @     (\result.equal_buckets ==> 
      @         (\forall int b; 
      @             0 <= b < \result.num_buckets - 1 && b % 2 == 1;
      @             (\forall int i; 
      @                 bucket_starts[b] <= i < bucket_starts[b + 1]; 
      @                 values[begin + bucket_starts[b]] == values[begin + i]))
      @     ) &&
      @     // At least two non empty buckets
      @     (\num_of int b; 0 <= b < \result.num_buckets; bucket_starts[b + 1] - bucket_starts[b] > 0) >= 2;
      @
      @ // Calls sample which has +0 => +1
      @ measured_by end - begin, 1;
      @ 
      @ assignable values[begin..end - 1];
      @ assignable storage.*;
      @ assignable bucket_starts[*];
      @*/
    private static /*@ nullable */ PartitionResult partition(
            int[] values,
            int begin,
            int end,
            int[] bucket_starts,
            Storage storage
    ) {
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
                classifier.num_buckets(),
                overflow);

        return new PartitionResult(classifier.num_buckets(), classifier.equal_buckets());
    }

    /*@ public normal_behaviour
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && bucket_starts[num_buckets] == end - begin;
      @ // Buckets are partitioned
      @ requires (\forall int b; 0 <= b < num_buckets; Sorter.isBucketPartitioned(values, begin, end, bucket_starts[b], bucket_starts[b + 1]));
      @ // Small buckets are sorted
      @ requires (\forall int b; 0 <= b < num_buckets; Sorter.smallBucketIsSorted(values, begin, end, bucket_starts[b], bucket_starts[b + 1]));
      @ // Equality buckets at odd indices except the last bucket
      @ requires equal_buckets ==> 
      @         (\forall int b; 
      @             0 <= b < num_buckets - 1 && b % 2 == 1;
      @             (\forall int i; 
      @                 bucket_starts[b] <= i < bucket_starts[b + 1]; 
      @                 values[begin + bucket_starts[b]] == values[begin + i]));
      @ // At least two non empty buckets
      @ requires (\num_of int b; 0 <= b < num_buckets; bucket_starts[b + 1] - bucket_starts[b] > 0) >= 2;
      @ 
      @ // Lemma
      @ requires Lemma.ascendingGeqFirst(bucket_starts, 0, num_buckets + 1);
      @ 
      @ ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
      @ ensures (\forall int b; 0 <= b < num_buckets; Functions.isSortedSlice(values, begin + bucket_starts[b], begin + bucket_starts[b + 1]));
      @ ensures (\forall int b; 0 <= b < num_buckets; Sorter.isBucketPartitioned(values, begin, end, bucket_starts[b], bucket_starts[b + 1]));
      @ 
      @ assignable values[begin..end - 1];
      @ assignable storage.*;
      @ 
      @ // calls sample_sort directly => +0
      @ measured_by end - begin, 0;
      @*/
    private static void sample_sort_recurse(int[] values, int begin, int end, Storage storage, int[] bucket_starts, int num_buckets, boolean equal_buckets) {
        // For every bucket there exists another bucket that is not empty
        // @ assert (\forall int b; 0 <= b < num_buckets; (\exists int o; 0 <= o < num_buckets && b != o; bucket_starts[o + 1] - bucket_starts[o] > 0));

        /*@ loop_invariant 0 <= bucket && bucket <= num_buckets;
          @ loop_invariant \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
          @ loop_invariant (\forall int b; 0 <= b < bucket; Functions.isSortedSlice(values, begin + bucket_starts[b], begin + bucket_starts[b + 1]));
          @ // Stays partitioned
          @ loop_invariant (\forall int b; 0 <= b < num_buckets; Sorter.isBucketPartitioned(values, begin, end, bucket_starts[b], bucket_starts[b + 1]));
          @ // All subsequent buckets keep the sorting property
          @ loop_invariant (\forall int b; bucket <= b < num_buckets; Sorter.smallBucketIsSorted(values, begin, end, bucket_starts[b], bucket_starts[b + 1]));
          @
          @ decreases num_buckets - bucket;
          @
          @ assignable values[begin..end - 1];
          @ assignable storage.*;
          @*/
        for (int bucket = 0; bucket < num_buckets; bucket += 1 + Constants.toInt(equal_buckets)) {
            int inner_start = begin + bucket_starts[bucket];
            int inner_end = begin + bucket_starts[bucket + 1];
            if (inner_end - inner_start > 2 * Constants.BASE_CASE_SIZE) {
                sample_sort(values, inner_start, inner_end, storage);
            }
        }

        if (equal_buckets) {
            int inner_start = begin + bucket_starts[num_buckets - 1];
            int inner_end = begin + bucket_starts[num_buckets];
            if (inner_end - inner_start > 2 * Constants.BASE_CASE_SIZE) {
                sample_sort(values, inner_start, inner_end, storage);
            }
        }
    }

    /*@ public normal_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires Functions.isValidSubSlice(values, begin, end, begin + bucket_start, begin + bucket_end);
      @ requires bucket_end - bucket_start < end - begin;
      @ // Small bucket is sorted
      @ requires Sorter.smallBucketIsSorted(values, begin, end, bucket_start, bucket_end);
      @ 
      @ ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
      @ ensures Functions.isSortedSlice(values, begin + bucket_start, begin + bucket_end);
      @ 
      @ assignable values[begin + bucket_start..begin + bucket_end - 1];
      @ assignable storage.*;
      @ 
      @ // calls sample_sort directly => +0
      @ measured_by end - begin, 0;
      @*/
    private static void sample_sort_recurse_on(int[] values, int begin, int end, Storage storage, int bucket_start, int bucket_end) {
        int inner_start = begin + bucket_start;
        int inner_end = begin + bucket_end;

        if (inner_end - inner_start > 2 * Constants.BASE_CASE_SIZE) {
            sample_sort(values, inner_start, inner_end, storage);
        }
    }

    /*@ public normal_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires end - begin > 2 * Constants.BASE_CASE_SIZE;
      @
      @ ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
      @ ensures Functions.isSortedSlice(values, begin, end);
      @
      @ // partition has +1, sample_sort_recurse +0 => +2
      @ measured_by end - begin, 2;
      @ 
      @ assignable values[begin..end - 1];
      @ assignable storage.*;
      @*/
    private static void sample_sort(int[] values, int begin, int end, Storage storage) {
        int[] bucket_starts = new int[Constants.MAX_BUCKETS + 1];

        /*@ normal_behaviour
          @ ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
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
          @ requires (\forall int b; 0 <= b < num_buckets; 
          @     Functions.isValidSubSlice(values, begin, end, begin + bucket_starts[b], begin + bucket_starts[b + 1]) && 
          @     bucket_starts[b + 1] - bucket_starts[b] < end - begin
          @ );
          @ // this is needed in many places and not automatically deduced
          @ requires values != bucket_starts;
          @ 
          @ ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
          @ ensures (\forall int b; 0 <= b < num_buckets; Functions.isSortedSlice(values, begin + bucket_starts[b], begin + bucket_starts[b + 1]));
          @ ensures (\forall int b; 0 <= b < num_buckets; Sorter.isBucketPartitioned(values, begin, end, bucket_starts[b], bucket_starts[b + 1]));
          @ 
          @ assignable values[begin..end - 1];
          @ assignable storage.*;
          @ 
          @ measured_by end - begin, 2;
          @*/
        {
            if (end - begin > Constants.SINGLE_LEVEL_THRESHOLD) {
                if (equal_buckets) {
                    /*@ loop_invariant 0 <= bucket && bucket <= num_buckets;
                      @ loop_invariant bucket % 2 == 0;
                      @ loop_invariant \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
                      @ loop_invariant (\forall int b; 0 <= b < bucket && b < num_buckets - 1; Functions.isSortedSlice(values, begin + bucket_starts[b], begin + bucket_starts[b + 1]));
                      @ // Stays partitioned
                      @ loop_invariant (\forall int b; 0 <= b < num_buckets; Sorter.isBucketPartitioned(values, begin, end, bucket_starts[b], bucket_starts[b + 1]));
                      @ // All subsequent buckets keep the sorting property
                      @ loop_invariant (\forall int b; bucket <= b < num_buckets; Sorter.smallBucketIsSorted(values, begin, end, bucket_starts[b], bucket_starts[b + 1]));
                      @ // Equality buckets at odd indices except the last bucket
                      @ loop_invariant (\forall int b; 0 <= b < num_buckets - 1 && b % 2 == 1;
                      @             (\forall int i; 
                      @                 bucket_starts[b] <= i < bucket_starts[b + 1]; 
                      @                 values[begin + bucket_starts[b]] == values[begin + i]));
                      @ 
                      @ // Keeps equal_buckets in scope for scripting
                      @ loop_invariant equal_buckets;
                      @
                      @ decreases num_buckets - bucket;
                      @
                      @ assignable values[begin..end - 1];
                      @ assignable storage.*;
                      @*/
                    for (int bucket = 0; bucket < num_buckets; bucket += 2) {
                        sample_sort_recurse_on(values, begin, end, storage, bucket_starts[bucket], bucket_starts[bucket + 1]);
                    }

                    sample_sort_recurse_on(values, begin, end, storage, bucket_starts[num_buckets - 1], bucket_starts[num_buckets]);
                } else {
                    /*@ loop_invariant 0 <= bucket && bucket <= num_buckets;
                      @ loop_invariant \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
                      @ loop_invariant bucket < num_buckets ==>
                      @     0 <= bucket_starts[bucket] && 
                      @     bucket_starts[bucket] <= bucket_starts[bucket + 1] && 
                      @     bucket_starts[bucket + 1] <= end - begin;
                      @ // Preceding buckets end before this one
                      @ loop_invariant (\forall int b; 0 <= b < bucket; bucket_starts[b + 1] <= bucket_starts[bucket]);
                      @ // Succeding buckets start after this one
                      @ loop_invariant (\forall int b; bucket + 1 <= b < num_buckets; bucket_starts[bucket + 1] <= bucket_starts[b]);
                      @ 
                      @ loop_invariant (\forall int b; 0 <= b < bucket; Functions.isSortedSlice(values, begin + bucket_starts[b], begin + bucket_starts[b + 1]));
                      @ // Stays partitioned
                      @ loop_invariant (\forall int b; 0 <= b < num_buckets; Sorter.isBucketPartitioned(values, begin, end, bucket_starts[b], bucket_starts[b + 1]));
                      @ // All subsequent buckets keep the sorting property
                      @ loop_invariant (\forall int b; bucket <= b < num_buckets; Sorter.smallBucketIsSorted(values, begin, end, bucket_starts[b], bucket_starts[b + 1]));
                      @ 
                      @ decreases num_buckets - bucket;
                      @
                      @ assignable values[begin..end - 1];
                      @ assignable storage.*;
                      @*/
                    for (int bucket = 0; bucket < num_buckets; bucket += 1) {
                        sample_sort_recurse_on(values, begin, end, storage, bucket_starts[bucket], bucket_starts[bucket + 1]);
                    }
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
      @ ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
      @ ensures Functions.isSortedSlice(values, start, end);
      @
      @ assignable values[start..end - 1];
      @*/
    private static void fallback_sort(int[] values, int start, int end) {
//        java.util.Arrays.sort(values, start, end);
    }

    /*@ public normal_behaviour
      @ requires Functions.isValidSlice(values, start, end);
      @
      @ ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
      @ ensures Functions.isSortedSlice(values, start, end);
      @
      @ assignable values[start..end - 1];
      @*/
    private static void base_case_sort(int[] values, int start, int end) {
        fallback_sort(values, start, end);
    }

    /*@ public normal_behaviour
      @ requires Functions.isValidSlice(values, start, end);
      @
      @ ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
      @ ensures Functions.isSortedSlice(values, start, end);
      @
      @ // sample_sort has +2 => +3
      @ measured_by end - start, 3;
      @ 
      @ assignable values[start..end - 1];
      @ assignable storage.*;
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
        sort(values, 0, values.length, new Storage());
    }
}
