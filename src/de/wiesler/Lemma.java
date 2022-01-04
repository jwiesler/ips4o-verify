package de.wiesler;

public class Lemma {
    /*@ public normal_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires Functions.isBetweenInclusive(num_buckets, 1, bucket_starts.length - 1);
      @ requires bucket_starts[0] == 0 && bucket_starts[num_buckets] == end - begin;
      @ requires Functions.isSortedSlice(bucket_starts, 0, num_buckets + 1);
      @ 
      @ // Buckets are partitioned
      @ requires (\forall 
      @     int b; 
      @     0 <= b < num_buckets; 
      @     Sorter.isBucketPartitioned(values, begin, end, bucket_starts[b], bucket_starts[b + 1])
      @ );
      @ // Buckets are sorted
      @ requires (\forall 
      @     int b; 
      @     0 <= b < num_buckets; 
      @     Functions.isSortedSlice(values, begin + bucket_starts[b], begin + bucket_starts[b + 1])
      @ );
      @ 
      @ ensures Functions.isSortedSlice(values, begin, end);
      @ 
      @ assignable \strictly_nothing;
      @*/
    public static void sortedness_from_partition_sorted(int[] values, int begin, int end, int[] bucket_starts, int num_buckets) {
        bucket_index_from_offset(bucket_starts, num_buckets, end - begin);
    }

    /*@ public normal_behaviour
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets);
      @ requires bucket_starts[num_buckets] == len;
      @ 
      @ ensures (\forall int i; 0 <= i < len; (\exists int b; 0 <= b < num_buckets; bucket_starts[b] <= i < bucket_starts[b + 1]));
      @ 
      @ assignable \strictly_nothing;
      @*/
    public static void bucket_index_from_offset(int[] bucket_starts, int num_buckets, int len) {}

    /*@ public model_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires Functions.isBetweenInclusive(num_buckets, 1, bucket_starts.length - 1);
      @ requires bucket_starts[0] == 0 && bucket_starts[num_buckets] == end - begin;
      @ requires Functions.isSortedSlice(bucket_starts, 0, num_buckets + 1);
      @ 
      @ // Buckets are partitioned
      @ requires (\forall 
      @     int b; 
      @     0 <= b < num_buckets; 
      @     Sorter.isBucketPartitioned(values, begin, end, bucket_starts[b], bucket_starts[b + 1])
      @ );
      @ // Buckets are sorted
      @ requires (\forall 
      @     int b; 
      @     0 <= b < num_buckets; 
      @     Functions.isSortedSlice(values, begin + bucket_starts[b], begin + bucket_starts[b + 1])
      @ );
      @ 
      @ requires bucket_index_from_offset_model(bucket_starts, num_buckets, end - begin);
      @ 
      @ ensures Functions.isSortedSlice(values, begin, end);
      @ ensures \result;
      @ 
      @ static model boolean sortedness_from_partition_sorted_model(int[] values, int begin, int end, int[] bucket_starts, int num_buckets) {
      @     return true;
      @ }
      @*/

    /*@ public model_behaviour
      @ requires Functions.isBetweenInclusive(num_buckets, 1, bucket_starts.length - 1);
      @ requires bucket_starts[0] == 0 && bucket_starts[num_buckets] == len;
      @ requires Functions.isSortedSlice(bucket_starts, 0, num_buckets + 1);
      @ 
      @ ensures (\forall int i; 0 <= i < len; (\exists int b; 0 <= b < num_buckets; bucket_starts[b] <= i < bucket_starts[b + 1]));
      @ ensures \result;
      @ 
      @ static model boolean bucket_index_from_offset_model(int[] bucket_starts, int num_buckets, int len) {
      @     return true;
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires Functions.isSortedSlice(values, begin, end);
      @ 
      @ ensures (\forall int i; begin <= i < end; values[begin] <= values[i]);
      @*/
    static void /*@ strictly_pure @*/ ascending_geq_first(int[] values, int begin, int end) {}

    /*@ public normal_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ // all positive
      @ requires (\forall int i; begin <= i < end; values[i] >= 0);
      @ 
      @ // lower bound of the sum is any term
      @ ensures (\forall int i; begin <= i < end; values[i] <= (\sum int i; begin <= i < end; values[i]));
      @*/
    static void /*@ strictly_pure @*/ sum_geq_any_term(int[] values, int begin, int end) {}
}