package de.wiesler;

public class Lemma {
    /*@ public model_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets);
      @ requires bucket_starts[num_buckets] == end - begin;
      @ 
      @ // Buckets are partitioned
      @ requires (\forall 
      @     int b; 
      @     0 <= b < num_buckets; 
      @     Sorter.isBucketPartitioned(values, begin, end, bucket_starts[b], bucket_starts[b + 1])
      @ );
      @ 
      @ // Buckets are sorted
      @ requires (\forall 
      @     int b; 
      @     0 <= b < num_buckets; 
      @     Functions.isSortedSlice(values, begin + bucket_starts[b], begin + bucket_starts[b + 1])
      @ );
      @ 
      @ requires Lemma.bucketIndexFromOffset(bucket_starts, num_buckets, end - begin);
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
      @ 
      @ accessible bucket_starts[0..num_buckets];
      @ 
      @ static model boolean bucketIndexFromOffset(int[] bucket_starts, int num_buckets, int len) {
      @     return (\forall int i; 0 <= i < len; (\exists int b; 0 <= b < num_buckets; bucket_starts[b] <= i < bucket_starts[b + 1]));
      @ }
      @*/

    /*@ public model_behaviour
      @ // Sorted
      @ requires Functions.isSortedSlice(values, begin, end);
      @ 
      @ ensures \result;
      @ 
      @ accessible values[begin..end - 1];
      @ 
      @ static model boolean ascendingGeqFirst(int[] values, int begin, int end) {
      @     return (\forall int i; begin <= i < end; values[begin] <= values[i]);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ // all positive
      @ requires (\forall int i; begin <= i < end; values[i] >= 0);
      @ 
      @ ensures \result;
      @ 
      @ static model boolean sumGeqAnyTerm(int[] values, int begin, int end) {
      @     // lower bound of the sum is any term
      @     return (\forall int i; begin <= i < end; values[i] <= (\sum int i; begin <= i < end; values[i]));
      @ }
      @*/
}