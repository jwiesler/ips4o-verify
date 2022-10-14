package de.wiesler;

public final class Functions {
    /*@ public model_behaviour
      @ accessible values[begin..end - 1];
      @
      @ static model int countElement(int[] values, int begin, int end, int element) {
      @     return (\num_of int i; begin <= i < end; values[i] == element);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires begin <= mid <= end;
      @
      @ ensures \result;
      @
      @ static model boolean countElementSplit(int[] values, int begin, int mid, int end) {
      @     return (\forall int element; true; countElement(values, begin, end, element) == countElement(values, begin, mid, element) + countElement(values, mid, end, element));
      @ }
      @*/

    /*@ public model_behaviour
      @ ensures \result ==> Functions.isSortedSliceTransitive(values, begin, end);
      @
      @ accessible values[begin..end - 1];
      @ static model boolean isSortedSlice(int[] values, int begin, int end) {
      @     return (\forall int i; begin <= i && i < end - 1; values[i] <= values[i + 1]);
      @ }
      @*/

    /*@ public model_behaviour
      @ ensures \result ==> Functions.isSortedSlice(values, begin, end);
      @
      @ accessible values[begin..end - 1];
      @
      @ static model boolean isSortedSliceTransitive(int[] values, int begin, int end) {
      @     return
      @         (\forall int i; begin <= i < end;
      @             (\forall int j; i <= j < end; values[i] <= values[j]));
      @ }
      @*/

    /*@ public model_behaviour
      @ ensures \result;
      @ static model boolean isSortedSeqTransitiveFromSlice(int[] values, int begin, int end) {
      @     return isSortedSliceTransitive(values, begin, end) ==> isSortedSeqTransitive(\dl_seq_def_workaround(begin, end, values));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @ static no_state model boolean isSortedSeqTransitive(\seq values) {
      @     return
      @         (\forall int i; 0 <= i < values.length;
      @             (\forall int j; i <= j < values.length; (int) values[i] <= (int) values[j]));
      @ }
      @*/

    /*@ public model_behaviour
      @ accessible bucket_starts[0..num_buckets];
      @ static model boolean isValidBucketStarts(int[] bucket_starts, int num_buckets) {
      @     return 2 <= num_buckets &&
      @         num_buckets + 1 <= bucket_starts.length &&
      @         isSortedSliceTransitive(bucket_starts, 0, num_buckets + 1) &&
      @         bucket_starts[0] == 0;
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires 1 <= num_samples && num_samples <= end - begin;
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @
      @ assignable values[begin..end - 1];
      @*/
    public static void select_n(int[] values, int begin, int end, int num_samples) {
        for (int i = 0; i < num_samples; ++i) {
            final int sample = java.util.concurrent.ThreadLocalRandom.current().nextInt(begin + i, end);
            final int tmp = values[begin + i];
            values[begin + i] = values[sample];
            values[sample] = tmp;
        }
    }

    /*@ public normal_behaviour
      @ ensures \result == ((a >= b) ? a : b);
      @ assignable \strictly_nothing;
      @*/
    public static int max(int a, int b) {
        return (a >= b) ? a : b;
    }

    /*@ public normal_behaviour
      @ ensures \result == ((a <= b) ? a : b);
      @ assignable \strictly_nothing;
      @*/
    public static int min(int a, int b) {
        return (a <= b) ? a : b;
    }

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @
      @ ensures (\forall int i; begin <= i < end; values[i] == value);
      @
      @ assignable values[begin..end - 1];
      @*/
    public static void fill(int[] values, int begin, int end, int value) {
        /*@ loop_invariant begin <= i <= end;
          @ loop_invariant (\forall int j; begin <= j < i; values[j] == value);
          @ assignable values[begin..end - 1];
          @ decreases end - i;
          @*/
        for (int i = begin; i < end; i++) {
            values[i] = value;
        }
    }

    /*@ public normal_behaviour
      @ requires 0 <= length;
      @ requires 0 <= srcPos && srcPos + length <= src.length;
      @ requires 0 <= destPos && destPos + length <= dest.length;
      @ requires \disjoint(src[srcPos..srcPos + length - 1], dest[destPos..destPos + length - 1]);
      @
      @ ensures (\forall int i; 0 <= i && i < length; dest[destPos + i] == src[srcPos + i]);
      @ // ensures \dl_seq_def_workaround(destPos, destPos + length, dest) == \dl_seq_def_workaround(srcPos, srcPos + length, src);
      @ ensures (\forall int element; true;
      @     countElement(dest, destPos, destPos + length, element) == countElement(src, srcPos, srcPos + length, element)
      @ );
      @
      @ assignable dest[destPos..destPos + length - 1];
      @*/
    public static void copy_nonoverlapping(int[] src, int srcPos, int[] dest, int destPos, int length) {
        // /*@ loop_invariant 0 <= i <= length;
        //   @ loop_invariant (\forall int j; 0 <= j < i; dest[destPos + j] == src[srcPos + j]);
        //   @
        //   @ decreases length - i;
        //   @
        //   @ assignable dest[destPos..destPos + length - 1];
        //   @*/
        // for (int i = 0; i < length; ++i) {
        //     dest[destPos + i] = src[srcPos + i];
        // }
        System.arraycopy(src, srcPos, dest, destPos, length);
    }

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires Functions.isSortedSlice(values, begin, end);
      @ requires \disjoint(target[*], values[*]);
      @
      @ requires target.length >= count;
      @
      @ requires count > 0;
      @ requires step > 0;
      @ requires begin + count * step - 1 < end;
      @
      @ ensures (\forall
      @     int i;
      @     0 <= i < \result;
      @     // It is from the source array
      @     (\exists int j; begin <= j < end; values[j] == target[i])
      @ );
      @ ensures (\forall
      @     int i;
      @     0 <= i < \result;
      @     // It is unique in the target array (or: strictly ascending)
      @     (i < \result - 1 ==> target[i] < target[i + 1])
      @ );
      @ ensures 1 <= \result <= count;
      @
      @ assignable target[0..count - 1];
      @*/
    public static int copy_unique(
            int[] values,
            int begin,
            int end,
            int count,
            int step,
            int[] target
    ) {
        int offset = begin + step - 1;
        //@ assert offset < end;
        target[0] = values[offset];
        int target_offset = 1;
        offset += step;

        /*@
          @ loop_invariant 1 <= i && i <= count;
          @ loop_invariant 1 <= target_offset && target_offset <= i;
          @
          @ loop_invariant begin <= offset;
          @ loop_invariant offset == begin + (step * (i + 1)) - 1;
          @ loop_invariant i < count ==> offset < end;
          @
          @ loop_invariant (\forall
          @     int j;
          @     0 <= j < target_offset;
          @     // It is from the source array
          @     (\exists int k; begin <= k < end; values[k] == target[j])
          @ );
          @ loop_invariant (\forall
          @     int j;
          @     0 <= j < target_offset - 1;
          @     // It is unique in the target array (or: strictly ascending)
          @     target[j] < target[j + 1]
          @ );
          @
          @ decreases count - i;
          @ assignable target[1..count - 1];
          @*/
        for (int i = 1; i < count; ++i) {
            // multiply both sides by step, this can't be proven automatically
            //@ assert i + 2 <= count ==> (i + 2) * step <= count * step;
            if (Constants.cmp(target[target_offset - 1], values[offset])) {
                target[target_offset] = values[offset];
                target_offset += 1;
            }
            offset += step;
        }

        return target_offset;
    }

    /*@ public model_behaviour
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets);
      @ requires 0 <= bucket < num_buckets;
      @
      @ ensures \result;
      @
      @ static model boolean bucketStartsOrdering(int[] bucket_starts, int num_buckets, int bucket) {
      @     return 0 <= bucket_starts[bucket] <= bucket_starts[bucket + 1] <= bucket_starts[num_buckets] &&
      @         (\forall int b; 0 <= b < num_buckets && b != bucket;
      @             (b < bucket ==> 0 <= bucket_starts[b] <= bucket_starts[b + 1] <= bucket_starts[bucket]) &&
      @             (b > bucket ==> bucket_starts[bucket + 1] <= bucket_starts[b] <= bucket_starts[b + 1] <= bucket_starts[num_buckets])
      @         );
      @ }
      @*/
}
