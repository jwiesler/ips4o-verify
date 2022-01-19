package de.wiesler;

public class Functions {
    /*@
      @ public model_behaviour
      @ requires index >= 1;
      @ accessible \nothing;
      @ static model boolean isAlignedTo(int index, int alignment) {
      @     return index % alignment == 0;
      @ }
      @*/

    /*@
      @ public model_behaviour
      @ requires lower <= upper;
      @ accessible \nothing;
      @ static model boolean isBetweenInclusive(int index, int lower, int upper) {
      @     return lower <= index && index <= upper;
      @ }
      @*/

    /*@
      @ public model_behaviour
      @ requires lower <= upper;
      @ accessible \nothing;
      @ static model boolean isBetween(int index, int lower, int upper) {
      @     return lower <= index && index < upper;
      @ }
      @*/

    /*@
      @ public model_behaviour
      @ requires true;
      @ accessible \nothing;
      @ static model boolean isValidSlice(int[] values, int begin, int end) {
      @     return values != null &&
      @         isBetweenInclusive(begin, 0, values.length) &&
      @         isBetweenInclusive(end, 0, values.length) &&
      @         begin <= end;
      @ }
      @*/

    /*@
      @ public model_behaviour
      @ requires isValidSlice(values, begin, end);
      @ 
      @ ensures \result ==> isValidSlice(values, sub_begin, sub_end);
      @ 
      @ accessible \nothing;
      @ static model boolean isValidSubSlice(int[] values, int begin, int end, int sub_begin, int sub_end) {
      @     return isBetweenInclusive(sub_begin, begin, end) &&
      @         isBetweenInclusive(sub_end, begin, end) &&
      @         sub_begin <= sub_end;
      @ }
      @*/

    /*@
      @ public model_behaviour
      @ requires true;
      @ 
      @ ensures \result ==> Lemma.ascendingGeqFirst(values, begin, end);
      @ 
      @ accessible values[begin..end - 1];
      @ static model boolean isSortedSlice(int[] values, int begin, int end) {
      @     return isValidSlice(values, begin, end) && 
      @         (\forall int i; begin <= i && i < end - 1; values[i] <= values[i + 1]);
      @ }
      @*/
    
    /*@ public model_behaviour
      @ requires true;
      @ accessible bucket_starts[0..num_buckets];
      @ 
      @ ensures \result ==> Lemma.bucketIndexFromOffset(bucket_starts, num_buckets, bucket_starts[num_buckets]);
      @ 
      @ static model boolean isValidBucketStarts(int[] bucket_starts, int num_buckets) {
      @     return isValidSlice(bucket_starts, 0, num_buckets + 1) &&
      @         2 <= num_buckets &&
      @         bucket_starts[0] == 0 &&
      @         isSortedSlice(bucket_starts, 0, num_buckets + 1);
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires isValidSlice(values, begin, end);
      @ requires 1 <= num_samples && num_samples <= end - begin;
      @
      @ ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
      @
      @ assignable values[begin..end - 1];
      @*/
    public static void select_n(int[] values, int begin, int end, int num_samples) {}

    /*@ public normal_behaviour
      @ ensures \result == ((a >= b) ? a : b);
      @ accessible \nothing;
      @ assignable \strictly_nothing;
      @*/
    public static int max(int a, int b) {
        return (a >= b) ? a : b;
    }

    /*@ public normal_behaviour
      @ ensures \result == ((a <= b) ? a : b);
      @ accessible \nothing;
      @ assignable \strictly_nothing;
      @*/
    public static int min(int a, int b) {
        return (a <= b) ? a : b;
    }

    /*@ public normal_behaviour
      @ ensures (\forall int i; begin <= i && i < end; values[i] == value);
      @ assignable values[begin..end - 1];
      @*/
    public static void fill(int[] values, int begin, int end, int value) {
        /*@
          @ loop_invariant 0 <= begin && i <= end;
          @ loop_invariant (\forall int j; begin <= j && j < i; values[j] == value);
          @ assignable values[begin..end - 1];
          @ decreases end - begin;
          @*/
        for (int i = begin; i < end; i++) {
            values[i] = value;
        }
    }

    /*@ public normal_behaviour
      @ requires 0 <= length;
      @ requires 0 <= srcPos && srcPos + length <= src.length;
      @ requires 0 <= destPos && destPos + length <= dest.length;
      @
      @ ensures (\forall int i; 0 <= i && i < length; dest[destPos + i] == \old(src[srcPos + i]));
      @
      @ assignable dest[destPos..destPos + length - 1];
      @*/
    public static void copy(int[] src, int srcPos, int[] dest, int destPos, int length) {
        System.arraycopy(src, srcPos, dest, destPos, length);
    }

    public static int isSorted(int[] values, int begin, int end) {
        for (int i = begin + 1; i < end; ++i) {
            if (values[i - 1] > values[i]) {
                return i - 1;
            }
        }
        return -1;
    }

    public static void assertSorted(int[] values, int begin, int end) {
        int inversion = isSorted(values, begin, end);
        if (inversion != -1) {
            System.out.println("Inversion at " + (inversion - begin) + " (" + inversion + " absolute): " + values[inversion] + " > " + values[inversion + 1]);
//            System.out.println(Arrays.toString(Arrays.copyOfRange(values, begin, end)));
            assert (false);
        }
    }

    public static void copy_block_to_buffer(int[] values, int begin, int end, int from, int[] buffer) {
        assert (from + Buffers.BUFFER_SIZE <= end);
        assert ((from - begin) % Buffers.BUFFER_SIZE == 0);
        System.arraycopy(values, from, buffer, 0, Buffers.BUFFER_SIZE);
    }

    public static void copy_block_from_buffer(int[] values, int begin, int end, int[] buffer, int to) {
        assert (to + Buffers.BUFFER_SIZE <= end);
        assert ((to - begin) % Buffers.BUFFER_SIZE == 0);
        assert (buffer.length == Buffers.BUFFER_SIZE);
        System.arraycopy(buffer, 0, values, to, Buffers.BUFFER_SIZE);
    }

    public static void copy_buffer_to(int[] buffer, int[] to) {
        assert (buffer.length == Buffers.BUFFER_SIZE);
        assert (to.length == Buffers.BUFFER_SIZE);
        System.arraycopy(buffer, 0, to, 0, Buffers.BUFFER_SIZE);
    }

    /*@ public normal_behaviour
      @ requires Functions.isSortedSlice(values, begin, end);
      @ requires values != target;
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
      @     // (\exists int j; begin <= j < end; values[j] == target[i]) &&
      @     // It is unique in the target array (or: strictly ascending)
      @     (i > 0 ==> target[i - 1] < target[i])
      @ );
      @ ensures Functions.isBetweenInclusive(\result, 1, count);
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
          @ // loop_invariant (\forall
          @ //     int j;
          @ //     0 <= j < target_offset;
          @ //     // It is from the source array
          @ //     (\exists int k; begin <= k < end; values[k] == target[j])
          @ // );
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
            if (Constants.cmp(target[target_offset - 1], values[offset])) {
                target[target_offset] = values[offset];
                target_offset += 1;
            }
            offset += step;
        }

        return target_offset;
    }
}
