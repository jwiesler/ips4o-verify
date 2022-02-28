package de.wiesler;

public final class Functions {
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
      @ requires true;
      @ accessible \nothing;
      @ static model boolean isValidSlice(int[] values, int begin, int end) {
      @     return 0 <= begin <= end <= values.length;
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
      @     return 0 <= begin <= sub_begin <= sub_end <= end <= values.length;
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @
      @ accessible values[begin..end - 1];
      @
      @ static model int countElement(int[] values, int begin, int end, int element) {
      @     return (\num_of int i; begin <= i < end; values[i] == element);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= mid <= end <= values.length;
      @
      @ ensures \result;
      @
      @ static model boolean countElementSplit(int[] values, int begin, int mid, int end) {
      @     return (\forall int element; true; countElement(values, begin, end, element) == countElement(values, begin, mid, element) + countElement(values, mid, end, element));
      @ }
      @*/

    /*@
      @ public model_behaviour
      @ requires true;
      @
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
      @ accessible \nothing;
      @
      @ static model boolean isSortedSeqTransitive(\seq values) {
      @     return
      @         (\forall int i; 0 <= i < values.length;
      @             (\forall int j; i <= j < values.length; (int) values[i] <= (int) values[j]));
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
      @         isSortedSliceTransitive(bucket_starts, 0, num_buckets + 1) &&
      @         2 <= num_buckets &&
      @         bucket_starts[0] == 0;
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires isValidSlice(values, begin, end);
      @ requires 1 <= num_samples && num_samples <= end - begin;
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
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
      @ requires \disjoint(src[srcPos..srcPos + length - 1], dest[destPos..destPos + length - 1]);
      @
      @ ensures (\forall int i; 0 <= i && i < length; dest[destPos + i] == src[srcPos + i]);
      @ ensures \dl_seq_def_workaround(destPos, destPos + length, dest) == \dl_seq_def_workaround(srcPos, srcPos + length, src);
      @ ensures (\forall int element; true;
      @     countElement(dest, destPos, destPos + length, element) == countElement(src, srcPos, srcPos + length, element)
      @ );
      @
      @ assignable dest[destPos..destPos + length - 1];
      @*/
    public static void copy_nonoverlapping(int[] src, int srcPos, int[] dest, int destPos, int length) {
        /*@ loop_invariant 0 <= i <= length;
          @ loop_invariant (\forall int j; 0 <= j < i; dest[destPos + j] == src[srcPos + j]);
          @
          @ decreases length - i;
          @
          @ assignable dest[destPos..destPos + length - 1];
          @*/
        for (int i = 0; i < length; ++i) {
            dest[destPos + i] = src[srcPos + i];
        }
        // System.arraycopy(src, srcPos, dest, destPos, length);
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

    /*@ public normal_behaviour
      @ requires Functions.isValidSubSlice(values, begin, end, from, from + Buffers.BUFFER_SIZE);
      @ requires Buffers.isBlockAligned(from - begin);
      @
      @ requires buffer.length == Buffers.BUFFER_SIZE;
      @ requires \disjoint(values[*], buffer[*]);
      @
      @ ensures (\forall int i; 0 <= i && i < Buffers.BUFFER_SIZE; buffer[i] == values[from + i]);
      @
      @ assignable buffer[*];
      @*/
    public static void copy_block_to_buffer(int[] values, int begin, int end, int from, int[] buffer) {
        copy_nonoverlapping(values, from, buffer, 0, Buffers.BUFFER_SIZE);
    }

    /*@ public normal_behaviour
      @ requires Functions.isValidSubSlice(values, begin, end, to, to + Buffers.BUFFER_SIZE);
      @ requires Buffers.isBlockAligned(to - begin);
      @
      @ requires buffer.length == Buffers.BUFFER_SIZE;
      @ requires \disjoint(values[*], buffer[*]);
      @
      @ ensures (\forall int i; 0 <= i && i < Buffers.BUFFER_SIZE; values[to + i] == buffer[i]);
      @
      @ assignable values[to..to + Buffers.BUFFER_SIZE - 1];
      @*/
    public static void copy_block_from_buffer(int[] values, int begin, int end, int[] buffer, int to) {
        copy_nonoverlapping(buffer, 0, values, to, Buffers.BUFFER_SIZE);
    }

    /*@ public normal_behaviour
      @ requires buffer.length == Buffers.BUFFER_SIZE;
      @ requires to.length == Buffers.BUFFER_SIZE;
      @ requires \disjoint(to[*], buffer[*]);
      @
      @ ensures (\forall int i; 0 <= i && i < Buffers.BUFFER_SIZE; buffer[i] == to[i]);
      @
      @ assignable to[*];
      @*/
    public static void copy_buffer_to(int[] buffer, int[] to) {
        copy_nonoverlapping(buffer, 0, to, 0, Buffers.BUFFER_SIZE);
    }

    /*@ public normal_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
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
      @     // It is from the source array
      @     (\exists int j; begin <= j < end; values[j] == target[i]) &&
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
}
