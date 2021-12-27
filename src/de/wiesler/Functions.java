package de.wiesler;

public class Functions {
    /*@
      @ public model_behaviour
      @ requires index >= 1;
      @ static model boolean isAlignedTo(int index, int alignment) {
      @     return index % alignment == 0;
      @ }
      @*/

    /*@
      @ public model_behaviour
      @ requires lower <= upper;
      @ static model boolean isBetweenInclusive(int index, int lower, int upper) {
      @     return lower <= index && index <= upper;
      @ }
      @*/

    /*@
      @ public model_behaviour
      @ requires true;
      @ static model boolean isValidSlice(int[] values, int begin, int end) {
      @     return values != null &&
      @         0 <= begin && begin <= values.length &&
      @         0 <= end && end <= values.length &&
      @         begin <= end;
      @ }
      @*/

    /*@
      @ public model_behaviour
      @ requires isValidSlice(values, begin, end);
      @ static model boolean isSortedSlice(int[] values, int begin, int end) {
      @     return (\forall int i; begin <= i && i < end - 1; values[i] <= values[i + 1]);
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires isValidSlice(values, begin, end);
      @ requires num_samples <= end - begin;
      @
      @ ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
      @
      @ assignable values[begin..end];
      @*/
    public static void select_n(int[] values, int begin, int end, int num_samples) {
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
}
