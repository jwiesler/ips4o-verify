package de.wiesler;

public class Storage {
    public static final int VALUES = 0;
    public static final int BUCKET_STARTS = 1;

    public static final int TREE = 2;
    public static final int SPLITTERS = 3;
    public static final int BUCKET_POINTERS = 4;
    public static final int BUFFERS_BUFFER = 5;
    public static final int BUFFERS_INDICES = 6;
    public static final int SWAP_1 = 7;
    public static final int SWAP_2 = 8;
    public static final int OVERFLOW = 9;

    /*@ public normal_behaviour
      @ ensures_free brandOf(array) == type;
      @ accessible \nothing;
      @ assignable \strictly_nothing;
      @*/
    static void brandArray(int[] array, int type) {}

    /*@ public normal_behaviour
      @ requires length >= 0;
      @ ensures brandOf(\result) == type;
      @ ensures \result.length == length;
      @ ensures \fresh(\result);
      @ ensures (\forall int i; 0 <= i < length; \result[i] == 0);
      @ assignable \nothing;
      @*/
    static int[] createBrandedArray(int length, int type) {
        int[] result = new int[length];
        brandArray(result, type);
        return result;
    }

    /*@ public model_behaviour
      @ requires true;
      @ accessible \nothing;
      @ static model int brandOf(int[] array) {
      @     return \dl_A(array);
      @ }
      @*/

    final int[] tree;
    final int[] splitters;
    final int[] bucket_pointers;
    final int[] buffers_buffer;
    final int[] buffers_indices;
    final int[] swap_1;
    final int[] swap_2;
    final int[] overflow;

    //@ ghost \locset allArrays;

    /*@ public instance invariant this.tree.length == Classifier.STORAGE_SIZE &&
      @     this.splitters.length == Classifier.STORAGE_SIZE &&
      @     this.bucket_pointers.length == 2 * Constants.MAX_BUCKETS &&
      @     this.buffers_buffer.length == 2 * Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS &&
      @     this.buffers_indices.length == Constants.MAX_BUCKETS &&
      @     this.swap_1.length == Buffers.BUFFER_SIZE &&
      @     this.swap_2.length == Buffers.BUFFER_SIZE &&
      @     this.overflow.length == Buffers.BUFFER_SIZE;
      @*/

    /*@ public instance invariant brandOf(this.tree) == Storage.TREE &&
      @     brandOf(this.splitters) == Storage.SPLITTERS &&
      @     brandOf(this.bucket_pointers) == Storage.BUCKET_POINTERS &&
      @     brandOf(this.buffers_buffer) == Storage.BUFFERS_BUFFER &&
      @     brandOf(this.buffers_indices) == Storage.BUFFERS_INDICES &&
      @     brandOf(this.swap_1) == Storage.SWAP_1 &&
      @     brandOf(this.swap_2) == Storage.SWAP_2 &&
      @     brandOf(this.overflow) == Storage.OVERFLOW;
      @*/

    /*@ public instance invariant this.allArrays == \set_union(
      @     \set_union(
      @         \set_union(
      @             \all_fields(tree), 
      @             \all_fields(splitters)
      @         ), 
      @         \set_union(
      @             \all_fields(bucket_pointers), 
      @             \all_fields(buffers_buffer)
      @         )
      @     ), 
      @     \set_union(
      @         \set_union(
      @             \all_fields(buffers_indices),
      @             \all_fields(swap_1)
      @         ), 
      @         \set_union(
      @             \all_fields(swap_2),
      @             \all_fields(overflow)
      @         )
      @     )
      @ );
      @*/

    /*@ public instance invariant \disjoint(this.allArrays, \all_fields(this));
      @*/

    //@ accessible \inv: this.*;

    /*@ public normal_behaviour
      @ ensures \fresh(this.allArrays);
      @ assignable \nothing;
      @*/
    Storage() {
        this.splitters = createBrandedArray(Classifier.STORAGE_SIZE, Storage.SPLITTERS);
        this.tree = createBrandedArray(Classifier.STORAGE_SIZE, Storage.TREE);
        this.bucket_pointers = createBrandedArray(2 * Constants.MAX_BUCKETS, Storage.BUCKET_POINTERS);
        this.buffers_buffer = createBrandedArray(2 * Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS, Storage.BUFFERS_BUFFER);
        this.buffers_indices = createBrandedArray(Constants.MAX_BUCKETS, Storage.BUFFERS_INDICES);
        this.swap_1 = createBrandedArray(Buffers.BUFFER_SIZE, Storage.SWAP_1);
        this.swap_2 = createBrandedArray(Buffers.BUFFER_SIZE, Storage.SWAP_2);
        this.overflow = createBrandedArray(Buffers.BUFFER_SIZE, Storage.OVERFLOW);

        //@ set this.allArrays = \set_union(\set_union(\set_union(\all_fields(tree), \all_fields(splitters)), \set_union(\all_fields(bucket_pointers), \all_fields(buffers_buffer))), \set_union(\set_union(\all_fields(buffers_indices), \all_fields(swap_1)), \set_union(\all_fields(swap_2), \all_fields(overflow))));
    }
}
