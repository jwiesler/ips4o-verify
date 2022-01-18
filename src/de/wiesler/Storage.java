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
      @*/
    static void brandArray(int[] array, int type) {}

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

    /*@ public final model \locset allArrays;
      @ represents allArrays =
      @     tree[*],
      @     splitters[*],
      @     bucket_pointers[*],
      @     buffers_buffer[*],
      @     buffers_indices[*],
      @     swap_1[*],
      @     swap_2[*],
      @     overflow[*];
      @ accessible allArrays: tree[*],
      @     splitters[*],
      @     bucket_pointers[*],
      @     buffers_buffer[*],
      @     buffers_indices[*],
      @     swap_1[*],
      @     swap_2[*],
      @     overflow[*];
      @*/

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
    //@ accessible \inv: this.*;

    /*@ public normal_behaviour
      @ ensures true;
      @ assignable \nothing;
      @*/
    Storage() {
        this.tree = new int[Classifier.STORAGE_SIZE];
        this.splitters = new int[Classifier.STORAGE_SIZE];
        this.bucket_pointers = new int[2 * Constants.MAX_BUCKETS];
        this.buffers_buffer = new int[2 * Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS];
        this.buffers_indices = new int[Constants.MAX_BUCKETS];
        this.swap_1 = new int[Buffers.BUFFER_SIZE];
        this.swap_2 = new int[Buffers.BUFFER_SIZE];
        this.overflow = new int[Buffers.BUFFER_SIZE];

        brandArray(this.splitters, Storage.SPLITTERS);
        brandArray(this.tree, Storage.TREE);
        brandArray(this.bucket_pointers, Storage.BUCKET_POINTERS);
        brandArray(this.buffers_buffer, Storage.BUFFERS_BUFFER);
        brandArray(this.buffers_indices, Storage.BUFFERS_INDICES);
        brandArray(this.swap_1, Storage.SWAP_1);
        brandArray(this.swap_2, Storage.SWAP_2);
        brandArray(this.overflow, Storage.OVERFLOW);
    }
}
