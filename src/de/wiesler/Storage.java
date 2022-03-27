package de.wiesler;

public final class Storage {
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
      @ requires length >= 0;
      @ ensures \result.length == length;
      @ ensures \fresh(\result);
      @ ensures (\forall int i; 0 <= i < length; \result[i] == 0);
      @ assignable \nothing;
      @*/
    static int[] createArray(int length) {
        return new int[length];
    }

    final int[] tree;
    final int[] splitters;
    final int[] bucket_pointers;
    final int[] buffers_buffer;
    final int[] buffers_indices;
    final int[] swap_1;
    final int[] swap_2;
    final int[] overflow;

    //@ ghost final \locset allArrays;

    /*@ public instance invariant this.tree.length == Classifier.STORAGE_SIZE &&
      @     this.splitters.length == Classifier.STORAGE_SIZE &&
      @     this.bucket_pointers.length == 2 * Constants.MAX_BUCKETS &&
      @     this.buffers_buffer.length == 2 * Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS &&
      @     this.buffers_indices.length == Constants.MAX_BUCKETS &&
      @     this.swap_1.length == Buffers.BUFFER_SIZE &&
      @     this.swap_2.length == Buffers.BUFFER_SIZE &&
      @     this.overflow.length == Buffers.BUFFER_SIZE;
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
        this.splitters = createArray(Classifier.STORAGE_SIZE);
        this.tree = createArray(Classifier.STORAGE_SIZE);
        this.bucket_pointers = createArray(2 * Constants.MAX_BUCKETS);
        this.buffers_buffer = createArray(2 * Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS);
        this.buffers_indices = createArray(Constants.MAX_BUCKETS);
        this.swap_1 = createArray(Buffers.BUFFER_SIZE);
        this.swap_2 = createArray(Buffers.BUFFER_SIZE);
        this.overflow = createArray(Buffers.BUFFER_SIZE);

        //@ set this.allArrays = \set_union(\set_union(\set_union(\all_fields(tree), \all_fields(splitters)), \set_union(\all_fields(bucket_pointers), \all_fields(buffers_buffer))), \set_union(\set_union(\all_fields(buffers_indices), \all_fields(swap_1)), \set_union(\all_fields(swap_2), \all_fields(overflow))));
    }
}
