package de.wiesler;

public final class Storage {
    /*@ public normal_behaviour
      @ requires_free length >= 0;
      @ ensures_free \result.length == length;
      @ ensures_free \fresh(\result);
      @ ensures_free (\forall int i; 0 <= i < length; \result[i] == 0);
      @ assignable_free \nothing;
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

    /*@ public instance invariant_free this.tree.length == Classifier.STORAGE_SIZE &&
      @     this.splitters.length == Classifier.STORAGE_SIZE &&
      @     this.bucket_pointers.length == 2 * Constants.MAX_BUCKETS &&
      @     this.buffers_buffer.length == Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS &&
      @     this.buffers_indices.length == Constants.MAX_BUCKETS &&
      @     this.swap_1.length == Buffers.BUFFER_SIZE &&
      @     this.swap_2.length == Buffers.BUFFER_SIZE &&
      @     this.overflow.length == Buffers.BUFFER_SIZE;
      @*/

    /*@ public instance invariant_free this.allArrays == \set_union(
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

    /*@ public instance invariant_free \disjoint(
      @     \all_fields(tree),
      @     \all_fields(splitters),
      @     \all_fields(bucket_pointers),
      @     \all_fields(buffers_buffer),
      @     \all_fields(buffers_indices),
      @     \all_fields(swap_1),
      @     \all_fields(swap_2),
      @     \all_fields(overflow)
      @ );
      @*/

    //@ accessible \inv: this.*;

    /*@ public normal_behaviour
      @ ensures_free \fresh(this.allArrays);
      @ assignable_free \nothing;
      @*/
    public Storage() {
        this.splitters = createArray(Classifier.STORAGE_SIZE);
        this.tree = createArray(Classifier.STORAGE_SIZE);
        this.bucket_pointers = createArray(2 * Constants.MAX_BUCKETS);
        this.buffers_buffer = createArray(Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS);
        this.buffers_indices = createArray(Constants.MAX_BUCKETS);
        this.swap_1 = createArray(Buffers.BUFFER_SIZE);
        this.swap_2 = createArray(Buffers.BUFFER_SIZE);
        this.overflow = createArray(Buffers.BUFFER_SIZE);

        //@ set this.allArrays = \set_union(\set_union(\set_union(\all_fields(tree), \all_fields(splitters)), \set_union(\all_fields(bucket_pointers), \all_fields(buffers_buffer))), \set_union(\set_union(\all_fields(buffers_indices), \all_fields(swap_1)), \set_union(\all_fields(swap_2), \all_fields(overflow))));
    }
}
