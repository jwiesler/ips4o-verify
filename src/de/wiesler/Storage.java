package de.wiesler;

public final class Storage<T> {
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

    final T[] tree;
    final T[] splitters;
    final int[] bucket_pointers;
    final T[] buffers_buffer;
    final int[] buffers_indices;
    final T[] swap_1;
    final T[] swap_2;
    final T[] overflow;

    //@ ghost final \locset allArrays;

    /*@ public instance invariant this.tree.length == Classifier.STORAGE_SIZE &&
      @     this.splitters.length == Classifier.STORAGE_SIZE &&
      @     this.bucket_pointers.length == 2 * Constants.MAX_BUCKETS &&
      @     this.buffers_buffer.length == Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS &&
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

    /*@ public instance invariant \disjoint(
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
      @ ensures \fresh(this.allArrays);
      @ assignable \nothing;
      @*/
    Storage() {
        this.splitters = new T[Classifier.STORAGE_SIZE];
        this.tree = new T[Classifier.STORAGE_SIZE];
        this.bucket_pointers = createArray(2 * Constants.MAX_BUCKETS);
        this.buffers_buffer = new T[Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS];
        this.buffers_indices = createArray(Constants.MAX_BUCKETS);
        this.swap_1 = new T[Buffers.BUFFER_SIZE];
        this.swap_2 = new T[Buffers.BUFFER_SIZE];
        this.overflow = new T[Buffers.BUFFER_SIZE];

        //@ set this.allArrays = \set_union(\set_union(\set_union(\all_fields(tree), \all_fields(splitters)), \set_union(\all_fields(bucket_pointers), \all_fields(buffers_buffer))), \set_union(\set_union(\all_fields(buffers_indices), \all_fields(swap_1)), \set_union(\all_fields(swap_2), \all_fields(overflow))));
    }
}
