package de.wiesler;

public class Storage {
    public final int[] tree;
    public final int[] splitters;
    public final int[] bucket_starts;
    public final int[] bucket_pointers;
    public final int[] buffers_buffer;
    public final int[] buffers_indices;
    public final int[] swap_1;
    public final int[] swap_2;
    public final int[] overflow;

    /*@
      @ invariant this.tree.length == Classifier.STORAGE_SIZE;
      @ invariant this.splitters.length == Classifier.STORAGE_SIZE;
      @ invariant this.bucket_starts.length == Constants.MAX_BUCKETS + 1;
      @ invariant this.bucket_pointers.length == 2 * Constants.MAX_BUCKETS;
      @ invariant this.buffers_buffer.length == 2 * Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS;
      @ invariant this.buffers_indices.length == Constants.MAX_BUCKETS;
      @ invariant this.swap_1.length == Buffers.BUFFER_SIZE;
      @ invariant this.swap_2.length == Buffers.BUFFER_SIZE;
      @ invariant this.overflow.length == Buffers.BUFFER_SIZE;
      @*/

    /*@ public normal_behaviour
      @ ensures true;
      @ assignable \nothing;
      @*/
    Storage() {
        this.splitters = new int[Classifier.STORAGE_SIZE];
        this.tree = new int[Classifier.STORAGE_SIZE];
        this.bucket_starts = new int[Constants.MAX_BUCKETS + 1];
        this.bucket_pointers = new int[2 * Constants.MAX_BUCKETS];
        this.buffers_buffer = new int[2 * Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS];
        this.buffers_indices = new int[Constants.MAX_BUCKETS];
        this.swap_1 = new int[Buffers.BUFFER_SIZE];
        this.swap_2 = new int[Buffers.BUFFER_SIZE];
        this.overflow = new int[Buffers.BUFFER_SIZE];
    }
}
