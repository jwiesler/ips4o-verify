package de.wiesler;

public class Storage {
    public final int[] tree;
    public final int[] splitters;
    public final int[] bucket_starts;
    public int[] swap_1;
    public int[] swap_2;
    public int[] overflow;

    /*@
      @ invariant this.tree.length == Classifier.STORAGE_SIZE;
      @ invariant this.splitters.length == Classifier.STORAGE_SIZE;
      @ invariant this.bucket_starts.length == Constants.MAX_BUCKETS + 1;
      @ invariant this.swap_1.length == Buffers.BUFFER_SIZE;
      @ invariant this.swap_2.length == Buffers.BUFFER_SIZE;
      @ invariant this.overflow.length == Buffers.BUFFER_SIZE;
      @*/

    /*@ public normal_behaviour
      @   ensures true;
      @*/
    Storage() {
        this.splitters = new int[Classifier.STORAGE_SIZE];
        this.tree = new int[Classifier.STORAGE_SIZE];
        this.bucket_starts = new int[Constants.MAX_BUCKETS + 1];
        this.swap_1 = new int[Buffers.BUFFER_SIZE];
        this.swap_2 = new int[Buffers.BUFFER_SIZE];
        this.overflow = new int[Buffers.BUFFER_SIZE];
    }
}
