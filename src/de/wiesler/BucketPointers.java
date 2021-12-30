package de.wiesler;

public class BucketPointers {
    // 2 * n integer (read, write)
    private final int[] buffer;

    //@ invariant buffer.length == 2 * Constants.MAX_BUCKETS;
    //@ invariant (\forall int i; 0 <= i && i < this.buffer.length; isValidBucketPointerAt(i));

    // TODO shadow bucket_starts?
    //@ ghost int buckets;

    /*@ public model_behaviour
      @     requires true;
      @ static model boolean isValidBucketPointer(int read, int write) {
      @     return 0 <= read &&
      @         0 <= write &&
      @         Functions.isAlignedTo(read, Buffers.BUFFER_SIZE) &&
      @         Functions.isAlignedTo(write, Buffers.BUFFER_SIZE);
      @ }
      @*/

    /*@ public model_behaviour
      @     requires 0 <= bucket && bucket < this.buckets;
      @ model boolean isValidBucketPointerAt(int bucket) {
      @     return isValidBucketPointer(this.buffer[2 * bucket], this.buffer[2 * bucket + 1]);
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires buffer.length == 2 * Constants.MAX_BUCKETS;
      @ requires buffer != bucket_starts;
      @ requires Functions.isBetweenInclusive(num_buckets, 2, Constants.MAX_BUCKETS);
      @ requires 0 <= first_empty_position && Functions.isAlignedTo(first_empty_position, Buffers.BUFFER_SIZE);
      @ requires bucket_starts.length >= num_buckets + 1;
      @ requires (\forall int i; 1 <= i && i <= num_buckets; bucket_starts[i - 1] <= bucket_starts[i]);
      @
      @ assignable buffer[0..2 * num_buckets - 1];
      @*/
    public BucketPointers(int[] bucket_starts, int num_buckets, int first_empty_position, int[] buffer) {
        this.buffer = buffer;
        //@ set buckets = num_buckets;

        /*@
          @ loop_invariant 0 <= bucket && bucket <= this.buckets;
          @ loop_invariant (\forall int i; 0 <= i && i <= this.buckets; isValidBucketPointerAt(i));
          @
          @ decreases num_buckets - bucket;
          @
          @ assignable this.buffer[0..2 * num_buckets - 1];
          @*/
        for (int bucket = 0; bucket < num_buckets; ++bucket) {
            int start = Buffers.align_to_next_block(bucket_starts[bucket]);
            int stop = Buffers.align_to_next_block(bucket_starts[bucket + 1]);
            this.init(bucket, start, stop, first_empty_position);
        }
    }

    /*@ public normal_behaviour
      @ requires Functions.isBetween(bucket, 0, this.buckets);
      @ requires Functions.isBetweenInclusive(start, 0, stop) && 0 <= first_empty_position;
      @ requires Functions.isAlignedTo(start, Buffers.BUFFER_SIZE);
      @ requires Functions.isAlignedTo(stop, Buffers.BUFFER_SIZE);
      @ requires Functions.isAlignedTo(first_empty_position, Buffers.BUFFER_SIZE);
      @
      @ ensures isValidBucketPointerAt(bucket);
      @
      @ assignable this.buffer[(2 * bucket)..(2 * bucket + 1) - 1];
      @*/
    void init(int bucket, int start, int stop, int first_empty_position) {
        int read;
        if (first_empty_position <= start) {
            read = start;
        } else if (stop <= first_empty_position) {
            read = stop;
        } else {
            read = first_empty_position;
        }

        this.buffer[2 * bucket] = read;
        this.buffer[2 * bucket + 1] = start;
        assert (read >= 0 && start >= 0);
    }

    public static class Increment {
        public boolean occupied;
        public int position;

        public Increment(boolean occupied, int position) {
            this.occupied = occupied;
            this.position = position;
        }
    }

    public int write(int bucket) {
        final int write_pos = 2 * bucket + 1;
        return this.buffer[write_pos];
    }

    public Increment increment_write(int bucket) {
        final int read_pos = 2 * bucket;
        final int write_pos = 2 * bucket + 1;
        final int write = this.buffer[write_pos];
        this.buffer[write_pos] += Buffers.BUFFER_SIZE;
        assert (write >= 0);
        return new Increment(this.buffer[read_pos] > write, write);
    }

    // -1 if None
    public int decrement_read(int bucket) {
        final int read_pos = 2 * bucket;
        final int write_pos = 2 * bucket + 1;
        int read = this.buffer[read_pos];
        final int write = this.buffer[write_pos];
        if (read <= write) {
            return -1;
        } else {
            read -= Buffers.BUFFER_SIZE;
            this.buffer[read_pos] = read;
            return read;
        }
    }
}
