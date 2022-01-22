package de.wiesler;

public class BucketPointers {
    // 2 * n integer (read, write)
    private final int[] buffer;

    //@ ghost int num_buckets;
    //@ ghost int bucket_starts[];
    //@ ghost int first_empty_position;

    /*@ model_behaviour
      @ requires true;
      @ static model boolean isBaseInvariantFullfilled(int[] buffer, int[] bucket_starts, int num_buckets, int first_empty_position) {
      @     return buffer != bucket_starts &&
      @         Functions.isValidBucketStarts(bucket_starts, num_buckets) &&
      @         Functions.isBetweenInclusive(2 * num_buckets, 0, buffer.length) &&
      @         Functions.isBetweenInclusive(first_empty_position, 0, bucket_starts[num_buckets]) &&
      @         Functions.isAlignedTo(first_empty_position, Buffers.BUFFER_SIZE);
      @ }
      @*/

    //@ instance invariant BucketPointers.isBaseInvariantFullfilled(this.buffer, this.bucket_starts, this.num_buckets, this.first_empty_position);
    //@ invariant (\forall int i; 0 <= i && i < this.num_buckets; this.isValidBucketPointerAt(i));

    /*@ model_behaviour
      @     requires true;
      @ static model boolean isValidBucketPointer(int read, int write) {
      @     return 0 <= read &&
      @         0 <= write &&
      @         Functions.isAlignedTo(read, Buffers.BUFFER_SIZE) &&
      @         Functions.isAlignedTo(write, Buffers.BUFFER_SIZE);
      @ }
      @*/

    /*@ model_behaviour
      @     requires 0 <= bucket && bucket < this.num_buckets;
      @ model boolean isValidBucketPointerAt(int bucket) {
      @     return isValidBucketPointer(this.buffer[2 * bucket], this.buffer[2 * bucket + 1]);
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires isBaseInvariantFullfilled(buffer, bucket_starts, num_buckets, first_empty_position);
      @
      @ ensures (\forall int i; 0 <= i && i < num_buckets; this.isValidBucketPointerAt(i));
      @ assignable buffer[0..2 * num_buckets - 1];
      @*/
    public BucketPointers(int[] bucket_starts, int num_buckets, int first_empty_position, int[] buffer) {
        this.buffer = buffer;
        //@ ghost BucketPointers self = this;
        //@ set self.num_buckets = num_buckets;
        //@ set self.bucket_starts = bucket_starts;
        //@ set self.first_empty_position = first_empty_position;

        //@ assert Lemma.isSortedSliceTransitive(bucket_starts, 0, num_buckets + 1);

        /*@
          @ loop_invariant 0 <= bucket && bucket <= this.num_buckets;
          @ loop_invariant (\forall int i; 0 <= i && i < bucket; this.isValidBucketPointerAt(i));
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

    /*@ normal_behaviour
      @ requires isBaseInvariantFullfilled(this.buffer, this.bucket_starts, this.num_buckets, this.first_empty_position);
      @ 
      @ requires Functions.isBetween(bucket, 0, this.num_buckets);
      @ requires Functions.isBetweenInclusive(start, 0, stop) && first_empty_position == this.first_empty_position;
      @ requires Functions.isAlignedTo(start, Buffers.BUFFER_SIZE);
      @ requires Functions.isAlignedTo(stop, Buffers.BUFFER_SIZE);
      @
      @ ensures this.isValidBucketPointerAt(bucket);
      @
      @ assignable this.buffer[(2 * bucket)..(2 * bucket + 1)];
      @*/
    /*@ helper @*/ void init(int bucket, int start, int stop, int first_empty_position) {
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

        public /*@ strictly_pure @*/ Increment(boolean occupied, int position) {
            this.occupied = occupied;
            this.position = position;
        }
    }

    public /*@ strictly_pure @*/ int write(int bucket) {
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
