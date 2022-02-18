package de.wiesler;

public final class BucketPointers {
    // 2 * n integer (read, write)
    private /*@ spec_public @*/ final int[] buffer;

    //@ ghost final int num_buckets;
    //@ ghost final \seq aligned_bucket_starts;
    //@ ghost final int first_empty_position;

    /*@ model_behaviour
      @ requires true;
      @ static model boolean isBaseInvariantFullfilled(int[] buffer, int[] aligned_bucket_starts, int num_buckets, int first_empty_position) {
      @     return buffer != aligned_bucket_starts &&
      @         Functions.isValidBucketStarts(aligned_bucket_starts, num_buckets) &&
      @         0 <= 2 * num_buckets <= buffer.length &&
      @         0 <= first_empty_position <= aligned_bucket_starts[num_buckets] &&
      @         Functions.isAlignedTo(first_empty_position, Buffers.BUFFER_SIZE);
      @ }
      @*/

    // instance invariant BucketPointers.isBaseInvariantFullfilled(this.buffer, this.aligned_bucket_starts, this.num_buckets, this.first_empty_position);
    //@ instance invariant (\forall int i; 0 <= i && i < this.num_buckets; this.isValidBucketPointerAt(i));
    //@ accessible \inv: this.buffer[*];

    /*@ model_behaviour
      @     requires true;
      @ static model boolean isValidBucketPointer(int read, int write) {
      @     return 0 <= read &&
      @         0 <= write &&
      @         Functions.isAlignedTo(read, Buffers.BUFFER_SIZE) &&
      @         Functions.isAlignedTo(write, Buffers.BUFFER_SIZE);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @
      @ ensures (int) this.aligned_bucket_starts[bucket] <= \result <= (int) this.aligned_bucket_starts[bucket + 1] - Buffers.BUFFER_SIZE;
      @ ensures 0 <= \result <= (int) this.aligned_bucket_starts[this.num_buckets];
      @ ensures Buffers.isBlockAligned(\result);
      @
      @ accessible this.buffer[2 * bucket];
      @ model int lastReadOf(int bucket) {
      @     return this.buffer[2 * bucket];
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @
      @ ensures (int) this.aligned_bucket_starts[bucket] <= \result <= (int) this.aligned_bucket_starts[bucket + 1];
      @ ensures Buffers.isBlockAligned(\result);
      @
      @ accessible this.buffer[2 * bucket + 1];
      @ model int nextWriteOf(int bucket) {
      @     return this.buffer[2 * bucket + 1];
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ ensures \result >= 0;
      @ ensures Buffers.isBlockAligned(\result);
      @
      @ accessible this.buffer[2 * bucket + 1];
      @ model int writtenCountOfBucket(int bucket) {
      @     return this.nextWriteOf(bucket) - (int) this.aligned_bucket_starts[bucket];
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @
      @ ensures \result >= 0;
      @ ensures Buffers.isBlockAligned(\result);
      @
      @ accessible this.buffer[2 * bucket + 1];
      @ model int remainingWriteCountOfBucket(int bucket) {
      @     return (int) this.aligned_bucket_starts[bucket + 1] - this.nextWriteOf(bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @
      @ ensures \result >= 0;
      @ ensures Buffers.isBlockAligned(\result);
      @
      @ accessible this.buffer[2 * bucket], this.buffer[2 * bucket + 1];
      @ model int toReadCountOfBucket(int bucket) {
      @     return this.lastReadOf(bucket) - this.nextWriteOf(bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ ensures \result.length >= 0;
      @ model \seq writtenElementsOfBucket(int values[], int begin, int bucket) {
      @     return \dl_seq_def_workaround(begin + (int) this.aligned_bucket_starts[bucket], begin + this.nextWriteOf(bucket), values);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ ensures \result.length >= 0;
      @ model \seq elementsToReadOfBucket(int values[], int begin, int bucket) {
      @     return \dl_seq_def_workaround(begin + this.nextWriteOf(bucket), begin + this.lastReadOf(bucket), values);
      @ }
      @*/

    /*@ model_behaviour
      @ requires 0 <= bucket && bucket < this.num_buckets;
      @ model boolean isValidBucketPointerAt(int bucket) {
      @     return isValidBucketPointer(this.buffer[2 * bucket], this.buffer[2 * bucket + 1]);
      @ }
      @*/

    /*@ public normal_behaviour
      @ // requires isBaseInvariantFullfilled(buffer, bucket_starts, num_buckets, first_empty_position);
      @
      @ ensures (\forall int i; 0 <= i && i < num_buckets; this.isValidBucketPointerAt(i));
      @
      @ ensures this.num_buckets == num_buckets && this.buffer == buffer;
      @ ensures (\forall int b; 0 <= b < num_buckets; this.writtenCountOfBucket(b) == \seq_empty);
      @
      @ assignable buffer[0..2 * num_buckets - 1];
      @*/
    public BucketPointers(int[] bucket_starts, int num_buckets, int first_empty_position, int[] buffer) {
        this.buffer = buffer;
        //@ set this.num_buckets = num_buckets;
        //@ set this.first_empty_position = first_empty_position;

        /*@ loop_invariant 0 <= bucket && bucket <= this.num_buckets;
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
      @ // requires isBaseInvariantFullfilled(this.buffer, this.aligned_bucket_starts, this.num_buckets, this.first_empty_position);
      @
      @ requires 0 <= bucket < this.num_buckets;
      @ requires 0 <= start <= stop && first_empty_position == this.first_empty_position;
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
        public final boolean occupied;
        public final int position;

        public /*@ strictly_pure @*/ Increment(boolean occupied, int position) {
            this.occupied = occupied;
            this.position = position;
        }
    }

    /*@ public normal_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @
      @ ensures \result == this.nextWriteOf(bucket);
      @
      @ assignable \strictly_nothing;
      @*/
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
    /*@ public normal_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ requires \old(this.toReadCountOfBucket(bucket)) != 0;
      @
      @ ensures 0 <= \result;
      @ ensures \result == this.lastReadOf(bucket);
      @
      @ ensures this.toReadCountOfBucket(bucket) + Buffers.BUFFER_SIZE == \old(this.toReadCountOfBucket(bucket));
      @ ensures \old(this.lastReadOf(bucket)) == this.lastReadOf(bucket) + Buffers.BUFFER_SIZE;
      @ ensures (\forall int b; 0 <= b < this.num_buckets && b != bucket; this.toReadCountOfBucket(b) == \old(this.toReadCountOfBucket(b)));
      @ ensures (\forall int b; 0 <= b < this.num_buckets; this.writtenCountOfBucket(b) == \old(this.writtenCountOfBucket(b)));
      @
      @ assignable this.buffer[2 * bucket];
      @
      @ also
      @*/
    /*@ public normal_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ requires this.toReadCountOfBucket(bucket) == 0;
      @
      @ ensures \result < 0;
      @
      @ assignable \strictly_nothing;
      @*/
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
