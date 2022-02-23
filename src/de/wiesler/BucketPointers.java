package de.wiesler;

public final class BucketPointers {
    // 2 * n integer (read, write)
    private /*@ spec_public @*/ final int[] buffer;

    //@ ghost final int num_buckets;
    //@ ghost final \seq aligned_bucket_starts;
    //@ ghost final int first_empty_position;

    //@ instance invariant 0 <= 2 * this.num_buckets <= this.buffer.length;
    //@ instance invariant 0 <= this.first_empty_position <= (int) this.aligned_bucket_starts[num_buckets] && Buffers.isBlockAligned(this.first_empty_position);
    //@ instance invariant this.aligned_bucket_starts.length == this.num_buckets + 1;
    //@ instance invariant (int) this.aligned_bucket_starts[0] == 0 && Functions.isSortedSeqTransitive(this.aligned_bucket_starts);
    //@ instance invariant (\forall int b; 0 <= b <= this.num_buckets; Buffers.isBlockAligned((int) this.aligned_bucket_starts[b]));
    //@ instance invariant (\forall int b; 0 <= b < this.num_buckets; this.isValidBucketPointer(b));
    //@ accessible \inv: this.buffer[*];

    /*@ model_behaviour
      @     requires true;
      @ model boolean isValidBucketPointer(int bucket) {
      @     return this.bucketStart(bucket) <= this.buffer[2 * bucket] <= this.bucketStart(bucket + 1) &&
      @         this.bucketStart(bucket) <= this.buffer[2 * bucket + 1] <= this.bucketStart(bucket + 1) &&
      @         this.buffer[2 * bucket] <= this.first_empty_position &&
      @         Buffers.isBlockAligned(this.buffer[2 * bucket]) &&
      @         Buffers.isBlockAligned(this.buffer[2 * bucket + 1]);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @
      @ ensures this.bucketStart(bucket) <= \result <= this.first_empty_position;
      @ ensures 0 <= \result <= this.bucketStart(this.num_buckets);
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
      @ ensures this.bucketStart(bucket) <= \result <= this.bucketStart(bucket + 1);
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
      @     return this.nextWriteOf(bucket) - this.bucketStart(bucket);
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
      @     return this.bucketStart(bucket + 1) - this.nextWriteOf(bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @
      @ ensures \result >= 0;
      @ ensures Buffers.isBlockAligned(\result);
      @ ensures \result == (int) this.aligned_bucket_starts[bucket];
      @
      @ accessible \nothing;
      @ model int bucketStart(int bucket) {
      @     return (int) this.aligned_bucket_starts[bucket];
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
      @     return this.lastReadOf(bucket) - this.nextWriteOf(bucket) >= 0 ? this.lastReadOf(bucket) - this.nextWriteOf(bucket) : 0;
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ ensures \result.length >= 0;
      @ model \seq writtenElementsOfBucket(int values[], int begin, int bucket) {
      @     return \dl_seq_def_workaround(begin + this.bucketStart(bucket), begin + this.nextWriteOf(bucket), values);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ ensures \result.length >= 0;
      @ model \seq elementsToReadOfBucket(int values[], int begin, int bucket) {
      @     return \dl_seq_def_workaround(begin + this.nextWriteOf(bucket), begin + this.lastReadOf(bucket), values);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ requires overflow.length == Buffers.BUFFER_SIZE;
      @
      @ accessible values[begin + this.bucketStart(bucket) .. begin + this.nextWriteOf(bucket) - 1], overflow[*], this.buffer[2 * bucket + 1], classifier.footprint;
      @ model boolean writtenElementsOfBucketClassified(Classifier classifier, int[] values, int begin, int end, int[] overflow, int bucket) {
      @     return end < begin + this.nextWriteOf(bucket) && this.writtenCountOfBucket(bucket) >= Buffers.BUFFER_SIZE ?
      @         classifier.isClassOfSlice(values, begin + this.bucketStart(bucket), begin + this.nextWriteOf(bucket) - Buffers.BUFFER_SIZE, bucket) &&
      @             classifier.isClassOfSlice(overflow, 0, Buffers.BUFFER_SIZE, bucket) :
      @         classifier.isClassOfSlice(values, begin + this.bucketStart(bucket), begin + this.nextWriteOf(bucket), bucket);
      @ }
      @*/

    /*@ model_behaviour
      @ requires 0 <= num_buckets <= bucket_starts.length;
      @
      @ static model \seq createAlignedBucketStarts(int[] bucket_starts, int num_buckets) {
      @     return (\seq_def \bigint b; 0; num_buckets + 1; Buffers.blockAligned(bucket_starts[b]));
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets);
      @ requires 0 <= 2 * num_buckets <= buffer.length;
      @ requires 0 <= first_empty_position <= bucket_starts[num_buckets];
      @ requires Buffers.isBlockAligned(first_empty_position);
      @ requires \disjoint(bucket_starts[*], buffer[*]);
      @
      @ ensures this.num_buckets == num_buckets && this.buffer == buffer;
      @ ensures (\forall int b; 0 <= b < num_buckets; this.writtenCountOfBucket(b) == 0);
      @ ensures (\forall int b; 0 <= b < num_buckets; (int) this.aligned_bucket_starts[b] == Buffers.blockAligned(bucket_starts[b]));
      @
      @ assignable buffer[0..2 * num_buckets - 1];
      @*/
    public BucketPointers(final int[] bucket_starts, final int num_buckets, final int first_empty_position, final int[] buffer) {
        this.buffer = buffer;
        //@ set this.num_buckets = num_buckets;
        //@ set this.first_empty_position = first_empty_position;
        // set this.aligned_bucket_starts = createAlignedBucketStarts(bucket_starts, num_buckets);

        /*@ loop_invariant 0 <= bucket && bucket <= num_buckets;
          @ loop_invariant (\forall int b; 0 <= b < bucket; this.isValidBucketPointer(b));
          @
          @ decreases num_buckets - bucket;
          @
          @ assignable this.buffer[0..2 * num_buckets - 1];
          @*/
        for (int bucket = 0; bucket < num_buckets; ++bucket) {
            int start = Buffers.align_to_next_block(bucket_starts[bucket]);
            int stop = Buffers.align_to_next_block(bucket_starts[bucket + 1]);
            //@ assert start == this.bucketStart(bucket) && stop == this.bucketStart(bucket + 1);
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
        }
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
      @ ensures \result == this.writtenCountOfBucket(bucket) + this.bucketStart(bucket);
      @
      @ assignable \strictly_nothing;
      @*/
    public int write(int bucket) {
        final int write_pos = 2 * bucket + 1;
        return this.buffer[write_pos];
    }

    /*@ public normal_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ requires this.remainingWriteCountOfBucket(bucket) > 0;
      @
      @ ensures \old(this.nextWriteOf(bucket)) + Buffers.BUFFER_SIZE == this.nextWriteOf(bucket);
      @ ensures \old(this.remainingWriteCountOfBucket(bucket)) == this.remainingWriteCountOfBucket(bucket) + Buffers.BUFFER_SIZE;
      @
      @ ensures \result.position == \old(this.nextWriteOf(bucket));
      @ ensures \result.occupied <==> \old(this.toReadCountOfBucket(bucket)) > 0;
      @
      @ assignable \strictly_nothing;
      @*/
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
      @ requires this.toReadCountOfBucket(bucket) != 0;
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
