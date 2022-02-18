package de.wiesler;

public final class Buffers {
    public static final int BUFFER_SIZE = 1024 / 4;

    /*@ public model_behaviour
      @ requires value >= 0;
      @
      @ ensures \result % BUFFER_SIZE == 0;
      @ ensures \result >= value;
      @ ensures \result - value < BUFFER_SIZE;
      @
      @ accessible \nothing;
      @
      @ static model int blockAligned(int value) {
      @     return align_to_next_block(value);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires value >= 0;
      @
      @ accessible \nothing;
      @
      @ static model boolean isBlockAligned(int value) {
      @     return value % BUFFER_SIZE == 0;
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires offset >= 0;
      @
      @ ensures \result == blockAligned(offset);
      @
      @ assignable \strictly_nothing;
      @ accessible \nothing;
      @*/
    public static int align_to_next_block(int offset) {
        return (offset + BUFFER_SIZE - 1) & (-BUFFER_SIZE);
    }

    /*@ public normal_behaviour
      @ requires offset >= 0;
      @
      @ ensures \result <= offset && Functions.isAlignedTo(\result, BUFFER_SIZE);
      @ ensures offset - \result < BUFFER_SIZE;
      @
      @ assignable \strictly_nothing;
      @ accessible \nothing;
      @*/
    public static int align_to_previous_block(int offset) {
        int aligned_offset = Buffers.align_to_next_block(offset);
        if (offset == aligned_offset) {
            return aligned_offset;
        } else {
            return aligned_offset - Buffers.BUFFER_SIZE;
        }
    }

    private /*@ spec_public @*/ final int[] buffer;
    private /*@ spec_public @*/ final int[] indices;
    //@ ghost final int buckets;

    /*@ public model_behaviour
      @ requires true;
      @
      @ ensures \result ==> (\forall int b; 0 <= b < this.buckets; this.bufferAt(b) == \seq_empty);
      @ ensures \result ==> this.count() == 0;
      @ model boolean isEmpty() {
      @     return (\forall int b; 0 <= b < this.buckets; this.len(b) == 0);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.buckets;
      @ accessible this.indices[bucket], this.buffer[bucket * BUFFER_SIZE..(bucket + 1) * BUFFER_SIZE - 1];
      @ model \seq bufferAt(int bucket) {
      @     return (\seq_def \bigint i; bucket * BUFFER_SIZE; bucket * BUFFER_SIZE + this.indices[bucket]; this.buffer[i]);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @
      @ accessible this.indices[0..this.buckets - 1];
      @ model int count() {
      @     return (\sum int b; 0 <= b < this.buckets; this.bufferAt(b).length);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires \invariant_for(classifier);
      @ requires classifier.num_buckets == this.buckets;
      @
      @ accessible this.indices[0..this.buckets - 1], this.buffer[0..Buffers.BUFFER_SIZE * this.buckets - 1], classifier.footprint;
      @ model boolean isClassifiedWith(Classifier classifier) {
      @     return (\forall
      @         int b;
      @         0 <= b < this.buckets;
      @         this.isBucketClassifiedWith(b, classifier)
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires \invariant_for(classifier);
      @
      @ requires classifier.num_buckets == this.buckets;
      @ requires 0 <= bucket < this.buckets;
      @ accessible this.indices[bucket], this.buffer[bucket * BUFFER_SIZE..(bucket + 1) * BUFFER_SIZE - 1], classifier.footprint;
      @ model boolean isBucketClassifiedWith(int bucket, Classifier classifier) {
      @     return (\forall int i; 0 <= i < this.bufferAt(bucket).length; classifier.classOf((int)this.bufferAt(bucket)[i]) == bucket);
      @ }
      @*/

    /*@
      @ invariant this.buffer != this.indices;
      @ invariant this.buffer.length == 2 * Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS;
      @ invariant this.indices.length == Constants.MAX_BUCKETS;
      @ invariant 0 <= this.buckets <= Constants.MAX_BUCKETS;
      @ invariant (\forall int i; 0 <= i && i < this.buckets; 0 <= this.indices[i] && this.indices[i] <= BUFFER_SIZE);
      @
      @ accessible \inv: this.*, this.indices[*];
      @*/

    /*@ public normal_behaviour
      @ requires buffer != indices;
      @ requires buffer.length == 2 * Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS;
      @ requires indices.length == Constants.MAX_BUCKETS;
      @ requires 0 <= num_buckets <= Constants.MAX_BUCKETS;
      @
      @ ensures this.buckets == num_buckets;
      @ ensures this.buffer == buffer;
      @ ensures this.indices == indices;
      @ ensures this.isEmpty();
      @
      @ assignable indices[0..num_buckets - 1];
      @*/
    public Buffers(int[] buffer, int[] indices, int num_buckets) {
        this.buffer = buffer;
        this.indices = indices;
        //@ set buckets = num_buckets;

        Functions.fill(this.indices, 0, num_buckets, 0);
    }

    /*@ public normal_behaviour
      @ requires 0 <= bucket && bucket < this.buckets;
      @
      @ requires this.bufferAt(bucket).length != BUFFER_SIZE;
      @
      @ ensures this.bufferAt(bucket) == \seq_concat(\old(this.bufferAt(bucket)), \seq_singleton(value));
      @ ensures (\forall int b; 0 <= b < this.buckets && b != bucket; this.bufferAt(b) == \old(this.bufferAt(b)));
      @ ensures this.count() == \old(this.count()) + 1;
      @
      @ assignable this.indices[bucket];
      @ assignable this.buffer[bucket * BUFFER_SIZE..(bucket + 1) * BUFFER_SIZE - 1];
      @*/
    public void push(int bucket, int value) {
        int buffer_offset = bucket * BUFFER_SIZE;
        int index = this.indices[bucket];
        this.buffer[buffer_offset + index] = value;
        this.indices[bucket] = index + 1;
    }

    /*@ public normal_behaviour
      @ requires 0 <= bucket < this.buckets;
      @ requires \disjoint(values[*], this.buffer[*], this.indices[*]);
      @ requires this.bufferAt(bucket).length == BUFFER_SIZE;
      @ requires Functions.isValidSlice(values, write, end);
      @ requires end - write >= BUFFER_SIZE;
      @
      @ ensures this.bufferAt(bucket) == \seq_empty;
      @ ensures (\forall int i; 0 <= i && i < BUFFER_SIZE; values[write + i] == \old(this.bufferAt(bucket)[i]));
      @ ensures (\forall int b; 0 <= b < this.buckets && b != bucket; this.bufferAt(b) == \old(this.bufferAt(b)));
      @ ensures this.count() == \old(this.count()) - BUFFER_SIZE;
      @
      @ assignable this.indices[bucket];
      @ assignable values[write..write + BUFFER_SIZE - 1];
      @*/
    public void flush(int bucket, int[] values, int write, int end) {
        int buffer_offset = bucket * BUFFER_SIZE;
        Functions.copy_nonoverlapping(buffer, buffer_offset, values, write, BUFFER_SIZE);
        this.indices[bucket] = 0;
    }

    /*@ public normal_behaviour
      @ requires 0 <= bucket && bucket < this.buckets;
      @ requires \disjoint(values[*], this.buffer[*], this.indices[*]);
      @
      @ requires Functions.isValidSlice(values, head_start, head_start + head_len);
      @ requires Functions.isValidSlice(values, tail_start, tail_start + tail_len);
      @
      @ requires head_len + tail_len == this.bufferAt(bucket).length;
      @ // Don't overlap
      @ requires head_start + head_len <= tail_start;
      @
      @ ensures (\forall int i; 0 <= i && i < head_len; values[head_start + i] == this.bufferAt(bucket)[i]);
      @ ensures (\forall int i; 0 <= i && i < tail_len; values[tail_start + i] == this.bufferAt(bucket)[head_len + i]);
      @
      @ assignable values[head_start..(head_start + head_len - 1)];
      @ assignable values[tail_start..(tail_start + tail_len - 1)];
      @*/
    public void distribute(int bucket, int[] values, int head_start, int head_len, int tail_start, int tail_len) {
        //@ assert head_len + tail_len == this.indices[bucket];
        int offset = bucket * BUFFER_SIZE;
        Functions.copy_nonoverlapping(this.buffer, offset, values, head_start, head_len);
        Functions.copy_nonoverlapping(this.buffer, offset + head_len, values, tail_start, tail_len);
    }

    /*@ public normal_behaviour
      @ requires 0 <= bucket < this.buckets;
      @ ensures \result == this.bufferAt(bucket).length;
      @ accessible this.indices[bucket];
      @ assignable \strictly_nothing;
      @*/
    public int len(int bucket) {
        return this.indices[bucket];
    }
}
