package de.wiesler;

public final class Buffers {
    public static final int BUFFER_SIZE = 1024 / 4;
    public static final int MAX_INT = 0x7FFFFFFF;
    public static final int MAX_LEN = MAX_INT - BUFFER_SIZE + 1;

    /*@ public model_behaviour
      @ requires 0 <= len;
      @
      @ ensures 0 <= \result <= BUFFER_SIZE;
      @
      @ // A remainder modulo BUFFER_SIZE that is never 0 for nonempty buckets
      @ static no_state model int bufferSizeForBucketLen(int len) {
      @     return (len >= Buffers.BUFFER_SIZE && len % Buffers.BUFFER_SIZE == 0) ?
      @         Buffers.BUFFER_SIZE : (len % Buffers.BUFFER_SIZE);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= value <= MAX_LEN;
      @
      @ ensures Buffers.isBlockAligned(\result);
      @ ensures \result >= value;
      @ ensures \result - value < BUFFER_SIZE;
      @
      @ static no_state model int blockAligned(int value) {
      @     return (value + BUFFER_SIZE - 1) & (-BUFFER_SIZE);
      @ }
      @*/

    private static boolean testBlockAlignedContract(int value, int result) {
        return
            result % BUFFER_SIZE == 0 &&
                result >= value &&
                result - value < BUFFER_SIZE;
    }

    /*@ public model_behaviour
      @ requires value >= 0;
      @
      @ static no_state model boolean isBlockAligned(int value) {
      @     return value % BUFFER_SIZE == 0;
      @ }
      @*/

    /*@ public model_behaviour
      @ ensures \result;
      @
      @ static no_state model boolean isBlockAlignedLemma() {
      @     return (\forall int i; 0 <= i && isBlockAligned(i);
      @         (\forall int j; isBlockAligned(j); isBlockAligned(i + j)) &&
      @         (\forall int j; j <= i && isBlockAligned(j); isBlockAligned(i - j))
      @     );
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires 0 <= offset <= MAX_LEN;
      @
      @ ensures \result == blockAligned(offset);
      @
      @ assignable \strictly_nothing;
      @ accessible \nothing;
      @*/
    public static int align_to_next_block(int offset) {
        return (offset + BUFFER_SIZE - 1) & (-BUFFER_SIZE);
    }

    public static void testContracts(int i) {
        if (0 <= i && i <= MAX_LEN && !testBlockAlignedContract(i, align_to_next_block(i))) {
            throw new Error("blockAligned contract fails for " + i);
        }
    }

    private /*@ spec_public @*/ final int[] buffer;
    private /*@ spec_public @*/ final int[] indices;
    //@ ghost final int num_buckets;

    /*@ public model_behaviour
      @ requires true;
      @
      @ ensures \result ==> (\forall int b; 0 <= b < this.num_buckets; this.bufferAt(b) == \seq_empty);
      @ ensures \result ==> this.count() == 0;
      @ model boolean isEmpty() {
      @     return (\forall int b; 0 <= b < this.num_buckets; this.len(b) == 0);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ ensures \result.length <= BUFFER_SIZE;
      @ accessible this.indices[bucket], this.buffer[bucket * BUFFER_SIZE..(bucket + 1) * BUFFER_SIZE - 1];
      @ model \seq bufferAt(int bucket) {
      @     return (\seq_def \bigint i; bucket * BUFFER_SIZE; bucket * BUFFER_SIZE + this.indices[bucket]; this.buffer[i]);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @
      @ accessible this.indices[0..this.num_buckets - 1];
      @ model int count() {
      @     return (\sum int b; 0 <= b < this.num_buckets; this.bufferAt(b).length);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires \invariant_for(classifier);
      @ requires classifier.num_buckets == this.num_buckets;
      @
      @ accessible this.indices[0..this.num_buckets - 1], this.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1], classifier.sorted_splitters[*], classifier.tree.tree[*];
      @ model boolean isClassifiedWith(Classifier classifier) {
      @     return (\forall
      @         int b;
      @         0 <= b < this.num_buckets;
      @         this.isBucketClassifiedWith(b, classifier)
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires classifier.num_buckets == this.num_buckets;
      @ requires 0 <= bucket < this.num_buckets;
      @ requires \invariant_for(classifier);
      @
      @ accessible this.indices[bucket], this.buffer[bucket * BUFFER_SIZE..(bucket + 1) * BUFFER_SIZE - 1], classifier.sorted_splitters[*], classifier.tree.tree[*];
      @ model boolean isBucketClassifiedWith(int bucket, Classifier classifier) {
      @     return (\forall int i; 0 <= i < this.bufferAt(bucket).length; classifier.classOf((int)this.bufferAt(bucket)[i]) == bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @
      @ accessible this.indices[bucket], this.buffer[bucket * BUFFER_SIZE..(bucket + 1) * BUFFER_SIZE - 1];
      @ model int countElementInBucket(int bucket, int element) {
      @     return (\num_of int i; bucket * BUFFER_SIZE <= i < bucket * BUFFER_SIZE + this.indices[bucket]; (int) this.buffer[i] == element);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @
      @ accessible this.indices[0..this.num_buckets - 1], this.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
      @ model int countElement(int element) {
      @     return (\sum int b; 0 <= b < this.num_buckets; this.countElementInBucket(b, element));
      @ }
      @*/

    /*@
      @ invariant this.buffer != this.indices;
      @ invariant this.buffer.length == 2 * Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS;
      @ invariant this.indices.length == Constants.MAX_BUCKETS;
      @ invariant 0 <= this.num_buckets <= Constants.MAX_BUCKETS;
      @ invariant (\forall int b; 0 <= b && b < this.num_buckets; 0 <= this.indices[b] && this.indices[b] <= BUFFER_SIZE);
      @
      @ accessible \inv: this.indices[*];
      @*/

    /*@ public normal_behaviour
      @ requires buffer != indices;
      @ requires buffer.length == 2 * Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS;
      @ requires indices.length == Constants.MAX_BUCKETS;
      @ requires 0 <= num_buckets <= Constants.MAX_BUCKETS;
      @
      @ ensures this.num_buckets == num_buckets;
      @ ensures this.buffer == buffer;
      @ ensures this.indices == indices;
      @ ensures this.isEmpty();
      @
      @ assignable indices[0..num_buckets - 1];
      @*/
    public Buffers(int[] buffer, int[] indices, int num_buckets) {
        this.buffer = buffer;
        this.indices = indices;
        //@ set this.num_buckets = num_buckets;

        Functions.fill(this.indices, 0, num_buckets, 0);
    }

    /*@ public normal_behaviour
      @ requires 0 <= bucket && bucket < this.num_buckets;
      @
      @ requires this.bufferAt(bucket).length != BUFFER_SIZE;
      @
      @ ensures this.bufferAt(bucket) == \seq_concat(\old(this.bufferAt(bucket)), \seq_singleton(value));
      @ ensures (\forall int b; 0 <= b < this.num_buckets && b != bucket; this.bufferAt(b) == \old(this.bufferAt(b)));
      @ ensures this.count() == \old(this.count()) + 1;
      @
      @ ensures (\forall int element; true; this.countElement(element) == \old(this.countElement(element)) + (element == value ? 1 : 0));
      @
      @ assignable this.indices[bucket];
      @ assignable this.buffer[bucket * BUFFER_SIZE..(bucket + 1) * BUFFER_SIZE - 1];
      @*/
    public void push(int bucket, int value) {
        int buffer_offset = bucket * BUFFER_SIZE;
        int index = this.indices[bucket];
        this.buffer[buffer_offset + index] = value;
        this.indices[bucket] = index + 1;
        //@ assert this.bufferAt(bucket) == \seq_concat(\old(this.bufferAt(bucket)), \seq_singleton(value));
        //@ assert (\forall int b; 0 <= b < this.num_buckets && b != bucket; this.bufferAt(b) == \old(this.bufferAt(b)));
        //@ assert (\forall int element; true; this.countElementInBucket(bucket, element) == \old(countElementInBucket(bucket, element)) + (element == value ? 1 : 0));
    }

    /*@ public normal_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ requires \disjoint(values[*], this.buffer[*], this.indices[*]);
      @ requires this.bufferAt(bucket).length == BUFFER_SIZE;
      @ requires Functions.isValidSlice(values, write, end);
      @ requires end - write >= BUFFER_SIZE;
      @
      @ ensures this.bufferAt(bucket) == \seq_empty;
      @ ensures (\forall int i; 0 <= i && i < BUFFER_SIZE; values[write + i] == \old(this.bufferAt(bucket)[i]));
      @ ensures (\forall int element; true;
      @     \old(this.countElement(element)) ==
      @     Functions.countElement(values, write, write + BUFFER_SIZE, element) +
      @         this.countElement(element)
      @ );
      @ ensures (\forall int b; 0 <= b < this.num_buckets && b != bucket; this.bufferAt(b) == \old(this.bufferAt(b)));
      @ ensures this.count() == \old(this.count()) - BUFFER_SIZE;
      @
      @ assignable this.indices[bucket];
      @ assignable values[write..write + BUFFER_SIZE - 1];
      @*/
    public void flush(int bucket, int[] values, int write, int end) {
        int buffer_offset = bucket * BUFFER_SIZE;
        Functions.copy_nonoverlapping(this.buffer, buffer_offset, values, write, BUFFER_SIZE);
        this.indices[bucket] = 0;
        //@ assert this.bufferAt(bucket) == \seq_empty;
        //@ assert (\forall int element; true; \old(this.countElementInBucket(bucket, element)) == Functions.countElement(values, write, write + BUFFER_SIZE, element));
    }

    /*@ public normal_behaviour
      @ requires 0 <= bucket && bucket < this.num_buckets;
      @ requires \disjoint(values[*], this.buffer[*], this.indices[*]);
      @
      @ requires Functions.isValidSlice(values, head_start, head_start + head_len);
      @ requires Functions.isValidSlice(values, tail_start, tail_start + tail_len);
      @
      @ requires head_len + tail_len == this.bufferAt(bucket).length;
      @ // Don't overlap
      @ requires \disjoint(values[head_start..(head_start + head_len - 1)], values[tail_start..(tail_start + tail_len - 1)]);
      @
      @ ensures (\forall int i; 0 <= i && i < head_len; values[head_start + i] == \old(this.bufferAt(bucket)[i]));
      @ ensures (\forall int i; 0 <= i && i < tail_len; values[tail_start + i] == \old(this.bufferAt(bucket)[head_len + i]));
      @
      @ ensures (\forall int element; true;
      @     Functions.countElement(values, head_start, head_start + head_len, element) +
      @         Functions.countElement(values, tail_start, tail_start + tail_len, element) ==
      @     \old(this.countElementInBucket(bucket, element))
      @ );
      @
      @ assignable values[head_start..(head_start + head_len - 1)];
      @ assignable values[tail_start..(tail_start + tail_len - 1)];
      @*/
    public void distribute(int bucket, int[] values, int head_start, int head_len, int tail_start, int tail_len) {
        //@ assert head_len + tail_len == this.indices[bucket];
        int offset = bucket * BUFFER_SIZE;
        //@ assert Functions.countElementSplit(this.buffer, offset, offset + head_len, offset + head_len + tail_len);
        Functions.copy_nonoverlapping(this.buffer, offset, values, head_start, head_len);
        Functions.copy_nonoverlapping(this.buffer, offset + head_len, values, tail_start, tail_len);
    }

    /*@ public normal_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ ensures \result == this.bufferAt(bucket).length;
      @ accessible this.indices[bucket];
      @ assignable \strictly_nothing;
      @*/
    public int len(int bucket) {
        return this.indices[bucket];
    }
}
