package de.wiesler;

public final class Buffers {
    public static final int BUFFER_SIZE = 1024 / 4;
    public static final int MAX_INT = 0x7FFFFFFF;
    public static final int MAX_LEN = MAX_INT - BUFFER_SIZE + 1;

    /*@ public model_behaviour
      @ requires 0 <= len;
      @
      @ ensures_free 0 <= \result <= BUFFER_SIZE;
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
      @ // checked by exhaustive search below
      @ ensures_free Buffers.isBlockAligned(\result);
      @ ensures_free \result >= value;
      @ ensures_free \result - value < BUFFER_SIZE;
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
      @ requires 0 <= i;
      @ requires 0 <= j;
      @ requires isBlockAligned(i) && isBlockAligned(j);
      @
      @ ensures_free \result;
      @
      @ static model boolean isBlockAlignedAdd(int i, int j) {
      @     return isBlockAligned(i + j);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= j <= i;
      @ requires isBlockAligned(i) && isBlockAligned(j);
      @
      @ ensures_free \result;
      @
      @ static model boolean isBlockAlignedSub(int i, int j) {
      @     return isBlockAligned(i - j);
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires_free 0 <= offset <= MAX_LEN;
      @
      @ ensures_free \result == blockAligned(offset);
      @
      @ assignable_free \strictly_nothing;
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
      @ ensures_free \result ==> this.count() == 0;
      @ ensures_free \result ==> (\forall int element; true; this.countElement(element) == 0);
      @ model boolean isEmpty() {
      @     return (\forall int b; 0 <= b < this.num_buckets; this.bufferLen(b) == 0);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ ensures_free 0 <= \result <= BUFFER_SIZE;
      @ accessible this.indices[bucket];
      @ model int bufferLen(int bucket) {
      @     return this.indices[bucket];
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @ accessible this.buffer[bucket * BUFFER_SIZE + offset];
      @ model int bufferElement(int bucket, int offset) {
      @     return this.buffer[bucket * BUFFER_SIZE + offset];
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @
      @ accessible this.indices[0..this.num_buckets - 1];
      @ model int count() {
      @     return (\sum int b; 0 <= b < this.num_buckets; this.bufferLen(b));
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
      @         classifier.isClassOfSlice(this.buffer, b * BUFFER_SIZE, b * BUFFER_SIZE + this.bufferLen(b), b)
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @
      @ model int countElementInBucket(int bucket, int element) {
      @     return Functions.countElement(this.buffer, bucket * BUFFER_SIZE, bucket * BUFFER_SIZE + this.bufferLen(bucket), element);
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
      @ invariant_free this.buffer != this.indices;
      @ invariant_free this.buffer.length == Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS;
      @ invariant_free this.indices.length == Constants.MAX_BUCKETS;
      @ invariant_free 0 <= this.num_buckets <= Constants.MAX_BUCKETS;
      @ invariant_free (\forall int b; 0 <= b && b < this.num_buckets; 0 <= this.indices[b] && this.indices[b] <= BUFFER_SIZE);
      @
      @ accessible \inv: this.indices[*];
      @*/

    /*@ public normal_behaviour
      @ requires_free buffer != indices;
      @ requires_free buffer.length == Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS;
      @ requires_free indices.length == Constants.MAX_BUCKETS;
      @ requires_free 0 <= num_buckets <= Constants.MAX_BUCKETS;
      @
      @ ensures_free this.num_buckets == num_buckets;
      @ ensures_free this.buffer == buffer;
      @ ensures_free this.indices == indices;
      @ ensures_free this.isEmpty();
      @
      @ assignable_free indices[0..num_buckets - 1];
      @*/
    public Buffers(int[] buffer, int[] indices, int num_buckets) {
        this.buffer = buffer;
        this.indices = indices;
        //@ set this.num_buckets = num_buckets;

        Functions.fill(this.indices, 0, num_buckets, 0);
    }

    /*@ public normal_behaviour
      @ requires_free 0 <= bucket && bucket < this.num_buckets;
      @
      @ requires_free this.bufferLen(bucket) != BUFFER_SIZE;
      @
      @ ensures_free this.bufferLen(bucket) == \old(this.bufferLen(bucket)) + 1;
      @ ensures_free this.bufferElement(bucket, \old(this.bufferLen(bucket))) == value;
      @ ensures_free this.count() == \old(this.count()) + 1;
      @
      @ ensures_free (\forall int element; true; this.countElement(element) == \old(this.countElement(element)) + (element == value ? 1 : 0));
      @
      @ assignable_free this.indices[bucket];
      @ assignable_free this.buffer[bucket * BUFFER_SIZE + this.bufferLen(bucket)];
      @*/
    public void push(int bucket, int value) {
        /*@ normal_behaviour
          @ assignable \nothing;
          @*/
        {
            value = value;
        }
        int buffer_offset = bucket * BUFFER_SIZE;
        int index = this.indices[bucket];
        this.buffer[buffer_offset + index] = value;
        this.indices[bucket] = index + 1;
        //@ assume Functions.countElementSplit(this.buffer, bucket * BUFFER_SIZE, bucket * BUFFER_SIZE + index, bucket * BUFFER_SIZE + index + 1);
    }

    /*@ public normal_behaviour
      @ requires_free 0 <= bucket < this.num_buckets;
      @ requires_free \disjoint(values[*], this.buffer[*], this.indices[*]);
      @ requires_free this.bufferLen(bucket) == BUFFER_SIZE;
      @ requires_free 0 <= write <= end <= values.length;
      @ requires_free end - write >= BUFFER_SIZE;
      @
      @ ensures_free this.bufferLen(bucket) == 0;
      @ ensures_free (\forall int i; 0 <= i && i < BUFFER_SIZE; values[write + i] == \old(this.buffer[bucket * BUFFER_SIZE + i]));
      @ ensures_free (\forall int element; true;
      @     \old(this.countElement(element)) ==
      @     Functions.countElement(values, write, write + BUFFER_SIZE, element) +
      @         this.countElement(element)
      @ );
      @ ensures_free this.count() == \old(this.count()) - BUFFER_SIZE;
      @
      @ assignable_free this.indices[bucket];
      @ assignable_free values[write..write + BUFFER_SIZE - 1];
      @*/
    public void flush(int bucket, int[] values, int write, int end) {
        int buffer_offset = bucket * BUFFER_SIZE;
        Functions.copy_nonoverlapping(this.buffer, buffer_offset, values, write, BUFFER_SIZE);
        this.indices[bucket] = 0;
        //@ assume (\forall int element; true; \old(this.countElementInBucket(bucket, element)) == Functions.countElement(values, write, write + BUFFER_SIZE, element));
    }

    /*@ public normal_behaviour
      @ requires_free 0 <= bucket && bucket < this.num_buckets;
      @ requires_free \disjoint(values[*], this.buffer[*], this.indices[*]);
      @
      @ requires_free 0 <= head_start <= head_start + head_len <= values.length;
      @ requires_free 0 <= tail_start <= tail_start + tail_len <= values.length;
      @
      @ requires_free head_len + tail_len == this.bufferLen(bucket);
      @ // Don't overlap
      @ requires_free \disjoint(values[head_start..(head_start + head_len - 1)], values[tail_start..(tail_start + tail_len - 1)]);
      @
      @ ensures_free (\forall int i; 0 <= i && i < head_len; values[head_start + i] == \old(this.bufferElement(bucket, i)));
      @ ensures_free (\forall int i; 0 <= i && i < tail_len; values[tail_start + i] == \old(this.bufferElement(bucket, head_len + i)));
      @
      @ ensures_free (\forall int element; true;
      @     Functions.countElement(values, head_start, head_start + head_len, element) +
      @         Functions.countElement(values, tail_start, tail_start + tail_len, element) ==
      @     \old(this.countElementInBucket(bucket, element))
      @ );
      @
      @ assignable_free values[head_start..(head_start + head_len - 1)];
      @ assignable_free values[tail_start..(tail_start + tail_len - 1)];
      @*/
    public void distribute(int bucket, int[] values, int head_start, int head_len, int tail_start, int tail_len) {
        //@ assume head_len + tail_len == this.indices[bucket];
        int offset = bucket * BUFFER_SIZE;
        //@ assume Functions.countElementSplit(this.buffer, offset, offset + head_len, offset + head_len + tail_len);
        Functions.copy_nonoverlapping(this.buffer, offset, values, head_start, head_len);
        Functions.copy_nonoverlapping(this.buffer, offset + head_len, values, tail_start, tail_len);
    }

    /*@ public normal_behaviour
      @ requires_free 0 <= bucket < this.num_buckets;
      @ ensures_free \result == this.bufferLen(bucket);
      @ assignable_free \strictly_nothing;
      @*/
    public int len(int bucket) {
        return this.indices[bucket];
    }
}
