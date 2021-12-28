package de.wiesler;

public class Buffers {
    public static final int BUFFER_SIZE = 1024 / 4;

    /*@ public normal_behaviour
      @ requires offset >= 0;
      @ ensures \result >= offset && Functions.isAlignedTo(\result, BUFFER_SIZE);
      @
      @ assignable \strictly_nothing;
      @*/
    public static int align_to_next_block(int offset) {
        return (offset + BUFFER_SIZE - 1) & (-BUFFER_SIZE);
    }

    private /*@ spec_public @*/ final int[] buffer;
    private /*@ spec_public @*/ final int[] indices;
    //@ ghost int buckets;

    /*@ public model_behaviour
      @ requires true;
      @ model boolean doesNotAlias(int[] array) {
      @     return array != this.buffer && array != this.indices;
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @ model boolean isEmpty() {
      @     return (\forall int b; Functions.isBetween(b, 0, this.buckets); this.indices[b] == 0);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @ model boolean isClassifiedWith(Classifier classifier) {
      @     return (\forall 
      @         int b; 
      @         Functions.isBetween(b, 0, this.buckets);
      @         (\forall int i; Functions.isBetween(i, b * BUFFER_SIZE, b * BUFFER_SIZE + this.indices[b]); classifier.isClassified(this.buffer[i], b))
      @     );
      @ }
      @*/

    /*@
      @ invariant this.buffer != this.indices;
      @ invariant this.buffer.length == 2 * Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS;
      @ invariant this.indices.length == Constants.MAX_BUCKETS;
      @ invariant Functions.isBetweenInclusive(this.buckets, 0, Constants.MAX_BUCKETS);
      @ invariant (\forall int i; 0 <= i && i < this.buckets; 0 <= this.indices[i] && this.indices[i] <= BUFFER_SIZE);
      @*/

    /*@ public normal_behaviour
      @ requires buffer != indices;
      @ requires buffer.length == 2 * Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS;
      @ requires indices.length == Constants.MAX_BUCKETS;
      @ requires Functions.isBetweenInclusive(num_buckets, 0, Constants.MAX_BUCKETS);
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
      @ requires Functions.isValidSlice(values, write, end);
      @ requires this.indices[bucket] == BUFFER_SIZE ==> (end - write >= BUFFER_SIZE);
      @ requires this.doesNotAlias(values);
      @
      @ ensures \result == (\old(this.indices[bucket]) == BUFFER_SIZE);
      @ ensures \result ==>
      @     (\forall int i; 0 <= i && i < BUFFER_SIZE; values[write + i] == \old(this.buffer[bucket * BUFFER_SIZE + i])) &&
      @     this.indices[bucket] == 1 && this.buffer[bucket * BUFFER_SIZE] == value;
      @ ensures !\result ==>
      @     this.indices[bucket] == \old(this.indices[bucket]) + 1 &&
      @     this.buffer[bucket * BUFFER_SIZE + \old(this.indices[bucket])] == value;
      @ // TODO Else values is unchanged?
      @
      @ assignable this.indices[bucket];
      @ assignable this.buffer[bucket * BUFFER_SIZE..(bucket + 1) * BUFFER_SIZE - 1];
      @ assignable values[write..(write + BUFFER_SIZE) - 1];
      @*/
    public boolean push(int value, int bucket, int[] values, int write, int end) {
        int buffer_offset = bucket * BUFFER_SIZE;
        int index = this.indices[bucket];
        boolean written = false;
        if (index == BUFFER_SIZE) {
            assert (write + BUFFER_SIZE <= end);
            Functions.copy(buffer, buffer_offset, values, write, BUFFER_SIZE);
            index = 0;
            written = true;
        }
        this.buffer[buffer_offset + index] = value;
        this.indices[bucket] = index + 1;
        return written;
    }

    /*@ public normal_behaviour
      @ requires 0 <= bucket && bucket < this.buckets;
      @
      @ requires Functions.isValidSlice(values, head_start, head_start + head_len);
      @ requires Functions.isValidSlice(values, tail_start, tail_start + tail_len);
      @
      @ requires head_len + tail_len == this.indices[bucket];
      @ // Don't overlap
      @ requires head_start + head_len <= tail_start;
      @ requires this.doesNotAlias(values);
      @
      @ ensures (\forall int i; 0 <= i && i < head_len; values[head_start + i] == this.buffer[bucket * BUFFER_SIZE + i]);
      @ ensures (\forall int i; 0 <= i && i < tail_len; values[tail_start + i] == this.buffer[bucket * BUFFER_SIZE + head_len + i]);
      @
      @ assignable values[head_start..(head_start + head_len - 1)];
      @ assignable values[tail_start..(tail_start + tail_len - 1)];
      @*/
    public void distribute(int bucket, int[] values, int head_start, int head_len, int tail_start, int tail_len) {
        assert (head_len + tail_len == this.indices[bucket]);
        int offset = bucket * BUFFER_SIZE;
        Functions.copy(this.buffer, offset, values, head_start, head_len);
        Functions.copy(this.buffer, offset + head_len, values, tail_start, tail_len);
    }

    public /*@ strictly_pure */ int len(int bucket) {
        return this.indices[bucket];
    }
}
