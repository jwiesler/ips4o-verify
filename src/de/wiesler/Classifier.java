package de.wiesler;

public final class Classifier {
    public static final int STORAGE_SIZE = (1 << Constants.LOG_MAX_BUCKETS);

    private /*@ spec_public @*/ final Tree tree;
    private /*@ spec_public @*/ final int num_buckets;
    private /*@ spec_public @*/ final int[] sorted_splitters;
    private /*@ spec_public @*/ final boolean equal_buckets;

    /*@ invariant_free 2 <= this.num_buckets <= Constants.MAX_BUCKETS;
      @ invariant_free this.num_buckets == (this.equal_buckets ? 2 * this.tree.num_buckets : this.tree.num_buckets);
      @ invariant_free this.tree.sorted_splitters == this.sorted_splitters;
      @ invariant_free Functions.isSortedSliceTransitive(this.sorted_splitters, 0, this.tree.num_buckets);
      @ invariant_free this.sorted_splitters[this.tree.num_buckets - 1] == this.sorted_splitters[this.tree.num_buckets - 2];
      @ invariant_free \invariant_for(this.tree);
      @
      @ accessible \inv: this.sorted_splitters[*], this.tree.tree[*];
      @*/

    // This is a wrapper around classify not to be expanded in partition.
    /*@ public model_behaviour
      @ ensures_free 0 <= \result < this.num_buckets;
      @ ensures_free this.isClassifiedAs(value, \result);
      @ accessible this.sorted_splitters[*], this.tree.tree[*];
      @ model int classOf(int value) {
      @     return this.classify(value);
      @ }
      @*/

    /*@ public model_behaviour
      @ accessible this.sorted_splitters[*], this.tree.tree[*], values[begin..end - 1];
      @ model boolean isClassOfSlice(int[] values, int begin, int end, int bucket) {
      @     return (\forall
      @              int i;
      @              begin <= i < end;
      @              this.classOf(values[i]) == bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires begin <= mid <= end;
      @
      @ ensures_free \result;
      @
      @ // Verified
      @ model boolean isClassOfSliceSplit(int[] values, int begin, int mid, int end, int bucket) {
      @     return this.isClassOfSlice(values, begin, end, bucket) <==>
      @         this.isClassOfSlice(values, begin, mid, bucket) && this.isClassOfSlice(values, mid, end, bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires this.isClassOfSlice(src, srcPos, srcPos + length, bucket);
      @ requires (\forall int i; 0 <= i && i < length; dest[destPos + i] == src[srcPos + i]);
      @
      @ ensures_free \result;
      @
      @ // Verified
      @ model boolean isClassOfSliceCopy(int[] src, int srcPos, int[] dest, int destPos, int length, int bucket) {
      @     return this.isClassOfSlice(dest, destPos, destPos + length, bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ accessible values[begin..end - 1], this.sorted_splitters[*], this.tree.tree[*];
      @ model int countClassOfSliceEq(int[] values, int begin, int end, int bucket) {
      @     return (\num_of
      @              int i;
      @              begin <= i < end;
      @              this.classOf(values[i]) == bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires this.isClassOfSlice(values, begin, end, bucket);
      @ requires begin <= end;
      @
      @ ensures_free \result;
      @
      @ model boolean countClassOfSliceEqLemma(int[] values, int begin, int end, int bucket) {
      @     return (\forall int b; 0 <= b < this.num_buckets;
      @         this.countClassOfSliceEq(values, begin, end, b) ==
      @             (b == bucket ? end - begin : 0)
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ accessible this.sorted_splitters[*], this.tree.tree[*], values[begin..end - 1];
      @ model boolean isClassifiedBlock(int[] values, int begin, int end) {
      @     return (\exists int bucket; 0 <= bucket < this.num_buckets; this.isClassOfSlice(values, begin, end, bucket));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires this.isClassifiedBlock(values, begin, end);
      @ requires this.classOf(values[begin]) == bucket;
      @
      @ ensures_free \result;
      @
      @ model boolean classOfClassifiedBlockFromFirst(int[] values, int begin, int end, int bucket) {
      @     return this.isClassOfSlice(values, begin, end, bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires Buffers.isBlockAligned(end - begin);
      @ accessible this.sorted_splitters[*], this.tree.tree[*], values[begin..end - 1];
      @ model boolean isClassifiedBlocksRange(int[] values, int begin, int end) {
      @     return (\forall
      @         int block;
      @         0 <= block && block < (end - begin) / Buffers.BUFFER_SIZE;
      @         this.isClassifiedBlock(values, begin + block * Buffers.BUFFER_SIZE, begin + (block + 1) * Buffers.BUFFER_SIZE)
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires begin <= mid <= end;
      @ requires Buffers.isBlockAligned(end - begin);
      @ requires Buffers.isBlockAligned(mid - begin);
      @
      @ ensures_free \result;
      @
      @ model boolean isClassifiedBlocksRangeSplit(int[] values, int begin, int mid, int end) {
      @     return this.isClassifiedBlocksRange(values, begin, end) <==>
      @         this.isClassifiedBlocksRange(values, begin, mid) && this.isClassifiedBlocksRange(values, mid, end);
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires_free tree != sorted_splitters;
      @ requires_free 1 <= log_buckets <= Constants.LOG_MAX_BUCKETS;
      @ requires_free 0 <= (1 << log_buckets) <= sorted_splitters.length;
      @ requires_free Functions.isSortedSliceTransitive(sorted_splitters, 0, 1 << log_buckets);
      @ requires_free (1 << log_buckets) <= tree.length;
      @ requires_free sorted_splitters[(1 << log_buckets) - 1] == sorted_splitters[(1 << log_buckets) - 2];
      @
      @ ensures_free this.tree.tree == tree && this.sorted_splitters == sorted_splitters;
      @ ensures_free this.tree.log_buckets == log_buckets && this.equal_buckets == equal_buckets && this.num_buckets == (equal_buckets ? 2 * (1 << log_buckets) : (1 << log_buckets));
      @
      @ assignable_free tree[*];
      @*/
    public Classifier(int[] sorted_splitters, int[] tree, int log_buckets, boolean equal_buckets) {
        int num_buckets = 1 << log_buckets;
        //@ assume 2 <= num_buckets <= (1 << Constants.LOG_MAX_BUCKETS);

        int num_splitters = num_buckets - 1;
        //@ assume (sorted_splitters[num_splitters] == sorted_splitters[num_splitters - 1]);

        this.tree = new Tree(sorted_splitters, tree, log_buckets);
        //@ assume this.tree.log_buckets == log_buckets;
        //@ assume sorted_splitters[num_splitters] == sorted_splitters[num_splitters - 1];
        this.sorted_splitters = sorted_splitters;
        /*@ normal_behaviour
          @ ensures_free this.num_buckets == (equal_buckets ? 2 * num_buckets : num_buckets);
          @ assignable_free this.num_buckets;
          @*/
        {
            this.num_buckets = equal_buckets ? 2 * num_buckets : num_buckets;
        }
        this.equal_buckets = equal_buckets;
    }

    /*@ public model_behaviour
      @ requires this.tree.classOfFirstSplitters();
      @ ensures_free \result;
      @
      @ model boolean classOfFirstSplitters() {
      @     return this.classOf(this.sorted_splitters[0]) != this.classOf(this.sorted_splitters[1]);
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires_free 0 <= num_splitters <= splitters.length;
      @ requires_free (\forall
      @     int j;
      @     0 <= j < num_splitters - 1;
      @     splitters[j] < splitters[j + 1]
      @ );
      @ requires_free \disjoint(splitters[*], tree[*]);
      @
      @ requires_free 2 <= num_splitters && num_splitters <= num_buckets - 1;
      @ requires_free 2 <= num_buckets && num_buckets <= (1 << Constants.LOG_MAX_BUCKETS);
      @ requires_free splitters.length == Classifier.STORAGE_SIZE;
      @ requires_free tree.length == Classifier.STORAGE_SIZE;
      @
      @ ensures_free \fresh(\result);
      @ ensures_free \invariant_free_for(\result);
      @ ensures \invariant_for(\result);
      @ ensures_free \result.sorted_splitters == splitters && \result.tree.tree == tree;
      @ ensures_free \result.num_buckets % 2 == 0;
      @ ensures_free splitters[0] == \old(splitters[0]) && splitters[1] == \old(splitters[1]);
      @ ensures_free \result.classOf(splitters[0]) != \result.classOf(splitters[1]);
      @
      @ assignable_free splitters[*], tree[*];
      @*/
    public static Classifier from_sorted_samples(
            int[] splitters,
            int[] tree,
            int num_splitters,
            int num_buckets
    ) {
        // Check for duplicate splitters
        boolean use_equal_buckets = (num_buckets - 1 - num_splitters) >= Constants.EQUAL_BUCKETS_THRESHOLD;

        // Fill the array to the next power of two
        int log_buckets = Constants.log2(num_splitters) + 1;
        // Cut for result >= Constants.LOG_MAX_BUCKETS, lower bound
        //@ assume log_buckets <= Constants.LOG_MAX_BUCKETS;
        int actual_num_buckets = 1 << log_buckets;
        //@ assume actual_num_buckets <= splitters.length && num_splitters < actual_num_buckets;

        /*@ loop_invariant_free num_splitters <= i && i <= actual_num_buckets;
          @
          @ loop_invariant_free (\forall
          @     int j;
          @     0 <= j < num_splitters;
          @     // It is unchanged
          @     splitters[j] == \old(splitters[j])
          @ );
          @ loop_invariant_free (\forall int j; num_splitters <= j < i; splitters[j] == splitters[num_splitters - 1]);
          @ loop_invariant_free 0 <= i <= splitters.length;
          @ loop_invariant_free Functions.isSortedSlice(splitters, 0, i);
          @
          @ decreases actual_num_buckets - i;
          @ assignable_free splitters[num_splitters..actual_num_buckets - 1];
          @*/
        for (int i = num_splitters; i < actual_num_buckets; ++i) {
            splitters[i] = splitters[num_splitters - 1];
        }

        Classifier classifier = new Classifier(splitters, tree, log_buckets, use_equal_buckets);
        //@ assume classifier.classOfFirstSplitters();
        return classifier;
    }

    /*@ public normal_behaviour
      @ ensures_free \result == this.num_buckets;
      @ assignable_free \strictly_nothing;
      @*/
    public int num_buckets() {
        return this.num_buckets;
    }

    /*@ public normal_behaviour
      @ ensures_free \result == this.equal_buckets;
      @ assignable_free \strictly_nothing;
      @*/
    public boolean equal_buckets() {
        return this.equal_buckets;
    }

    /*@ public model_behaviour
      @ requires true;
      @
      @ model boolean isClassifiedAs(int value, int bucket) {
      @     return this.equal_buckets ?
      @         ((bucket % 2 == 0 || bucket == this.num_buckets - 1) ?
      @             ((0 < bucket ==> this.sorted_splitters[bucket / 2 - 1] < value) &&
      @             (bucket < this.num_buckets - 1 ==> value < this.sorted_splitters[bucket / 2])) :
      @             (this.sorted_splitters[bucket / 2] == value &&
      @             // elements land in equality buckets iff the non equality bucket actually allows elements
      @             (0 < bucket / 2 ==> this.sorted_splitters[bucket / 2 - 1] < value))) :
      @         ((0 < bucket ==> this.sorted_splitters[bucket - 1] < value) &&
      @             (bucket < this.num_buckets - 1 ==> value <= this.sorted_splitters[bucket]));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @
      @ ensures_free \result;
      @
      @ model boolean classOfTrans() {
      @     return (\forall int i, j, classI, classJ; 0 <= classI < classJ < this.num_buckets;
      @         this.isClassifiedAs(i, classI) && this.isClassifiedAs(j, classJ) ==> i < j
      @     );
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires_free \dl_inInt(value);
      @ ensures_free 0 <= \result < this.num_buckets;
      @ ensures_free this.isClassifiedAs(value, \result);
      @
      @ // Needed to bring this method to logic
      @ ensures_free \result == this.classify(value);
      @
      @ assignable_free \strictly_nothing;
      @
      @ accessible this.sorted_splitters[*], this.tree.tree[*];
      @*/
    public int classify(int value) {
        /*@ normal_behaviour
          @ assignable \nothing;
          @*/
        {
            value = value;
        }
        int index = this.tree.classify(value);
        int bucket;
        if (this.equal_buckets) {
            int bucket_index = index - this.num_buckets / 2;
            boolean equal_to_splitter = !Constants.cmp(value, this.sorted_splitters[bucket_index]);
            bucket = 2 * index + Constants.toInt(equal_to_splitter) - this.num_buckets;
        } else {
            bucket = index - this.num_buckets;
        }
        return bucket;
    }

    /*@ public normal_behaviour
      @ requires_free 0 <= begin <= end <= values.length;
      @ requires_free end - begin == indices.length;
      @ requires_free \disjoint(values[*], indices[*], this.tree.tree[*], this.sorted_splitters[*]);
      @
      @ ensures_free (\forall int i; 0 <= i && i < indices.length; this.classOf(values[begin + i]) == indices[i]);
      @
      @ assignable_free indices[*];
      @*/
    public void classify_all(int[] values, int begin, int end, int[] indices) {
        this.tree.classify_all(values, begin, end, indices);
        if (this.equal_buckets) {
            /*@ loop_invariant_free 0 <= i <= indices.length;
              @ loop_invariant_free (\forall int j; 0 <= j < i; this.classify(values[begin + j]) == indices[j]);
              @ loop_invariant_free (\forall int j; i <= j < indices.length; this.tree.classify(values[begin + j]) == indices[j]);
              @ loop_invariant_free \invariant_for(this) && \invariant_for(this.tree);
              @
              @ decreases indices.length - i;
              @ assignable_free indices[*];
              @*/
            for (int i = 0; i < indices.length; ++i) {
                final int value = values[begin + i];
                //@ assume \dl_inInt(value);
                final int index = indices[i];
                //@ assert this.tree.num_buckets <= index < 2 * this.tree.num_buckets;
                //@ assume 0 <= (index - this.num_buckets / 2) < this.sorted_splitters.length;
                final int bucket = index - this.num_buckets / 2;
                final boolean equal_to_splitter = !Constants.cmp(value, this.sorted_splitters[bucket]);
                indices[i] = 2 * index + Constants.toInt(equal_to_splitter) - this.num_buckets;
            }
        } else {
            /*@ loop_invariant_free 0 <= i <= indices.length;
              @ loop_invariant_free (\forall int j; 0 <= j < i; this.classify(values[begin + j]) == indices[j]);
              @ loop_invariant_free (\forall int j; i <= j < indices.length; this.tree.classify(values[begin + j]) == indices[j]);
              @ loop_invariant_free \invariant_for(this) && \invariant_for(this.tree);
              @
              @ decreases indices.length - i;
              @ assignable_free indices[*];
              @*/
            for (int i = 0; i < indices.length; ++i) {
                //@ assume \dl_inInt(values[begin + i]);
                indices[i] -= this.num_buckets;
            }
        }
    }

    /*@ model_behaviour
      @ requires bucket_starts.length >= this.num_buckets;
      @ accessible this.sorted_splitters[*];
      @ accessible this.tree.tree[*];
      @ accessible values[begin..write - 1];
      @ accessible bucket_starts[0..this.num_buckets];
      @ model boolean allElementsCounted(int[] values, int begin, int write, int[] bucket_starts) {
      @     return
      @         (\forall int b; 0 <= b && b < this.num_buckets; bucket_starts[b] == this.countClassOfSliceEq(values, begin, write, b)) &&
      @         (\sum int b; 0 <= b < this.num_buckets; bucket_starts[b]) == write - begin;
      @ }
      @*/

    public static final int BATCH_SIZE = 16;

    /*@ model_behaviour
      @ requires \invariant_for(buffers);
      @
      @ requires bucket_starts.length >= this.num_buckets;
      @ requires buffers.num_buckets == this.num_buckets;
      @ requires Buffers.isBlockAligned(write - begin);
      @ accessible
      @     this.sorted_splitters[*], this.tree.tree[*],
      @     values[begin..write - 1],
      @     bucket_starts[0..this.num_buckets],
      @     buffers.indices[0..this.num_buckets - 1],
      @     buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
      @ model boolean isClassifiedUntil(int[] values, int begin, int write, int i, int[] bucket_starts, Buffers buffers) {
      @     return this.allElementsCounted(values, begin, write, bucket_starts) &&
      @         isClassifiedBlocksRange(values, begin, write) &&
      @         buffers.isClassifiedWith(this) &&
      @         (\forall int b; 0 <= b < this.num_buckets; isValidBufferLen(buffers.bufferLen(b), bucket_starts[b])) &&
      @         buffers.count() == i - write;
      @ }
      @*/

    /*@ model_behaviour
      @ requires \invariant_for(buffers);
      @ ensures_free \result >= 0;
      @
      @ accessible values[begin..write - 1];
      @ accessible values[read..end - 1];
      @ accessible buffers.indices[0..buffers.num_buckets - 1], buffers.buffer[0..Buffers.BUFFER_SIZE * buffers.num_buckets - 1];
      @ model static int countElement(int[] values, int begin, int write, int read, int end, Buffers buffers, int element) {
      @     return
      @         // element in [begin,write)
      @         Functions.countElement(values, begin, write, element) +
      @         // element in [read,end)
      @         Functions.countElement(values, read, end, element) +
      @         // element in all buffers
      @         buffers.countElement(element);
      @ }
      @*/

    /*@ model_behaviour
      @ requires 0 <= len <= Buffers.BUFFER_SIZE;
      @
      @ ensures_free \result ==> Buffers.bufferSizeForBucketLen(len + writtenElements) == len;
      @ static model no_state boolean isValidBufferLen(int len, int writtenElements) {
      @     return
      @         0 <= writtenElements &&
      @         Buffers.isBlockAligned(writtenElements) &&
      @         (0 < writtenElements ==> len != 0);
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires_free \invariant_free_for(buffers);
      @
      @ requires_free bucket_starts.length >= this.num_buckets + 1;
      @ requires_free \disjoint(values[*], bucket_starts[*], buffers.buffer[*], buffers.indices[*], this.sorted_splitters[*], this.tree.tree[*], indices[*]);
      @ requires_free buffers.num_buckets == this.num_buckets;
      @
      @ requires_free 0 <= begin <= end <= values.length;
      @
      @ requires_free begin <= write <= i && i + indices.length <= end;
      @ requires_free Buffers.isBlockAligned(write - begin);
      @ requires_free (i - begin) % BATCH_SIZE == 0;
      @ requires_free indices.length <= BATCH_SIZE;
      @
      @ requires_free (\forall int j; 0 <= j < indices.length; this.classOf(values[i + j]) == indices[j]);
      @
      @ requires_free this.isClassifiedUntil(values, begin, write, i, bucket_starts, buffers);
      @
      @ ensures_free \invariant_free_for(buffers) && \invariant_free_for(this);
      @ ensures \invariant_for(buffers) && \invariant_for(this);
      @
      @ ensures_free write <= \result && \result <= i && Buffers.isBlockAligned(\result - begin);
      @ ensures_free this.isClassifiedUntil(values, begin, \result, i + indices.length, bucket_starts, buffers);
      @
      @ ensures_free (\forall int element; true;
      @     \old(Classifier.countElement(values, begin, write, i, end, buffers, element)) ==
      @          Classifier.countElement(values, begin, \result, i + indices.length, end, buffers, element)
      @ );
      @
      @ // Bucket starts
      @
      @ assignable_free values[write..i - 1];
      @ assignable_free bucket_starts[0..this.num_buckets - 1];
      @ assignable_free buffers.indices[0..this.num_buckets - 1], buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
      @*/
    private int finish_batch(int[] indices, int[] values, int begin, int write, int i, int end, int[] bucket_starts, Buffers buffers) {
        //@ ghost int old_write = write;
        /*@ loop_invariant_free 0 <= j && j <= indices.length;
          @
          @ loop_invariant_free \old(write) <= write && write <= i;
          @ loop_invariant_free Buffers.isBlockAligned(write - begin);
          @
          @ loop_invariant_free this.isClassifiedUntil(values, begin, write, i + j, bucket_starts, buffers);
          @
          @ loop_invariant_free (\forall int element; true;
          @     \old(Classifier.countElement(values, begin, old_write, i, end, buffers, element)) ==
          @          Classifier.countElement(values, begin, write, i + j, end, buffers, element)
          @ );
          @
          @ loop_invariant_free \invariant_for(buffers) && \invariant_for(this);
          @
          @ decreases indices.length - j;
          @
          @ assignable_free buffers.indices[0..this.num_buckets - 1], buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
          @ assignable_free values[old_write..i - 1];
          @ assignable_free bucket_starts[0..this.num_buckets - 1];
          @*/
        for (int j = 0; j < indices.length; ++j) {
            //@ ghost \dl_Heap heapAtLoopBodyBegin = \dl_heap();

            int bucket = indices[j];
            int value = values[i + j];

            //@ assume this.classOf(value) == bucket;
            //@ assume 0 <= bucket < this.num_buckets;

            /*@ public normal_behaviour
              @ ensures_free buffers.bufferLen(bucket) != Buffers.BUFFER_SIZE;
              @
              @ ensures_free \old(write) <= write && write <= i;
              @ ensures_free Buffers.isBlockAligned(write - begin);
              @
              @ ensures_free this.allElementsCounted(values, begin, write, bucket_starts) &&
              @     isClassifiedBlocksRange(values, begin, write) &&
              @     buffers.isClassifiedWith(this) &&
              @     buffers.count() == i + j - write;
              @
              @ ensures_free (\forall int b; 0 <= b < this.num_buckets;
              @     isValidBufferLen(buffers.bufferLen(b) + (b == bucket ? 1 : 0), bucket_starts[b])
              @ );
              @
              @ ensures_free (\forall int element; true;
              @     \old(Classifier.countElement(values, begin, old_write, i, end, buffers, element)) ==
              @          Classifier.countElement(values, begin, write, i + j, end, buffers, element)
              @ );
              @
              @ ensures_free \invariant_free_for(buffers) && \invariant_free_for(this);
              @ ensures \invariant_for(buffers) && \invariant_for(this);
              @
              @ assignable_free buffers.indices[bucket];
              @ assignable_free values[old_write..i - 1];
              @ assignable_free bucket_starts[bucket];
              @*/
            {
                if (buffers.len(bucket) == Buffers.BUFFER_SIZE) {
                    // Use element lower bound
                    /*@ assume write + 256 <= i &&
                      @     Buffers.isBlockAlignedAdd(write - begin, Buffers.BUFFER_SIZE) &&
                      @     Buffers.isBlockAlignedAdd(bucket_starts[bucket], Buffers.BUFFER_SIZE);
                      @*/

                    // This was moved ahead to remove heap modifications after flush, changes nothing in the algorithm
                    bucket_starts[bucket] += Buffers.BUFFER_SIZE;

                    buffers.flush(bucket, values, write, i);

                    /*@ assume
                      @     \invariant_for(this) &&
                      @     Buffers.isBlockAligned(write + Buffers.BUFFER_SIZE - begin) &&
                      @     Buffers.isBlockAligned(bucket_starts[bucket]);
                      @*/

                    // Split off the written part
                    /*@ assume
                      @     this.isClassifiedBlocksRangeSplit(values, begin, write, write + Buffers.BUFFER_SIZE) &&
                      @     this.isClassOfSliceCopy(buffers.buffer, bucket * Buffers.BUFFER_SIZE, values, write, Buffers.BUFFER_SIZE, bucket) &&
                      @     Functions.countElementSplit(values, begin, write, write + Buffers.BUFFER_SIZE);
                      @*/
                    //@ assume this.isClassOfSlice(values, write, write + Buffers.BUFFER_SIZE, bucket);
                    //@ assume this.countClassOfSliceEqLemma(values, write, write + Buffers.BUFFER_SIZE, bucket);
                    /*@ assume (\forall int b; 0 <= b && b < this.num_buckets;
                      @     \at(this.countClassOfSliceEq(values, begin, write, b), heapAtLoopBodyBegin) + (b == bucket ? Buffers.BUFFER_SIZE : 0) ==
                      @         this.countClassOfSliceEq(values, begin, write + Buffers.BUFFER_SIZE, b)
                      @ );
                      @*/

                    /*@ assume (\sum int b; 0 <= b < this.num_buckets; bucket_starts[b]) ==
                      @         (\sum int b; 0 <= b < this.num_buckets; \at(bucket_starts[b], heapAtLoopBodyBegin)) + Buffers.BUFFER_SIZE;
                      @*/

                    write += Buffers.BUFFER_SIZE;
                }
            }
            //@ assume \dl_inInt(value);
            buffers.push(bucket, value);
            //@ assume \invariant_for(this) && Functions.countElementSplit(values, i + j, i + j + 1, end);
            // permutation property: elements in [begin,write) stayed the same, split first in [read,end), split on element = value
        }

        return write;
    }

    /*@ public normal_behaviour
      @ requires_free \invariant_free_for(buffers);
      @
      @ requires_free bucket_starts.length >= this.num_buckets + 1;
      @ requires_free 0 <= begin <= end <= values.length;
      @ requires_free (\forall int b; 0 <= b < this.num_buckets; bucket_starts[b] == 0);
      @ requires_free buffers.isEmpty();
      @ requires_free \disjoint(values[*], bucket_starts[*], buffers.buffer[*], buffers.indices[*], this.sorted_splitters[*], this.tree.tree[*]);
      @ requires_free buffers.num_buckets == this.num_buckets;
      @
      @ ensures_free \invariant_free_for(buffers);
      @ ensures \invariant_for(buffers);
      @
      @ // classifies until end - (end - begin) % BATCH_SIZE
      @
      @ ensures_free begin <= \result && \result <= (end - (end - begin) % BATCH_SIZE) && Buffers.isBlockAligned(\result - begin);
      @ ensures_free this.isClassifiedUntil(values, begin, \result, end - (end - begin) % BATCH_SIZE, bucket_starts, buffers);
      @ ensures_free (\forall int element; true;
      @     \old(Classifier.countElement(values, begin, begin, begin, end, buffers, element)) ==
      @          Classifier.countElement(values, begin, \result, end - (end - begin) % BATCH_SIZE, end, buffers, element)
      @ );
      @
      @ assignable_free values[begin..end - (end - begin) % BATCH_SIZE - 1];
      @ assignable_free bucket_starts[0..this.num_buckets - 1];
      @ assignable_free buffers.indices[0..this.num_buckets - 1], buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
      @*/
    public int classify_locally_batched(int[] values, int begin, int end, int[] bucket_starts, Buffers buffers) {
        int write = begin;
        int i = begin;

        /*@ assume
          @     this.isClassifiedUntil(values, begin, write, i, bucket_starts, buffers) &&
          @     (\forall int element; true;
          @         \old(Classifier.countElement(values, begin, begin, begin, end, buffers, element)) ==
          @              Classifier.countElement(values, begin, write, i, end, buffers, element)
          @     );
          @*/
        if (end - begin >= BATCH_SIZE) {
            int cutoff = end - BATCH_SIZE;
            final int[] indices = new int[BATCH_SIZE];
            //@ assume \disjoint(values[*], bucket_starts[*], buffers.buffer[*], buffers.indices[*], this.sorted_splitters[*], this.tree.tree[*], indices[*]);

            /*@ loop_invariant_free begin <= i && i <= end - (end - begin) % BATCH_SIZE;
              @
              @ loop_invariant_free begin <= write && write <= i;
              @ loop_invariant_free (i - begin) % BATCH_SIZE == 0;
              @ loop_invariant_free Buffers.isBlockAligned(write - begin);
              @
              @ // Bucket starts contain all elements in values[..write]
              @ loop_invariant_free this.isClassifiedUntil(values, begin, write, i, bucket_starts, buffers);
              @
              @ loop_invariant_free (\forall int element; true;
              @     \old(Classifier.countElement(values, begin, begin, begin, end, buffers, element)) ==
              @          Classifier.countElement(values, begin, write, i, end, buffers, element)
              @ );
              @
              @ loop_invariant_free \invariant_for(buffers) && \invariant_for(this);
              @
              @ decreases end - i;
              @
              @ assignable_free buffers.indices[0..this.num_buckets - 1], buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
              @ assignable_free values[begin..end - (end - begin) % BATCH_SIZE - 1];
              @ assignable_free bucket_starts[0..this.num_buckets - 1];
              @ assignable_free indices[*];
              @*/
            while (i <= cutoff) {
                this.classify_all(values, i, i + BATCH_SIZE, indices);

                write = this.finish_batch(indices, values, begin, write, i, end, bucket_starts, buffers);

                i += BATCH_SIZE;
            }
            //@ assume i == end - (end - begin) % BATCH_SIZE;
        }

        return write;
    }

    /*@ public normal_behaviour
      @ requires_free \invariant_free_for(buffers);
      @
      @ requires_free bucket_starts.length >= this.num_buckets + 1;
      @ requires_free 0 <= begin <= end <= values.length;
      @ requires_free \disjoint(values[*], bucket_starts[*], buffers.buffer[*], buffers.indices[*], this.sorted_splitters[*], this.tree.tree[*]);
      @ requires_free buffers.num_buckets == this.num_buckets;
      @ requires_free this.isClassifiedUntil(values, begin, write, end, bucket_starts, buffers);
      @ requires_free begin <= write <= end;
      @ requires_free Buffers.isBlockAligned(write - begin);
      @
      @ ensures_free Functions.isValidBucketStarts(bucket_starts, this.num_buckets) && bucket_starts[this.num_buckets] == end - begin;
      @ ensures_free (\forall int b; 0 <= b < this.num_buckets;
      @     bucket_starts[b + 1] - bucket_starts[b] ==
      @         \old(this.countClassOfSliceEq(values, begin, write, b)) + \old(buffers.bufferLen(b))
      @ );
      @
      @ assignable_free bucket_starts[0..this.num_buckets];
      @*/
    public void calculate_bucket_starts(int[] values, int begin, int write, int end, int[] bucket_starts, Buffers buffers) {
        // bucket_starts contains the bucket counts without buffer contents
        // Calculate bucket starts
        int sum = 0;

        /*@ loop_invariant_free 0 <= j <= this.num_buckets;
          @ loop_invariant_free 0 < j ==> bucket_starts[j - 1] <= sum && bucket_starts[0] == 0;
          @ loop_invariant_free sum == (\sum int b; 0 <= b < j;
          @     \old(this.countClassOfSliceEq(values, begin, write, b)) + \old(buffers.bufferLen(b))
          @ );
          @ loop_invariant_free Functions.isSortedSlice(bucket_starts, 0, j);
          @ loop_invariant_free (\forall int b; j <= b < this.num_buckets; bucket_starts[b] == \old(this.countClassOfSliceEq(values, begin, write, b)));
          @ loop_invariant_free (\forall int b; 0 <= b < j;
          @     (b + 1 == j ? sum : bucket_starts[b + 1]) - bucket_starts[b] ==
          @         \old(this.countClassOfSliceEq(values, begin, write, b)) + \old(buffers.bufferLen(b))
          @ );
          @
          @ decreases this.num_buckets - j;
          @
          @ assignable_free bucket_starts[0..this.num_buckets];
          @*/
        for (int j = 0; j < this.num_buckets; ++j) {
            //@ assume \invariant_for(buffers);
            /*@ assume
              @     bucket_starts[j] == \old(this.countClassOfSliceEq(values, begin, write, j)) &&
              @     buffers.bufferLen(j) == \old(buffers.bufferLen(j));
              @*/
            // Add the partially filled buffers
            int size = bucket_starts[j] + buffers.len(j);

            // Exclusive prefix sum
            bucket_starts[j] = sum;
            sum += size;
            //@ assume size >= 0;
        }
        bucket_starts[this.num_buckets] = sum;

        //@ assume sum == end - begin && Functions.isSortedSlice(bucket_starts, 0, this.num_buckets + 1);
    }

    /*@ public normal_behaviour
      @ requires_free \invariant_free_for(buffers);
      @
      @ requires_free bucket_starts.length >= this.num_buckets + 1;
      @ requires_free 0 <= begin <= end <= values.length;
      @ requires_free (\forall int b; 0 <= b < this.num_buckets; bucket_starts[b] == 0);
      @ requires_free buffers.isEmpty();
      @ requires_free \disjoint(values[*], bucket_starts[*], buffers.buffer[*], buffers.indices[*], this.sorted_splitters[*], this.tree.tree[*]);
      @ requires_free buffers.num_buckets == this.num_buckets;
      @
      @ ensures_free begin <= \result && \result <= end && Buffers.isBlockAligned(\result - begin);
      @ ensures_free this.isClassifiedBlocksRange(values, begin, \result);
      @ ensures_free buffers.isClassifiedWith(this);
      @ ensures_free Functions.isValidBucketStarts(bucket_starts, this.num_buckets) && bucket_starts[this.num_buckets] == end - begin;
      @
      @ ensures_free (\forall int b; 0 <= b < this.num_buckets;
      @     // Bucket starts contains the bucket counts
      @     bucket_starts[b + 1] - bucket_starts[b] ==
      @         buffers.bufferLen(b) + this.countClassOfSliceEq(values, begin, \result, b) &&
      @     // Buffer len is correct for the bucket size
      @     buffers.bufferLen(b) == Buffers.bufferSizeForBucketLen(bucket_starts[b + 1] - bucket_starts[b])
      @ );
      @ ensures_free (\forall int element; true;
      @     \old(Functions.countElement(values, begin, end, element)) ==
      @         Functions.countElement(values, begin, \result, element) +
      @         buffers.countElement(element)
      @ );
      @ ensures_free \invariant_free_for(buffers);
      @ ensures \invariant_for(buffers);
      @
      @ // All values are either in a buffer or in values[..\result]
      @ // Bucket starts
      @
      @ assignable_free values[begin..end - 1];
      @ assignable_free bucket_starts[0..this.num_buckets];
      @ assignable_free buffers.indices[0..this.num_buckets - 1], buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
      @*/
    public int classify_locally(int[] values, int begin, int end, int[] bucket_starts, Buffers buffers) {
        /*@ assume (\forall int element; true;
          @     Functions.countElement(values, begin, end, element) ==
          @         Classifier.countElement(values, begin, begin, begin, end, buffers, element)
          @ );
          @*/
        int write = this.classify_locally_batched(values, begin, end, bucket_starts, buffers);
        int i = end - (end - begin) % BATCH_SIZE;
        //@ assume end - i >= 0;
        int[] indices = new int[end - i];
        //@ assume \disjoint(values[*], bucket_starts[*], buffers.buffer[*], buffers.indices[*], this.sorted_splitters[*], this.tree.tree[*], indices[*]);
        this.classify_all(values, i, end, indices);
        write = this.finish_batch(indices, values, begin, write, i, end, bucket_starts, buffers);

        this.calculate_bucket_starts(values, begin, write, end, bucket_starts, buffers);
        return write;
    }
}
