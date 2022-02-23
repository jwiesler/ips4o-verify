package de.wiesler;

public final class Classifier {
    public static final int STORAGE_SIZE = (1 << Constants.LOG_MAX_BUCKETS);

    private final Tree tree;
    private /*@ spec_public @*/ final int num_buckets;
    private final int[] sorted_splitters;
    private final boolean equal_buckets;

    //@ ghost final \locset footprint;

    /*@ public invariant 2 <= this.num_buckets <= Constants.MAX_BUCKETS;
      @ public invariant this.num_buckets == (1 << (this.tree.log_buckets + Constants.toInt(this.equal_buckets)));
      @ invariant this.tree.num_buckets <= this.sorted_splitters.length;
      @ invariant Functions.isValidSlice(this.sorted_splitters, 0, this.tree.num_buckets);
      @ invariant Functions.isSortedSlice(this.sorted_splitters, 0, this.tree.num_buckets);
      @ invariant this.sorted_splitters[this.tree.num_buckets - 1] == this.sorted_splitters[this.tree.num_buckets - 2];
      @ invariant this.footprint == \set_union(this.sorted_splitters[*], this.tree.tree[*]);
      @ accessible \inv: this.sorted_splitters[*], this.tree.tree[*];
      @*/

    /*@ public model_behaviour
      @ requires array != this.sorted_splitters && this.tree.doesNotAlias(array);
      @ accessible \nothing;
      @ model boolean doesNotAlias(int[] array) {
      @     return true;
      @ }
      @*/

    /*@ public model_behaviour
      @ ensures 0 <= \result < this.num_buckets;
      @ accessible this.footprint;
      @ model int classOf(int value) {
      @     return this.classify(value);
      @ }
      @*/

    /*@ public model_behaviour
      @ accessible this.footprint;
      @ model boolean isClassOfSeq(\seq values, int bucket) {
      @     return (\forall
      @              int i;
      @              0 <= i < values.length;
      @              this.classOf((int) values[i]) == bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ accessible this.footprint, values[begin..end - 1];
      @ model boolean isClassOfSlice(int[] values, int begin, int end, int bucket) {
      @     return (\forall
      @              int i;
      @              begin <= i < end;
      @              this.classOf((int) values[i]) == bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires begin <= mid <= end;
      @ requires this.isClassOfSlice(values, begin, end, bucket);
      @
      @ ensures \result;
      @
      @ // Verified
      @ model boolean isClassOfSliceSplit(int[] values, int begin, int mid, int end, int bucket) {
      @     return this.isClassOfSlice(values, begin, mid, bucket) && this.isClassOfSlice(values, mid, end, bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires this.isClassOfSlice(src, srcPos, srcPos + length, bucket);
      @ requires (\forall int i; 0 <= i && i < length; dest[destPos + i] == src[srcPos + i]);
      @
      @ ensures \result;
      @
      @ // Verified
      @ model boolean isClassOfSliceCopy(int[] src, int srcPos, int[] dest, int destPos, int length, int bucket) {
      @     return this.isClassOfSlice(dest, destPos, destPos + length, bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires begin <= mid <= end;
      @ requires this.isClassOfSlice(values, begin, mid, bucket) && this.isClassOfSlice(values, mid, end, bucket);
      @
      @ ensures \result;
      @
      @ // Verified
      @ model boolean isClassOfSliceConcat(int[] values, int begin, int mid, int end, int bucket) {
      @     return this.isClassOfSlice(values, begin, end, bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ accessible this.footprint;
      @ model int countClassOfSeqEq(\seq values, int bucket) {
      @     return (\num_of
      @              int i;
      @              0 <= i < values.length;
      @              this.classOf((int) values[i]) == bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ accessible this.footprint, values[begin..end - 1];
      @ model boolean isClassifiedBlock(int[] values, int begin, int end) {
      @     return (\exists int bucket; 0 <= bucket < this.num_buckets; this.isClassOfSeq(\dl_seq_def_workaround(begin, end, values), bucket));
      @ }
      @*/

    /*@ public model_behaviour
      @ accessible this.footprint;
      @ model boolean isClassifiedBlockSeq(\seq values) {
      @     return (\exists int bucket; 0 <= bucket < this.num_buckets; this.isClassOfSeq(values, bucket));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires Functions.isAlignedTo(end - begin, Buffers.BUFFER_SIZE);
      @ accessible this.footprint, values[begin..end - 1];
      @ model boolean isClassifiedBlocksRange(int[] values, int begin, int end) {
      @     return (\forall
      @         int block;
      @         0 <= block && block < (end - begin) / Buffers.BUFFER_SIZE;
      @         this.isClassifiedBlock(values, begin + block * Buffers.BUFFER_SIZE, begin + (block + 1) * Buffers.BUFFER_SIZE)
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires Functions.isAlignedTo(values.length, Buffers.BUFFER_SIZE);
      @ accessible this.footprint;
      @ model boolean isClassifiedBlocksRangeSeq(\seq values) {
      @     return (\forall
      @         int block;
      @         0 <= block && block < values.length / Buffers.BUFFER_SIZE;
      @         this.isClassifiedBlockSeq(\dl_seqSub(values, block * Buffers.BUFFER_SIZE, (block + 1) * Buffers.BUFFER_SIZE - 1))
      @     );
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires tree != sorted_splitters;
      @ requires 1 <= log_buckets <= Constants.LOG_MAX_BUCKETS;
      @ requires Functions.isValidSlice(sorted_splitters, 0, 1 << log_buckets);
      @ requires Functions.isSortedSlice(sorted_splitters, 0, 1 << log_buckets);
      @ requires (1 << log_buckets) <= tree.length;
      @ requires sorted_splitters[(1 << log_buckets) - 1] == sorted_splitters[(1 << log_buckets) - 2];
      @
      @ assignable sorted_splitters[*], tree[*];
      @*/
    public Classifier(int[] sorted_splitters, int[] tree, int log_buckets, boolean equal_buckets) {
        int num_buckets = 1 << log_buckets;
        //@ assert 2 <= num_buckets <= (1 << Constants.LOG_MAX_BUCKETS);

        int num_splitters = num_buckets - 1;
        assert (sorted_splitters[num_splitters] == sorted_splitters[num_splitters - 1]);

        this.tree = new Tree(sorted_splitters, tree, log_buckets);
        //@ assert this.tree.log_buckets == log_buckets;
        //@ assert sorted_splitters[num_splitters] == sorted_splitters[num_splitters - 1];
        this.sorted_splitters = sorted_splitters;
        this.num_buckets = num_buckets << Constants.toInt(equal_buckets);
        this.equal_buckets = equal_buckets;
        //@ set this.footprint = \set_union(\all_fields(this.sorted_splitters), \all_fields(this.tree.tree));
    }

    /*@ public normal_behaviour
      @ requires Functions.isValidSlice(splitters, 0, num_splitters);
      @ requires Functions.isSortedSlice(splitters, 0, num_splitters);
      @ requires splitters != tree;
      @
      @ requires 1 <= num_splitters && num_splitters <= num_buckets - 1;
      @ requires 2 <= num_buckets && num_buckets <= (1 << Constants.LOG_MAX_BUCKETS);
      @ requires splitters.length == Classifier.STORAGE_SIZE;
      @ requires tree.length == Classifier.STORAGE_SIZE;
      @
      @ ensures \fresh(\result);
      @ ensures \invariant_for(\result);
      @ ensures \result.sorted_splitters == splitters && \result.tree.tree == tree && \result.num_buckets == num_buckets;
      @
      @ assignable splitters[*], tree[*];
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
        //@ assert log_buckets <= Constants.LOG_MAX_BUCKETS;
        int actual_num_buckets = 1 << log_buckets;
        //@ assert actual_num_buckets <= splitters.length;

        /*@
          @ loop_invariant num_splitters <= i && i <= actual_num_buckets;
          @
          @ loop_invariant (\forall
          @     int j;
          @     0 <= j < num_splitters;
          @     // It is unchanged
          @     splitters[j] == \old(splitters[j])
          @ );
          @ loop_invariant (\forall int j; num_splitters <= j < i; splitters[j] == splitters[num_splitters - 1]);
          @ loop_invariant Functions.isValidSlice(splitters, 0, i);
          @ loop_invariant Functions.isSortedSlice(splitters, 0, i);
          @
          @ decreases actual_num_buckets - i;
          @ assignable splitters[num_splitters..actual_num_buckets - 1];
          @*/
        for (int i = num_splitters; i < actual_num_buckets; ++i) {
            splitters[i] = splitters[num_splitters - 1];
        }

        // TODO remove workaround
        Functions.fill(tree, 0, tree.length, 0);
        return new Classifier(splitters, tree, log_buckets, use_equal_buckets);
    }

    /*@ public normal_behaviour
      @ ensures \result == this.num_buckets;
      @ assignable \strictly_nothing;
      @*/
    public int num_buckets() {
        return this.num_buckets;
    }

    /*@ public normal_behaviour
      @ ensures \result == this.equal_buckets;
      @ assignable \strictly_nothing;
      @*/
    public boolean equal_buckets() {
        return this.equal_buckets;
    }

    /*@ public normal_behaviour
      @ ensures 0 <= \result < this.num_buckets;
      @ ensures this.classOf(value) == \result;
      @ assignable \strictly_nothing;
      @ accessible this.footprint;
      @*/
    public /*@ pure */ int classify(int value) {
        int index = this.tree.classify(value);
        int bucket;
        if (this.equal_buckets) {
            int bucket_index = index - this.num_buckets / 2;
            boolean equal_to_splitter = !Constants.cmp(value, this.sorted_splitters[bucket_index]);
            bucket = 2 * index + Constants.toInt(equal_to_splitter) - this.num_buckets;
        } else {
            bucket = index - this.num_buckets;
        }
        assert (bucket < this.num_buckets);
        return bucket;
    }

    /*@ public normal_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires end - begin == indices.length;
      @
      @ ensures (\forall int i; 0 <= i && i < indices.length; 0 <= indices[i] < this.num_buckets);
      @ ensures (\forall int i; 0 <= i && i < indices.length; this.classOf(values[begin + i]) == indices[i]);
      @
      @ assignable indices[*];
      @*/
    public void classify_all(int[] values, int begin, int end, int[] indices) {
        // TODO class invariant
        //@ assert (this.num_buckets == 1 << (this.tree.log_buckets + Constants.toInt(this.equal_buckets)));

        this.tree.classify_all(values, begin, end, indices);
        if (this.equal_buckets) {
            for (int i = 0; i < indices.length; ++i) {
                final int value = values[begin + i];
                final int index = indices[i];
                final int bucket = index - this.num_buckets / 2;
                final boolean equal_to_splitter = !Constants.cmp(value, this.sorted_splitters[bucket]);
                indices[i] = 2 * index + Constants.toInt(equal_to_splitter);
            }
        }
        for (int i = 0; i < indices.length; ++i) {
            indices[i] -= this.num_buckets;
            assert (indices[i] < this.num_buckets);
        }
    }

    /*@ model_behaviour
      @ ensures \result >= 0;
      @
      @ accessible this.footprint, values[begin..end - 1];
      @ model int countClassifiedElements(int[] values, int begin, int end, int bucket) {
      @     return (\num_of int i; begin <= i && i < end; this.classOf(values[i]) == bucket);
      @ }
      @*/

    /*@ model_behaviour
      @ requires bucket_starts.length >= this.num_buckets;
      @ accessible this.footprint, values[begin..write - 1], bucket_starts[0..this.num_buckets];
      @ model boolean allElementsCounted(int[] values, int begin, int write, int[] bucket_starts) {
      @     return (\forall int b; 0 <= b && b < this.num_buckets; bucket_starts[b] == this.countClassifiedElements(values, begin, write, b));
      @ }
      @*/

    public static final int BATCH_SIZE = 16;

    /*@ model_behaviour
      @ requires \invariant_for(buffers);
      @
      @ requires bucket_starts.length >= this.num_buckets;
      @ requires buffers.num_buckets == this.num_buckets;
      @ requires Functions.isAlignedTo(write - begin, Buffers.BUFFER_SIZE);
      @ accessible
      @     this.footprint,
      @     values[begin..write - 1],
      @     bucket_starts[0..this.num_buckets],
      @     buffers.indices[0..this.num_buckets - 1],
      @     buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
      @ model boolean isClassifiedUntil(int[] values, int begin, int write, int i, int[] bucket_starts, Buffers buffers) {
      @     return this.allElementsCounted(values, begin, write, bucket_starts)
      @         && isClassifiedBlocksRange(values, begin, write)
      @         && buffers.isClassifiedWith(this)
      @         && buffers.count() == i - write;
      @ }
      @*/

    /*@ model_behaviour
      @ requires \invariant_for(buffers);
      @
      @ requires buffers.num_buckets == this.num_buckets;
      @ requires Functions.isAlignedTo(end - begin, Buffers.BUFFER_SIZE);
      @ requires buffers.isClassifiedWith(this);
      @
      @ ensures \result >= 0;
      @
      @ accessible
      @     this.footprint,
      @     values[begin..end - 1],
      @     buffers.indices[0..this.num_buckets - 1],
      @     buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
      @
      @ // All elements in [begin, end) and the buffers that are classified < bucket
      @ model int allElementsInRangeAndBuffersLT(int[] values, int begin, int end, Buffers buffers, int bucket) {
      @     return (\num_of int i; begin <= i && i < end; this.classOf(values[i]) < bucket) +
      @         (\sum int c; 0 <= c < bucket; buffers.bufferAt(c).length);
      @ }
      @*/

    /*@ model_behaviour
      @ requires Functions.isAlignedTo(write - begin, Buffers.BUFFER_SIZE);
      @ requires 0 <= begin <= write <= read <= end <= values.length;
      @
      @ ensures \result >= 0;
      @
      @ accessible values[begin..end];
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

    /*@ public normal_behaviour
      @ requires \invariant_for(buffers);
      @
      @ requires bucket_starts.length >= this.num_buckets + 1;
      @ requires \disjoint(values[*], bucket_starts[*], buffers.buffer[*], buffers.indices[*], this.footprint, indices[*]);
      @ requires buffers.num_buckets == this.num_buckets;
      @
      @ requires Functions.isValidSlice(values, begin, end);
      @
      @ requires begin <= write <= i && i + indices.length <= end;
      @ requires Functions.isAlignedTo(write - begin, Buffers.BUFFER_SIZE);
      @
      @ requires (\forall int j; 0 <= j < indices.length; this.classOf(values[i + j]) == indices[j]);
      @
      @ requires this.isClassifiedUntil(values, begin, write, i, bucket_starts, buffers);
      @
      @ ensures \invariant_for(buffers) && \invariant_for(this);
      @
      @ ensures write <= \result && \result <= i && Functions.isAlignedTo(\result - begin, Buffers.BUFFER_SIZE);
      @ ensures this.isClassifiedUntil(values, begin, \result, i + indices.length, bucket_starts, buffers);
      @
      @ ensures (\forall int element; true;
      @     \old(Classifier.countElement(values, begin, write, i, end, buffers, element)) ==
      @          Classifier.countElement(values, begin, \result, i + indices.length, end, buffers, element)
      @ );
      @
      @ // Bucket starts
      @
      @ assignable values[write..i - 1];
      @ assignable bucket_starts[0..this.num_buckets - 1];
      @ assignable buffers.indices[0..this.num_buckets - 1], buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
      @*/
    private int finish_batch(int[] indices, int[] values, int begin, int write, int i, int end, int[] bucket_starts, Buffers buffers) {
        //@ ghost int old_write = write;
        /*@ loop_invariant 0 <= j && j <= indices.length;
          @
          @ loop_invariant \old(write) <= write && write <= i;
          @ loop_invariant Functions.isAlignedTo(write - begin, Buffers.BUFFER_SIZE);
          @
          @ loop_invariant this.isClassifiedUntil(values, begin, write, i + j, bucket_starts, buffers);
          @
          @ loop_invariant (\forall int element; true;
          @     \old(Classifier.countElement(values, begin, old_write, i, end, buffers, element)) ==
          @          Classifier.countElement(values, begin, write, i + j, end, buffers, element)
          @ );
          @
          @ loop_invariant \invariant_for(buffers) && \invariant_for(this);
          @
          @ decreases indices.length - j;
          @
          @ assignable buffers.indices[0..this.num_buckets - 1], buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
          @ assignable values[old_write..i - 1];
          @ assignable bucket_starts[0..this.num_buckets - 1];
          @*/
        for (int j = 0; j < indices.length; ++j) {
            int bucket = indices[j];
            int value = values[i + j];

            //@ assert this.classOf(value) == bucket;
            //@ assert 0 <= bucket < this.num_buckets;

            /*@ public normal_behaviour
              @ ensures buffers.bufferAt(bucket).length != Buffers.BUFFER_SIZE;
              @
              @ ensures \old(write) <= write && write <= i;
              @ ensures Functions.isAlignedTo(write - begin, Buffers.BUFFER_SIZE);
              @
              @ ensures this.isClassifiedUntil(values, begin, write, i + j, bucket_starts, buffers);
              @ ensures (\forall int element; true;
              @     \old(Classifier.countElement(values, begin, old_write, i, end, buffers, element)) ==
              @          Classifier.countElement(values, begin, write, i + j, end, buffers, element)
              @ );
              @
              @ ensures \invariant_for(buffers);
              @
              @ assignable buffers.indices[0..this.num_buckets - 1];
              @ assignable values[old_write..i - 1];
              @ assignable bucket_starts[0..this.num_buckets - 1];
              @*/
            {
                if (buffers.len(bucket) == Buffers.BUFFER_SIZE) {
                    // Use element lower bound
                    //@ assert write + 256 <= i;
                    buffers.flush(bucket, values, write, i);
                    write += Buffers.BUFFER_SIZE;

                    // Split off the written part
                    //@ assert Functions.countElementSplit(values, begin, write - Buffers.BUFFER_SIZE, write);

                    // Show this here to reduce the dependency contracts needed, verified
                    /*@ assert (\forall int element; true;
                      @     \old(Classifier.countElement(values, begin, old_write, i, end, buffers, element)) ==
                      @          Classifier.countElement(values, begin, write, i + j, end, buffers, element)
                      @ );
                      @*/

                    bucket_starts[bucket] += Buffers.BUFFER_SIZE;
                    //@ assert \invariant_for(this) && \disjoint(values[*], bucket_starts[*], buffers.buffer[*], buffers.indices[*], this.footprint, indices[*]);
                    //@ assert this.isClassOfSeq(\dl_seq_def_workaround(write - Buffers.BUFFER_SIZE, write, values), bucket);
                }
            }
            buffers.push(bucket, value);
            //@ assert \invariant_for(this) && \disjoint(values[*], bucket_starts[*], buffers.buffer[*], buffers.indices[*], this.footprint, indices[*]);
            // permutation property: elements in [begin,write) stayed the same, split first in [read,end), split on element = value
        }

        return write;
    }

    /*@ public normal_behaviour
      @ requires \invariant_for(buffers);
      @
      @ requires bucket_starts.length >= this.num_buckets + 1;
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires (\forall int b; 0 <= b < this.num_buckets; bucket_starts[b] == 0);
      @ requires buffers.isEmpty();
      @ requires \disjoint(values[*], bucket_starts[*], buffers.buffer[*], buffers.indices[*], this.footprint);
      @ requires buffers.num_buckets == this.num_buckets;
      @
      @ ensures \invariant_for(buffers);
      @
      @ // classifies until end - (end - begin) % BATCH_SIZE
      @
      @ ensures begin <= \result && \result <= (end - (end - begin) % BATCH_SIZE) && Functions.isAlignedTo(\result - begin, Buffers.BUFFER_SIZE);
      @ ensures this.isClassifiedUntil(values, begin, \result, end - (end - begin) % BATCH_SIZE, bucket_starts, buffers);
      @ ensures (\forall int element; true;
      @     \old(Classifier.countElement(values, begin, begin, begin, end, buffers, element)) ==
      @          Classifier.countElement(values, begin, \result, end - (end - begin) % BATCH_SIZE, end, buffers, element)
      @ );
      @
      @ assignable values[begin..end - (end - begin) % BATCH_SIZE - 1];
      @ assignable bucket_starts[0..this.num_buckets - 1];
      @ assignable buffers.indices[0..this.num_buckets - 1], buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
      @*/
    public int classify_locally_batched(int[] values, int begin, int end, int[] bucket_starts, Buffers buffers) {
        int write = begin;
        int i = begin;

        /*@ assert
          @     this.isClassifiedUntil(values, begin, write, i, bucket_starts, buffers) &&
          @     (\forall int element; true;
          @         \old(Classifier.countElement(values, begin, begin, begin, end, buffers, element)) ==
          @              Classifier.countElement(values, begin, write, i, end, buffers, element)
          @     );
          @*/
        if (end - begin >= BATCH_SIZE) {
            int cutoff = end - BATCH_SIZE;
            final int[] indices = new int[BATCH_SIZE];

            /*@ loop_invariant begin <= i && i <= end - (end - begin) % BATCH_SIZE;
              @
              @ loop_invariant begin <= write && write <= i;
              @ loop_invariant Functions.isAlignedTo(i - begin, BATCH_SIZE);
              @ loop_invariant Functions.isAlignedTo(write - begin, Buffers.BUFFER_SIZE);
              @
              @ // Bucket starts contain all elements in values[..write]
              @ loop_invariant this.isClassifiedUntil(values, begin, write, i, bucket_starts, buffers);
              @
              @ loop_invariant \disjoint(values[*], bucket_starts[*], buffers.buffer[*], buffers.indices[*], this.footprint, indices[*]);
              @
              @ loop_invariant (\forall int element; true;
              @     \old(Classifier.countElement(values, begin, begin, begin, end, buffers, element)) ==
              @          Classifier.countElement(values, begin, write, i, end, buffers, element)
              @ );
              @
              @ loop_invariant \invariant_for(buffers) && \invariant_for(this);
              @
              @ decreases end - i;
              @
              @ assignable buffers.indices[0..this.num_buckets - 1], buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
              @ assignable values[begin..end - (end - begin) % BATCH_SIZE - 1];
              @ assignable bucket_starts[0..this.num_buckets - 1];
              @ assignable indices[*];
              @*/
            while (i <= cutoff) {
                this.classify_all(values, i, i + BATCH_SIZE, indices);

                write = this.finish_batch(indices, values, begin, write, i, end, bucket_starts, buffers);

                i += BATCH_SIZE;
            }
            //@ assert i == end - (end - begin) % BATCH_SIZE;
        }

        return write;
    }

    /*@ public normal_behaviour
      @ requires \invariant_for(buffers);
      @
      @ requires bucket_starts.length >= this.num_buckets + 1;
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires \disjoint(values[*], bucket_starts[*], buffers.buffer[*], buffers.indices[*], this.footprint);
      @ requires buffers.num_buckets == this.num_buckets;
      @ requires this.isClassifiedUntil(values, begin, write, end, bucket_starts, buffers);
      @ requires begin <= write <= end;
      @ requires Functions.isAlignedTo(write - begin, Buffers.BUFFER_SIZE);
      @
      @ ensures Functions.isValidBucketStarts(bucket_starts, this.num_buckets) && bucket_starts[this.num_buckets] == end - begin;
      @
      @ assignable bucket_starts[0..this.num_buckets];
      @*/
    public void calculate_bucket_starts(int[] values, int begin, int write, int end, int[] bucket_starts, Buffers buffers) {
        // bucket_starts contains the bucket counts without buffer contents
        // Calculate bucket starts
        int sum = 0;

        /*@ loop_invariant 0 <= j && j <= this.num_buckets;
          @ loop_invariant sum == this.allElementsInRangeAndBuffersLT(values, begin, write, buffers, j);
          @ loop_invariant Functions.isSortedSlice(bucket_starts, 0, j);
          @ loop_invariant (\forall int b; j <= b < this.num_buckets; bucket_starts[b] == \old(bucket_starts[b]));
          @ loop_invariant (\forall int b; 0 <= b < j; bucket_starts[b] == this.allElementsInRangeAndBuffersLT(values, begin, write, buffers, b));
          @ loop_invariant j > 0 ==> sum >= this.allElementsInRangeAndBuffersLT(values, begin, write, buffers, j - 1);
          @
          @ decreases this.num_buckets - j;
          @
          @ assignable bucket_starts[0..this.num_buckets];
          @*/
        for (int j = 0; j < this.num_buckets; ++j) {
            // Add the partially filled buffers
            int size = bucket_starts[j] + buffers.len(j);


            // Exclusive prefix sum
            bucket_starts[j] = sum;
            sum += size;
            //@ assert size >= 0;
        }
        bucket_starts[this.num_buckets] = sum;

        //@ assert sum == end - begin && Functions.isSortedSlice(bucket_starts, 0, this.num_buckets + 1);
    }

    /*@ public normal_behaviour
      @ requires \invariant_for(buffers);
      @
      @ requires bucket_starts.length >= this.num_buckets + 1;
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires (\forall int b; 0 <= b < this.num_buckets; bucket_starts[b] == 0);
      @ requires buffers.isEmpty();
      @ requires \disjoint(values[*], bucket_starts[*], buffers.buffer[*], buffers.indices[*], this.footprint);
      @ requires buffers.num_buckets == this.num_buckets;
      @
      @ ensures begin <= \result && \result <= end && Functions.isAlignedTo(\result - begin, Buffers.BUFFER_SIZE);
      @ ensures this.isClassifiedBlocksRange(values, begin, \result);
      @ ensures buffers.isClassifiedWith(this);
      @ ensures Functions.isValidBucketStarts(bucket_starts, this.num_buckets) && bucket_starts[this.num_buckets] == end - begin;
      @ ensures (\forall int i; true;
      @     \old(Classifier.countElement(values, begin, begin, begin, end, buffers, i)) ==
      @          Classifier.countElement(values, begin, \result, end, end, buffers, i)
      @ );
      @ ensures \invariant_for(buffers);
      @
      @ // All values are either in a buffer or in values[..\result]
      @ // Bucket starts
      @
      @ assignable values[begin..end - 1];
      @ assignable bucket_starts[0..this.num_buckets];
      @ assignable buffers.indices[0..this.num_buckets - 1], buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
      @*/
    public int classify_locally(int[] values, int begin, int end, int[] bucket_starts, Buffers buffers) {
        int write = this.classify_locally_batched(values, begin, end, bucket_starts, buffers);
        int i = end - (end - begin) % BATCH_SIZE;
        //@ assert end - i >= 0;
        int[] indices = new int[end - i];
        this.classify_all(values, i, end, indices);
        write = this.finish_batch(indices, values, begin, write, i, end, bucket_starts, buffers);

        this.calculate_bucket_starts(values, begin, write, end, bucket_starts, buffers);
        //@ assert bucket_starts[this.num_buckets] == end - begin;
        return write;
    }
}
