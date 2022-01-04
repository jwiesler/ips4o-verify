package de.wiesler;

public class Classifier {
    public static final int STORAGE_SIZE = (1 << Constants.LOG_MAX_BUCKETS);

    private final Tree tree;
    private final int num_buckets;
    private final int[] sorted_splitters;
    private final boolean equal_buckets;

    /*@ public invariant Functions.isBetweenInclusive(this.num_buckets, 2, Constants.MAX_BUCKETS);
      @ public invariant this.num_buckets == (1 << (this.tree.log_buckets + Constants.toInt(this.equal_buckets)));
      @ invariant (1 << this.tree.log_buckets) <= this.sorted_splitters.length;
      @ invariant Functions.isSortedSlice(this.sorted_splitters, 0, (1 << this.tree.log_buckets));
      @ invariant this.sorted_splitters[this.num_buckets - 1] == this.sorted_splitters[this.num_buckets - 2];
      @*/

    /*@ public model_behaviour
      @ requires true;
      @ model boolean doesNotAlias(int[] array) {
      @     return array != this.sorted_splitters && this.tree.doesNotAlias(array);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @ model boolean isBucketIndex(int bucket) {
      @     return Functions.isBetweenInclusive(bucket, 0, this.num_buckets - 1);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires this.isBucketIndex(bucket);
      @ model boolean isClassified(int value, int bucket) {
      @     return true;
      @ }
      @*/

    /*@ public model_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ model boolean isClassifiedBlock(int[] values, int begin, int end) {
      @     return (\exists int bucket; this.isBucketIndex(bucket);
      @         (\forall
      @              int i;
      @              begin <= i && i < end;
      @              this.isClassified(values[i], bucket))
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires Functions.isAlignedTo(end - begin, block_size);
      @ model boolean isClassifiedBlocksRange(int[] values, int begin, int end, int block_size) {
      @     return (\forall
      @         int block;
      @         0 <= block && block < (end - begin) / block_size;
      @         this.isClassifiedBlock(values, begin + block * block_size, begin + (block + 1) * block_size)
      @     );
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires tree != sorted_splitters;
      @ requires Functions.isBetweenInclusive(log_buckets, 1, Constants.LOG_MAX_BUCKETS);
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
        sorted_splitters[num_splitters] = sorted_splitters[num_splitters - 1];

        this.tree = new Tree(sorted_splitters, tree, log_buckets);
        this.sorted_splitters = sorted_splitters;
        this.num_buckets = num_buckets << Constants.toInt(equal_buckets);
        this.equal_buckets = equal_buckets;
    }

    /*@ public normal_behaviour
      @ requires Functions.isSortedSlice(splitters, 0, num_splitters);
      @ requires splitters != tree;
      @
      @ requires 1 <= num_splitters && num_splitters <= num_buckets - 1;
      @ requires 2 <= num_buckets && num_buckets <= (1 << Constants.LOG_MAX_BUCKETS);
      @ requires splitters.length == Classifier.STORAGE_SIZE;
      @ requires tree.length == Classifier.STORAGE_SIZE;
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

    public /*@ strictly_pure */ int num_buckets() {
        return this.num_buckets;
    }

    public /*@ strictly_pure */ boolean equal_buckets() {
        return this.equal_buckets;
    }

    /*@ public normal_behaviour
      @ ensures this.isBucketIndex(\result);
      @ ensures this.isClassified(value, \result);
      @ assignable \strictly_nothing;
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
      @ ensures (\forall int i; 0 <= i && i < indices.length; this.isBucketIndex(indices[i]));
      @ ensures (\forall int i; 0 <= i && i < indices.length; this.isClassified(values[begin + i], indices[i]));
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

    /*@
      @ public model_behaviour
      @ requires true;
      @ model boolean exactlyNElementsInBuffers(Buffers buffers, int count) {
      @     return count == (\sum int bucket; this.isBucketIndex(bucket); buffers.indices[bucket]);
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires bucket_starts.length >= this.num_buckets + 1;
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires (\forall int i; 0 <= i < this.num_buckets; bucket_starts[i] == 0);
      @ requires buffers.isEmpty();
      @ requires this.doesNotAlias(values) &&
      @     buffers.doesNotAlias(values) &&
      @     this.doesNotAlias(bucket_starts) &&
      @     buffers.doesNotAlias(bucket_starts) &&
      @     this.doesNotAlias(buffers.buffer) &&
      @     this.doesNotAlias(buffers.indices) && values != bucket_starts;
      @
      @ ensures begin <= \result && \result <= end && Functions.isAlignedTo(\result - begin, Buffers.BUFFER_SIZE);
      @ ensures this.isClassifiedBlocksRange(values, begin, \result, Buffers.BUFFER_SIZE);
      @ ensures buffers.isClassifiedWith(this);
      @ ensures Functions.isValidBucketStarts(bucket_starts, this.num_buckets) && bucket_starts[this.num_buckets] == end - begin;
      @
      @ // All values are either in a buffer or in values[..\result]
      @ // Bucket starts
      @
      @ assignable values[begin..end - 1];
      @ assignable bucket_starts[0..this.num_buckets];
      @ assignable buffers.indices[0..this.num_buckets - 1], buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
      @*/
    public int classify_locally(int[] values, int begin, int end, int[] bucket_starts, Buffers buffers) {
        int write = begin;

        {
            final int BATCH_SIZE = 16;
            int i = begin;

            /*@ normal_behaviour
              @ ensures begin <= i && i <= end;
              @ ensures end - i <= BATCH_SIZE;
              @ ensures begin <= write && write <= i;
              @ ensures Functions.isAlignedTo(write - begin, Buffers.BUFFER_SIZE);
              @
              @ // Bucket starts contain all elements in values[..write]
              @ ensures (\forall int j; 0 <= j && j < this.num_buckets; bucket_starts[j] == (\num_of int k; begin <= k && k < write; this.isClassified(values[k], j)));
              @ // values[..write] is block classified
              @ ensures isClassifiedBlocksRange(values, begin, write, Buffers.BUFFER_SIZE);
              @ ensures this.exactlyNElementsInBuffers(buffers, i -  write);
              @
              @ assignable values[begin..end - 1];
              @ assignable bucket_starts[0..this.num_buckets - 1];
              @ assignable buffers.indices[0..this.num_buckets - 1], buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
              @*/
            {
                if (end - begin > BATCH_SIZE) {
                    int cutoff = end - BATCH_SIZE;
                    final int[] indices = new int[BATCH_SIZE];

                    /*@
                      @ loop_invariant begin <= i && i <= cutoff;
                      @ loop_invariant begin <= write && write <= i;
                      @ loop_invariant Functions.isAlignedTo(i - begin, BATCH_SIZE);
                      @ loop_invariant Functions.isAlignedTo(write - begin, Buffers.BUFFER_SIZE);
                      @
                      @ // Bucket starts contain all elements in values[..write]
                      @ loop_invariant (\forall int j; 0 <= j && j < this.num_buckets; bucket_starts[j] == (\num_of int k; begin <= k && k < write; this.isClassified(values[k], j)));
                      @
                      @ // values[..write] is block classified
                      @ loop_invariant isClassifiedBlocksRange(values, begin, write, Buffers.BUFFER_SIZE);
                      @
                      @ loop_invariant this.exactlyNElementsInBuffers(buffers, i - write);
                      @
                      @ // All elements in values[..write] or buffers or values[i..end]
                      @
                      @
                      @ decreases cutoff - i;
                      @
                      @ assignable values[begin..end - 1];
                      @ assignable bucket_starts[0..this.num_buckets - 1];
                      @ assignable indices[*];
                      @*/
                    while (i <= cutoff) {
                        this.classify_all(values, i, i + BATCH_SIZE, indices);

                        /*@
                          @ loop_invariant 0 <= j && j <= indices.length;
                          @
                          @ loop_invariant begin <= write && write <= i;
                          @ loop_invariant Functions.isAlignedTo(write - begin, Buffers.BUFFER_SIZE);
                          @
                          @ // Bucket starts contain all full blocks already flushed
                          @ // All elements in values[..write] or buffers or values[i + j..end]
                          @ // values[..write] is block classified
                          @ loop_invariant this.exactlyNElementsInBuffers(buffers, write - begin);
                          @
                          @ decreases indices.length - j;
                          @
                          @ assignable buffers.indices[0..this.num_buckets - 1], buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
                          @ assignable values[begin..end - 1];
                          @ assignable bucket_starts[0..this.num_buckets - 1];
                          @*/
                        for (int j = 0; j < indices.length; ++j) {
                            int bucket = indices[j];
                            int value = values[i + j];
                            if (buffers.push(value, bucket, values, write, end)) {
                                write += Buffers.BUFFER_SIZE;
                                bucket_starts[bucket] += Buffers.BUFFER_SIZE;
                            }
                        }

                        i += BATCH_SIZE;
                    }
                }
            }
            /*@
              @ loop_invariant begin <= i && i <= end;
              @ loop_invariant begin <= write && write <= i;
              @ loop_invariant Functions.isAlignedTo(write - begin, Buffers.BUFFER_SIZE);
              @ loop_invariant (\forall int j; 0 <= j && j < this.num_buckets; bucket_starts[j] == (\num_of int k; begin <= k && k < write; this.isClassified(values[k], j)));
              @
              @ // All elements in values[..write] or buffers or values[i..end]
              @ // values[..write] is block classified
              @ loop_invariant isClassifiedBlocksRange(values, begin, write, Buffers.BUFFER_SIZE);
              @
              @ decreases i - end;
              @
              @ assignable buffers.indices[0..this.num_buckets - 1], buffers.buffer[0..Buffers.BUFFER_SIZE * this.num_buckets - 1];
              @ assignable values[begin..end - 1];
              @ assignable bucket_starts[0..this.num_buckets - 1];
              @*/
            for (; i < end; ++i) {
                int value = values[i];
                int bucket = this.classify(value);
                if (buffers.push(value, bucket, values, write, end)) {
                    write += Buffers.BUFFER_SIZE;
                    bucket_starts[bucket] += Buffers.BUFFER_SIZE;
                }
            }
        }

        {
            // bucket_starts contains the bucket counts without buffer contents
            // Calculate bucket starts
            int sum = 0;
            /*@
              @ loop_invariant 0 <= i && i <= this.num_buckets;
              @ // bucket_starts[..i] is a prefix sum? contains what?
              @ // loop_invariant (\forall int j; 0 <= j < i; bucket_starts[j] == );
              @
              @ decreases i - end;
              @
              @ assignable bucket_starts[0..this.num_buckets - 1];
              @*/
            for (int i = 0; i < this.num_buckets; ++i) {
                // Add the partially filled buffers
                int size = bucket_starts[i] + buffers.len(i);

                // Exclusive prefix sum
                bucket_starts[i] = sum;
                sum += size;
            }
            bucket_starts[this.num_buckets] = sum;

            assert (sum == end - begin);
        }
        return write;
    }
}
