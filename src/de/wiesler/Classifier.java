package de.wiesler;

public class Classifier {
    public static final int STORAGE_SIZE = (1 << Constants.LOG_MAX_BUCKETS);

    private final Tree tree;
    private final int num_buckets;
    private final int[] sorted_splitters;
    private final boolean equal_buckets;

    /*@
      @ invariant this.sorted_splitters.length == Classifier.STORAGE_SIZE;
      @ invariant Functions.isBetweenInclusive(this.num_buckets, 0, Constants.MAX_BUCKETS - 1);
      @ // invariant Functions.isSortedSlice(this.sorted_splitters, ;
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
      @ requires tree.length == Classifier.STORAGE_SIZE;
      @ requires sorted_splitters.length == Classifier.STORAGE_SIZE;
      @
      @ assignable sorted_splitters[*], tree[*];
      @*/
    public Classifier(int[] sorted_splitters, int[] tree, int log_buckets, boolean equal_buckets) {
        assert (log_buckets <= Constants.LOG_MAX_BUCKETS + 1);
        int num_buckets = 1 << log_buckets;

        int num_splitters = num_buckets - 1;
        sorted_splitters[num_splitters] = sorted_splitters[num_splitters - 1];
        if (equal_buckets) {
            num_buckets = 2 * num_buckets;
        }

        this.tree = new Tree(sorted_splitters, tree, log_buckets);
        this.sorted_splitters = sorted_splitters;
        this.num_buckets = num_buckets;
        this.equal_buckets = equal_buckets;
    }

    /*@ public normal_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires Functions.isSortedSlice(values, begin, end);
      @ requires values != target;
      @
      @ requires target.length >= count;
      @
      @ requires count > 0;
      @ requires step > 0;
      @ requires begin + count * step - 1 < end;
      @
      @ ensures (\forall
      @     int i;
      @     0 <= i < \result;
      @     // It is from the source array
      @     // (\exists int j; begin <= j < end; values[j] == target[i]) &&
      @     // It is unique in the target array (or: strictly ascending)
      @     (i > 0 ==> target[i - 1] < target[i])
      @ );
      @ ensures Functions.isValidSlice(target, 0, \result);
      @
      @ assignable target[0..count - 1];
      @*/
    private static int copy_unique(
            int[] values,
            int begin,
            int end,
            int count,
            int step,
            int[] target
    ) {
        int offset = begin + step - 1;
        target[0] = values[offset];
        int target_offset = 1;
        offset += step;

        /*@
          @ loop_invariant 1 <= i && i <= count;
          @ loop_invariant 1 <= target_offset && target_offset <= i;
          @
          @ loop_invariant begin <= offset;
          @ loop_invariant offset == begin + (step * (i + 1)) - 1;
          @ loop_invariant i < count ==> offset < end;
          @
          @ // loop_invariant (\forall
          @ //     int j;
          @ //     0 <= j < target_offset;
          @ //     // It is from the source array
          @ //     (\exists int k; begin <= k < end; values[k] == target[j])
          @ // );
          @ loop_invariant (\forall
          @     int j;
          @     0 <= j < target_offset - 1;
          @     // It is unique in the target array (or: strictly ascending)
          @     target[j] < target[j + 1]
          @ );
          @
          @ decreases count - i;
          @ assignable target[1..count - 1];
          @*/
        for (int i = 1; i < count; ++i) {
            if (Constants.cmp(target[target_offset - 1], values[offset])) {
                target[target_offset] = values[offset];
                target_offset += 1;
            }
            offset += step;
        }

        return target_offset;
    }

    /*@ public normal_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires Functions.isSortedSlice(values, begin, end);
      @ requires splitters != tree && values != tree && values != splitters;
      @
      @ requires 0 < step && 1 < num_buckets && num_buckets <= (1 << Constants.LOG_MAX_BUCKETS);
      @ requires splitters.length == Classifier.STORAGE_SIZE;
      @ requires tree.length == Classifier.STORAGE_SIZE;
      @
      @ requires begin + (num_buckets - 1) * step + 1 <= end;
      @
      @ assignable splitters[*], tree[*];
      @*/
    public static /*@ nullable */ Classifier from_sorted_samples(
            int[] values,
            int begin,
            int end,
            int[] splitters,
            int[] tree,
            int num_buckets,
            int step
    ) {
        int max_splitters = num_buckets - 1;
        // Select num_buckets - 1 splitters
        int splitter_count = copy_unique(values, begin, end, max_splitters, step, splitters);

        if (splitter_count == 0) {
            return null;
        }

        // Check for duplicate splitters
        boolean use_equal_buckets = (max_splitters - splitter_count) >= Constants.EQUAL_BUCKETS_THRESHOLD;

        // Fill the array to the next power of two
        int log_buckets = Constants.log2(splitter_count) + 1;
        int actual_num_buckets = 1 << log_buckets;
        assert (actual_num_buckets <= splitters.length);
        assert (splitter_count < actual_num_buckets);

        /*@
          @ loop_invariant splitter_count <= i && i <= actual_num_buckets;
          @
          @ loop_invariant (\forall
          @     int j;
          @     0 <= j < i;
          @     // It is from the source array
          @     (\exists int k; begin <= k < end; values[k] == splitters[j]) &&
          @     // Sorted
          @     j > 0 ==> splitters[j - 1] <= splitters[j]
          @ );
          @
          @ decreases actual_num_buckets - i;
          @ assignable splitters[splitter_count..actual_num_buckets - 1];
          @*/
        for (int i = splitter_count; i < actual_num_buckets; ++i) {
            splitters[i] = splitters[splitter_count - 1];
        }

        Functions.fill(tree, 0, tree.length, 0);
        return new Classifier(splitters, tree, log_buckets, use_equal_buckets);
    }

    public int num_buckets() {
        return this.num_buckets;
    }

    public boolean equal_buckets() {
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
        assert (this.num_buckets == 1 << (this.tree.log_buckets() + Constants.toInt(this.equal_buckets)));

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
      @ requires bucket_starts.length == Constants.MAX_BUCKETS + 1;
      @ requires buckets_count > 0 && buckets_count <= bucket_starts.length;
      @ static model boolean validBucketStarts(int[] bucket_starts, int buckets_count, int values_len) {
      @     return (\forall int i; 1 <= i < buckets_count; bucket_starts[i - 1] <= bucket_starts[i]) &&
      @         (bucket_starts[buckets_count - 1] == values_len);
      @ }
      @*/

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
      @ requires (\forall int i; 0 <= i < this.num_buckets; buffers.indices[i] == 0);
      @ requires this.doesNotAlias(values) &&
      @     buffers.doesNotAlias(values) &&
      @     this.doesNotAlias(bucket_starts) &&
      @     buffers.doesNotAlias(bucket_starts) &&
      @     this.doesNotAlias(buffers.buffer) &&
      @     this.doesNotAlias(buffers.indices) && values != bucket_starts;
      @
      @ ensures begin <= \result && \result <= end && Functions.isAlignedTo(\result - begin, Buffers.BUFFER_SIZE);
      @ ensures this.isClassifiedBlocksRange(values, begin, \result, Buffers.BUFFER_SIZE);
      @ ensures Classifier.validBucketStarts(bucket_starts, this.num_buckets, end - begin);
      @
      @ // All values are either in a buffer or in values[..\result]
      @ // Bucket starts
      @
      @ assignable values[begin..end];
      @ assignable bucket_starts[0..this.num_buckets];
      @ assignable buffers.indices[0..this.num_buckets], buffers.buffer[*];
      @*/
    public int classify_locally(int[] values, int begin, int end, int[] bucket_starts, Buffers buffers) {
        int write = begin;

        {
            final int BATCH_SIZE = 16;
            int i = begin;
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
                  @ loop_invariant this.exactlyNElementsInBuffers(buffers, write - begin);
                  @
                  @ // All elements in values[..write] or buffers or values[i..end]
                  @
                  @
                  @ decreases cutoff - i;
                  @
                  @ assignable values[write..i];
                  @ assignable bucket_starts[0..this.num_buckets()];
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
                      @ assignable values[write..i];
                      @ assignable bucket_starts[*];
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
              @ assignable values[write..i];
              @ assignable bucket_starts[*];
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
              @ assignable sum;
              @ assignable bucket_starts[*];
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
