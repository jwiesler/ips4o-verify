package de.wiesler;

public final class BucketPointers {
    // 2 * n integer (read, write)
    private /*@ spec_public @*/ final int[] buffer;

    //@ ghost final int num_buckets;
    //@ ghost final \seq bucket_starts;
    //@ ghost final int first_empty_position;

    //@ public instance invariant_free 0 <= 2 * this.num_buckets <= this.buffer.length;
    //@ public instance invariant_free 0 <= this.first_empty_position <= (int) this.bucket_starts[num_buckets] <= Buffers.MAX_LEN && Buffers.isBlockAligned(this.first_empty_position);
    //@ public instance invariant_free this.bucket_starts.length == this.num_buckets + 1;
    //@ public instance invariant_free (int) this.bucket_starts[0] == 0 && Functions.isSortedSeqTransitive(this.bucket_starts);
    //@ public instance invariant_free (\forall int b; 0 <= b < this.num_buckets; this.isValidBucketPointer(b));
    //@ accessible \inv: this.buffer[*];

    /*@ model_behaviour
      @     requires true;
      @ model boolean isValidBucketPointer(int bucket) {
      @     return this.bucketStart(bucket) <= this.buffer[2 * bucket] <= this.bucketStart(bucket + 1) &&
      @         this.bucketStart(bucket) <= this.buffer[2 * bucket + 1] <= this.bucketStart(bucket + 1) &&
      @         (this.bucketStart(bucket) == this.buffer[2 * bucket] || this.buffer[2 * bucket] <= this.first_empty_position) &&
      @         Buffers.isBlockAligned(this.buffer[2 * bucket]) &&
      @         Buffers.isBlockAligned(this.buffer[2 * bucket + 1]);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket <= this.num_buckets;
      @ requires \invariant_for(this);
      @
      @ ensures_free 0 <= \result <= this.bucketStart(this.num_buckets) <= Buffers.MAX_LEN;
      @ ensures_free Buffers.isBlockAligned(\result);
      @ ensures_free bucket < this.num_buckets ==> \result <= this.bucketStart(bucket + 1);
      @ ensures_free 0 < bucket <= this.num_buckets ==> this.bucketStart(bucket - 1) <= \result;
      @
      @ // final only no_state
      @ model int bucketStart(int bucket) {
      @     return Buffers.blockAligned((int) this.bucket_starts[bucket]);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ requires \invariant_for(this);
      @
      @ ensures_free \result >= 0;
      @ ensures_free Buffers.isBlockAligned(\result);
      @
      @ // final only no_state
      @ model int bucketSize(int bucket) {
      @     return this.bucketStart(bucket + 1) - this.bucketStart(bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @
      @ ensures_free 0 <= this.bucketStart(bucket) <= \result <= this.bucketStart(bucket + 1) <= this.bucketStart(this.num_buckets);
      @ ensures_free \result <= this.first_empty_position || \result == this.bucketStart(bucket);
      @ ensures_free this.first_empty_position <= this.bucketStart(this.num_buckets);
      @ ensures_free Buffers.isBlockAligned(\result);
      @
      @ accessible this.buffer[2 * bucket];
      @ model int lastReadOf(int bucket) {
      @     return this.buffer[2 * bucket];
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @
      @ ensures_free 0 <= this.bucketStart(bucket) <= \result <= this.bucketStart(bucket + 1) <= this.bucketStart(this.num_buckets);
      @ ensures_free Buffers.isBlockAligned(\result);
      @
      @ accessible this.buffer[2 * bucket + 1];
      @ model int nextWriteOf(int bucket) {
      @     return this.buffer[2 * bucket + 1];
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @
      @ accessible this.buffer[2 * bucket + 1];
      @ model int writtenCountOfBucket(int bucket) {
      @     return this.nextWriteOf(bucket) - this.bucketStart(bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @
      @ accessible this.buffer[2 * bucket + 1];
      @ model int remainingWriteCountOfBucket(int bucket) {
      @     return this.bucketStart(bucket + 1) - this.nextWriteOf(bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @
      @ ensures_free \result >= 0;
      @ ensures_free Buffers.isBlockAligned(\result);
      @
      @ accessible this.buffer[2 * bucket], this.buffer[2 * bucket + 1];
      @ model int toReadCountOfBucket(int bucket) {
      @     return this.nextWriteOf(bucket) < this.lastReadOf(bucket) ? this.lastReadOf(bucket) - this.nextWriteOf(bucket) : 0;
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ requires overflow.length == Buffers.BUFFER_SIZE;
      @ requires \invariant_for(classifier);
      @
      @ accessible values[begin + this.bucketStart(bucket) .. begin + this.nextWriteOf(bucket) - 1], overflow[*], this.buffer[2 * bucket + 1], classifier.sorted_splitters[*], classifier.tree.tree[*];
      @ model boolean writtenElementsOfBucketClassified(Classifier classifier, int[] values, int begin, int end, int[] overflow, int bucket) {
      @     return end - begin < this.nextWriteOf(bucket) && Buffers.BUFFER_SIZE <= this.writtenCountOfBucket(bucket) ?
      @         classifier.isClassOfSlice(values, begin + this.bucketStart(bucket), begin + this.nextWriteOf(bucket) - Buffers.BUFFER_SIZE, bucket) &&
      @             classifier.isClassOfSlice(overflow, 0, Buffers.BUFFER_SIZE, bucket) :
      @         classifier.isClassOfSlice(values, begin + this.bucketStart(bucket), begin + this.nextWriteOf(bucket), bucket);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ requires \invariant_for(classifier);
      @
      @ accessible values[begin + this.nextWriteOf(bucket) .. begin + this.lastReadOf(bucket) - 1], this.buffer[2 * bucket..2 * bucket + 1], classifier.sorted_splitters[*], classifier.tree.tree[*];
      @ model boolean elementsToReadOfBucketBlockClassified(Classifier classifier, int[] values, int begin, int end, int bucket) {
      @     return this.nextWriteOf(bucket) < this.lastReadOf(bucket) ==> classifier.isClassifiedBlocksRange(values, begin + this.nextWriteOf(bucket), begin + this.lastReadOf(bucket));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ requires overflow.length == Buffers.BUFFER_SIZE;
      @
      @ accessible values[begin + this.bucketStart(bucket) .. begin + this.nextWriteOf(bucket) - 1], overflow[*], this.buffer[2 * bucket + 1];
      @ model int writtenElementsOfBucketCountElement(int[] values, int begin, int end, int[] overflow, int bucket, int element) {
      @     return end - begin < this.nextWriteOf(bucket) && Buffers.BUFFER_SIZE <= this.writtenCountOfBucket(bucket) ?
      @         Functions.countElement(values, begin + this.bucketStart(bucket), begin + this.nextWriteOf(bucket) - Buffers.BUFFER_SIZE, element) +
      @             Functions.countElement(overflow, 0, Buffers.BUFFER_SIZE, element) :
      @         Functions.countElement(values, begin + this.bucketStart(bucket), begin + this.nextWriteOf(bucket), element);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @
      @ accessible values[begin + this.nextWriteOf(bucket) .. begin + this.lastReadOf(bucket) - 1], this.buffer[2 * bucket..2 * bucket + 1];
      @ model int elementsToReadOfBucketCountElement(int[] values, int begin, int end, int bucket, int element) {
      @     return Functions.countElement(values, begin + this.nextWriteOf(bucket), begin + this.lastReadOf(bucket), element);
      @ }
      @*/

    /*@ model_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires overflow.length == Buffers.BUFFER_SIZE;
      @
      @ model int countElement(int[] values, int begin, int end, int[] overflow, int element) {
      @     return this.elementsToReadCountElement(values, begin, end, element) +
      @         this.writtenElementsCountElement(values, begin, end, overflow, element);
      @ }
      @*/

    /*@ model_behaviour
      @ requires overflow.length == Buffers.BUFFER_SIZE;
      @
      @ model int writtenElementsCountElement(int[] values, int begin, int end, int[] overflow, int element) {
      @     return (\sum int b; 0 <= b < this.num_buckets;
      @         this.writtenElementsOfBucketCountElement(values, begin, end, overflow, b, element)
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= split_bucket < this.num_buckets;
      @ requires begin + this.bucketStart(split_bucket) <= begin + this.nextWriteOf(split_bucket) - Buffers.BUFFER_SIZE <= begin + this.nextWriteOf(split_bucket);
      @ ensures_free \result;
      @ model boolean writtenElementsCountElementSplitBucket(int[] values, int begin, int end, int[] overflow, int split_bucket) {
      @     return (\forall int element; true;
      @         this.writtenElementsCountElement(values, begin, end, overflow, element) ==
      @             (\sum int b; 0 <= b < this.num_buckets;
      @                 (b == split_bucket) ?
      @                     Functions.countElement(values, begin + this.bucketStart(split_bucket), begin + this.nextWriteOf(split_bucket) - Buffers.BUFFER_SIZE, element) :
      @                     this.writtenElementsOfBucketCountElement(values, begin, end, overflow, b, element)
      @             ) +
      @             (end - begin < this.nextWriteOf(split_bucket) && Buffers.BUFFER_SIZE <= this.writtenCountOfBucket(split_bucket) ?
      @                 Functions.countElement(overflow, 0, Buffers.BUFFER_SIZE, element) :
      @                 Functions.countElement(values, begin + this.nextWriteOf(split_bucket) - Buffers.BUFFER_SIZE, begin + this.nextWriteOf(split_bucket), element))
      @     );
      @ }
      @*/

    /*@ model_behaviour
      @ requires true;
      @
      @ model int elementsToReadCountElement(int[] values, int begin, int end, int element) {
      @     return (\sum int b; 0 <= b < this.num_buckets;
      @         this.elementsToReadOfBucketCountElement(values, begin, end, b, element)
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= split_bucket < this.num_buckets;
      @ requires begin + this.nextWriteOf(split_bucket) <= mid <= begin + this.lastReadOf(split_bucket);
      @ ensures_free \result;
      @ model boolean elementsToReadCountElementSplitBucket(int[] values, int begin, int mid, int end, int split_bucket, boolean pullout_first) {
      @     return (\forall int element; true;
      @         this.elementsToReadCountElement(values, begin, end, element) ==
      @             (\sum int b; 0 <= b < this.num_buckets; (b == split_bucket) ?
      @                 (pullout_first ?
      @                     Functions.countElement(values, mid, begin + this.lastReadOf(b), element) :
      @                     Functions.countElement(values, begin + this.nextWriteOf(b), mid, element)
      @                 ) :
      @                 this.elementsToReadOfBucketCountElement(values, begin, end, b, element)) +
      @             (pullout_first ?
      @                 Functions.countElement(values, begin + this.nextWriteOf(split_bucket), mid, element) :
      @                 Functions.countElement(values, mid, begin + this.lastReadOf(split_bucket), element)
      @             )
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ requires 0 <= begin <= end <= values.length;
      @ requires this.num_buckets == classifier.num_buckets;
      @ requires \invariant_for(classifier);
      @ ensures_free \result >= 0;
      @ accessible values[begin + this.nextWriteOf(bucket) .. begin + this.lastReadOf(bucket) - 1], this.buffer[2 * bucket..2 * bucket + 1], classifier.sorted_splitters[*], classifier.tree.tree[*];
      @ model int elementsToReadOfBucketCountClassEq(Classifier classifier, int[] values, int begin, int end, int bucket, int cls) {
      @     return classifier.countClassOfSliceEq(values, begin + this.nextWriteOf(bucket), begin + this.lastReadOf(bucket), cls);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ requires 0 <= begin <= end <= values.length;
      @ ensures_free \result >= 0;
      @ model int elementsToReadCountClassEq(Classifier classifier, int[] values, int begin, int end, int bucket) {
      @     return (\sum int b; 0 <= b < this.num_buckets;
      @         this.elementsToReadOfBucketCountClassEq(classifier, values, begin, end, b, bucket)
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= split_bucket < this.num_buckets;
      @ requires this.num_buckets == classifier.num_buckets;
      @ requires begin + this.nextWriteOf(split_bucket) <= mid <= begin + this.lastReadOf(split_bucket);
      @ ensures_free \result;
      @ model boolean elementsToReadCountClassEqSplitBucket(Classifier classifier, int[] values, int begin, int mid, int end, int split_bucket, boolean pullout_first) {
      @     return (\forall int bucket; 0 <= bucket < this.num_buckets;
      @         this.elementsToReadCountClassEq(classifier, values, begin, end, bucket) ==
      @             (\sum int b; 0 <= b < this.num_buckets; (b == split_bucket) ?
      @                 (pullout_first ?
      @                     classifier.countClassOfSliceEq(values, mid, begin + this.lastReadOf(b), bucket) :
      @                     classifier.countClassOfSliceEq(values, begin + this.nextWriteOf(b), mid, bucket)
      @                 ) :
      @                 this.elementsToReadOfBucketCountClassEq(classifier, values, begin, end, b, bucket)) +
      @             (pullout_first ?
      @                 classifier.countClassOfSliceEq(values, begin + this.nextWriteOf(split_bucket), mid, bucket) :
      @                 classifier.countClassOfSliceEq(values, mid, begin + this.lastReadOf(split_bucket), bucket)
      @             )
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ ensures_free \result;
      @ model boolean disjointBucketsLemma(int bucket) {
      @     return (\forall int b; 0 <= b < this.num_buckets && b != bucket;
      @         (b < bucket ==> this.bucketStart(b + 1) <= this.bucketStart(bucket)) &&
      @         (b > bucket ==> this.bucketStart(bucket + 1) <= this.bucketStart(b))
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= end;
      @ requires end - begin == (int) this.bucket_starts[num_buckets];
      @ ensures_free \result;
      @ model boolean overflowBucketCharacteristic(int begin, int end) {
      @     return (\forall int b; 0 <= b < this.num_buckets;
      @         end - begin < this.nextWriteOf(b) && Buffers.BUFFER_SIZE <= this.writtenCountOfBucket(b) ==>
      @             this.bucketStart(b) < end - begin &&
      @             this.nextWriteOf(b) == this.bucketStart(b + 1) &&
      @             this.bucketStart(b + 1) == this.bucketStart(this.num_buckets)
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= end;
      @ requires 0 <= bucket < this.num_buckets;
      @ requires end - begin == (int) this.bucket_starts[num_buckets];
      @ requires end - begin < this.nextWriteOf(bucket) && Buffers.BUFFER_SIZE <= this.writtenCountOfBucket(bucket);
      @ requires this.disjointBucketsLemma(bucket);
      @ requires this.overflowBucketCharacteristic(begin, end);
      @ ensures_free \result;
      @ model boolean overflowBucketUniqueLemma(int begin, int end, int bucket) {
      @     return (\forall int b; 0 <= b < this.num_buckets && b != bucket;
      @         // Show that nextWriteOf(bucket) == bucketStart(bucket) == bucketStart(num_buckets)
      @         // b > bucket: writtenCountOfBucket can't be > 0 since nextWriteOf(b) <= bucketStart(num_buckets)
      @         // b < bucket: bucketStart(bucket) <= end - begin
      @         !(end - begin < this.nextWriteOf(b) && Buffers.BUFFER_SIZE <= this.writtenCountOfBucket(b))
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @ requires begin + this.bucketStart(bucket) <= subBegin <= subEnd <= begin + this.bucketStart(bucket + 1);
      @ requires this.disjointBucketsLemma(bucket);
      @ ensures_free \result;
      @ model boolean disjointBucketsAreaLemma(int[] values, int begin, int end, int bucket, int subBegin, int subEnd) {
      @     return (\forall int b; 0 <= b < this.num_buckets && b != bucket;
      @         \disjoint(\dl_arrayRange(values, begin + this.bucketStart(b), begin + this.nextWriteOf(b) - 1), \dl_arrayRange(values, subBegin, subEnd - 1)) &&
      @         \disjoint(\dl_arrayRange(values, begin + this.nextWriteOf(b), begin + this.lastReadOf(b) - 1), \dl_arrayRange(values, subBegin, subEnd - 1))
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires start <= read <= stop;
      @ static model no_state boolean readIsMaximal(int start, int read, int stop, int first_empty_position) {
      @     return read == (first_empty_position <= start ? start : (stop <= first_empty_position ? stop : first_empty_position));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @
      @ accessible this.buffer[2 * bucket..2 * bucket + 1];
      @ model boolean isAtInitialBucketState(int bucket) {
      @     return this.writtenCountOfBucket(bucket) == 0 &&
      @         BucketPointers.readIsMaximal(this.bucketStart(bucket), this.lastReadOf(bucket), this.bucketStart(bucket + 1), this.first_empty_position);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @
      @ model boolean isAtInitialState() {
      @     return (\forall int b; 0 <= b < this.num_buckets;
      @         this.isAtInitialBucketState(b)
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires end - begin == (int) this.bucket_starts[num_buckets];
      @ requires this.isAtInitialState();
      @ requires classifier.isClassifiedBlocksRange(values, begin, begin + this.first_empty_position);
      @
      @ ensures_free \result;
      @
      @ model boolean initialReadAreasBlockClassified(Classifier classifier, int[] values, int begin, int end) {
      @     return (\forall int b; 0 <= b < this.num_buckets; this.elementsToReadOfBucketBlockClassified(classifier, values, begin, end, b));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires end - begin == (int) this.bucket_starts[num_buckets];
      @ requires this.isAtInitialState();
      @
      @ ensures_free \result;
      @
      @ model boolean initialReadAreasCountLemma(int[] values, int begin, int end) {
      @     return (\forall int iv; 0 <= iv <= this.num_buckets;
      @         (\forall int element; true;
      @             Functions.countElement(values, begin, begin + (this.bucketStart(iv) < first_empty_position ? this.bucketStart(iv) : first_empty_position), element) ==
      @                 (\sum int b; 0 <= b < iv; this.elementsToReadOfBucketCountElement(values, begin, end, b, element))
      @         )
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires this.initialReadAreasCountLemma(values, begin, end);
      @
      @ ensures_free \result;
      @
      @ model boolean initialReadAreasCount(int[] values, int begin, int end) {
      @     return (\forall int element; true;
      @             Functions.countElement(values, begin, begin + first_empty_position, element) ==
      @                 this.elementsToReadCountElement(values, begin, end, element)
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires end - begin == (int) this.bucket_starts[num_buckets];
      @ requires this.isAtInitialState();
      @
      @ ensures_free \result;
      @
      @ model boolean initialReadAreasCountBucketElementsLemma(Classifier classifier, int[] values, int begin, int end) {
      @     return (\forall int iv; 0 <= iv <= this.num_buckets;
      @         (\forall int bucket; 0 <= bucket < this.num_buckets;
      @             classifier.countClassOfSliceEq(values, begin, begin + (this.bucketStart(iv) < first_empty_position ? this.bucketStart(iv) : first_empty_position), bucket) ==
      @                 (\sum int b; 0 <= b < iv; this.elementsToReadOfBucketCountClassEq(classifier, values, begin, end, b, bucket))
      @         )
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires this.initialReadAreasCountBucketElementsLemma(classifier, values, begin, end);
      @
      @ ensures_free \result;
      @
      @ model boolean initialReadAreasCountBucketElements(Classifier classifier, int[] values, int begin, int end) {
      @     return (\forall int bucket; 0 <= bucket < this.num_buckets;
      @             classifier.countClassOfSliceEq(values, begin, begin + first_empty_position, bucket) ==
      @                 this.elementsToReadCountClassEq(classifier, values, begin, end, bucket)
      @     );
      @ }
      @*/

    /*@ model_behaviour
      @ requires_free 0 <= start <= stop <= Buffers.MAX_LEN;
      @ ensures_free \result;
      @ static model no_state boolean alignedBoundariesKeepEnoughSpace(int start, int stop) {
      @     return stop - start - Buffers.bufferSizeForBucketLen(stop - start) <= Buffers.blockAligned(stop) - Buffers.blockAligned(start);
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires_free Functions.isSortedSliceTransitive(bucket_starts, 0, num_buckets + 1);
      @ requires_free num_buckets + 1 <= bucket_starts.length;
      @ requires_free bucket_starts[num_buckets] <= Buffers.MAX_LEN;
      @ requires_free bucket_starts[0] == 0;
      @ requires_free 0 <= 2 * num_buckets <= buffer.length;
      @ requires_free 0 <= first_empty_position <= bucket_starts[num_buckets];
      @ requires_free Buffers.isBlockAligned(first_empty_position);
      @ requires_free \disjoint(bucket_starts[*], buffer[*]);
      @
      @ ensures_free this.num_buckets == num_buckets && this.buffer == buffer && this.first_empty_position == first_empty_position;
      @ ensures_free bucket_starts[num_buckets] == (int) this.bucket_starts[num_buckets];
      @ ensures_free this.isAtInitialState();
      @ ensures_free (\forall int b; 0 <= b < num_buckets;
      @     // enough space to write everything except the buffer content
      @     bucket_starts[b + 1] - bucket_starts[b] - Buffers.bufferSizeForBucketLen(bucket_starts[b + 1] - bucket_starts[b]) <= this.bucketSize(b)
      @ );
      @ ensures_free (\forall int b; 0 <= b <= num_buckets; this.bucketStart(b) == Buffers.blockAligned(bucket_starts[b]));
      @
      @ assignable_free buffer[0..2 * num_buckets - 1];
      @*/
    public BucketPointers(final int[] bucket_starts, final int num_buckets, final int first_empty_position, final int[] buffer) {
        //@ set this.num_buckets = num_buckets;
        //@ set this.first_empty_position = first_empty_position;
        //@ set this.bucket_starts = \dl_seq_def_workaround(0, num_buckets + 1, bucket_starts);

        /*@ assume
          @     (\forall int b; 0 <= b <= num_buckets; this.bucketStart(b) == Buffers.blockAligned(bucket_starts[b])) &&
          @     Functions.isSortedSeqTransitive(this.bucket_starts);
          @*/

        this.buffer = buffer;

        /*@ loop_invariant_free 0 <= bucket && bucket <= num_buckets;
          @ loop_invariant_free (\forall int b; 0 <= b < bucket;
          @     this.isValidBucketPointer(b) &&
          @     this.isAtInitialBucketState(b) &&
          @     bucket_starts[b + 1] - bucket_starts[b] - Buffers.bufferSizeForBucketLen(bucket_starts[b + 1] - bucket_starts[b]) <= this.bucketSize(b)
          @ );
          @
          @ decreases num_buckets - bucket;
          @
          @ assignable_free this.buffer[0..2 * num_buckets - 1];
          @*/
        for (int bucket = 0; bucket < num_buckets; ++bucket) {
            //@ assume 0 <= bucket_starts[bucket] <= bucket_starts[bucket + 1] <= bucket_starts[num_buckets];
            int start = Buffers.align_to_next_block(bucket_starts[bucket]);
            int stop = Buffers.align_to_next_block(bucket_starts[bucket + 1]);
            //@ assume start == this.bucketStart(bucket) && stop == this.bucketStart(bucket + 1) && start <= stop;
            int read = -1;

            /*@ normal_behaviour
              @ ensures_free start <= read <= stop;
              @ ensures_free Buffers.isBlockAligned(read);
              @ ensures_free BucketPointers.readIsMaximal(start, read, stop, this.first_empty_position);
              @
              @ assignable_free \strictly_nothing;
              @*/
            {
                if (first_empty_position <= start) {
                    read = start;
                } else if (stop <= first_empty_position) {
                    read = stop;
                } else {
                    read = first_empty_position;
                }
            }

            this.buffer[2 * bucket] = read;
            this.buffer[2 * bucket + 1] = start;

            //@ assume BucketPointers.alignedBoundariesKeepEnoughSpace(bucket_starts[bucket], bucket_starts[bucket + 1]);
        }
    }

    /*@ public normal_behaviour
      @ requires_free 0 <= bucket < this.num_buckets;
      @
      @ ensures_free \result == this.nextWriteOf(bucket);
      @ ensures_free \result == this.writtenCountOfBucket(bucket) + this.bucketStart(bucket);
      @
      @ assignable_free \strictly_nothing;
      @*/
    public int write(int bucket) {
        final int write_pos = 2 * bucket + 1;
        return this.buffer[write_pos];
    }

    /*@ public normal_behaviour
      @ requires_free 0 <= bucket < this.num_buckets;
      @ requires_free this.bucketSize(bucket) >= this.writtenCountOfBucket(bucket) + Buffers.BUFFER_SIZE;
      @
      @ ensures_free \old(this.nextWriteOf(bucket)) + Buffers.BUFFER_SIZE == this.nextWriteOf(bucket);
      @ ensures_free \old(this.remainingWriteCountOfBucket(bucket)) == this.remainingWriteCountOfBucket(bucket) + Buffers.BUFFER_SIZE;
      @ ensures_free \old(this.writtenCountOfBucket(bucket)) + Buffers.BUFFER_SIZE == this.writtenCountOfBucket(bucket);
      @ ensures_free this.lastReadOf(bucket) == \old(this.lastReadOf(bucket));
      @ // read count either decreased or stayed 0
      @ ensures_free \old(this.toReadCountOfBucket(bucket)) >= Buffers.BUFFER_SIZE ?
      @     this.toReadCountOfBucket(bucket) < \old(this.toReadCountOfBucket(bucket)) :
      @     this.toReadCountOfBucket(bucket) == 0;
      @
      @ ensures_free \result.position == \old(this.nextWriteOf(bucket));
      @ ensures_free \result.occupied <==> \old(this.toReadCountOfBucket(bucket)) >= Buffers.BUFFER_SIZE;
      @
      @ assignable_free this.buffer[2 * bucket + 1];
      @*/
    public Increment increment_write(int bucket) {
        final int read_pos = 2 * bucket;
        final int write_pos = 2 * bucket + 1;
        final int write = this.buffer[write_pos];
        this.buffer[write_pos] += Buffers.BUFFER_SIZE;
        return new Increment(this.buffer[read_pos] > write, write);
    }

    /*@ public normal_behaviour
      @ requires_free 0 <= bucket < this.num_buckets;
      @
      @ ensures_free \result <==> this.toReadCountOfBucket(bucket) >= Buffers.BUFFER_SIZE;
      @
      @ assignable_free \strictly_nothing;
      @*/
    public boolean hasRemainingRead(int bucket) {
        final int read_pos = 2 * bucket;
        final int write_pos = 2 * bucket + 1;
        int read = this.buffer[read_pos];
        final int write = this.buffer[write_pos];
        return read > write;
    }

    /*@ public normal_behaviour
      @ requires_free 0 <= bucket < this.num_buckets;
      @ requires_free this.toReadCountOfBucket(bucket) != 0;
      @
      @ ensures_free \result == this.lastReadOf(bucket);
      @
      @ ensures_free this.toReadCountOfBucket(bucket) + Buffers.BUFFER_SIZE == \old(this.toReadCountOfBucket(bucket));
      @ ensures_free \old(this.lastReadOf(bucket)) == this.lastReadOf(bucket) + Buffers.BUFFER_SIZE;
      @ // ensures (\forall int b; 0 <= b < this.num_buckets && b != bucket; this.toReadCountOfBucket(b) == \old(this.toReadCountOfBucket(b)));
      @ // ensures (\forall int b; 0 <= b < this.num_buckets; this.writtenCountOfBucket(b) == \old(this.writtenCountOfBucket(b)));
      @
      @ assignable_free this.buffer[2 * bucket];
      @*/
    public int decrement_read(int bucket) {
        final int read_pos = 2 * bucket;
        int read = this.buffer[read_pos];
        read -= Buffers.BUFFER_SIZE;
        this.buffer[read_pos] = read;
        return read;
    }
}
