package de.wiesler;

public final class Tree {
    private /*@ spec_public @*/ final int[] tree;
    private /*@ spec_public @*/ final int log_buckets;
    //@ ghost final int num_buckets;
    //@ ghost final int[] sorted_splitters;

    // /*@ public model_behaviour
    //   @ requires 1 <= log_length <= 29;
    //   @ requires 0 <= index < (1 << log_length);
    //   @
    //   @ ensures \result ==> 2 * index + 1 < (1 << log_length);
    //   @
    //   @ static model no_state boolean hasChildren(int log_length, int index) {
    //   @     return 2 * index < (1 << log_length);
    //   @ }
    //   @*/

    // /*@ public model_behaviour
    //   @ requires (1 << log_length) <= tree.length;
    //   @ static model boolean heapProperty(int[] tree, int log_length) {
    //   @     return (\forall int i; 0 <= i < (1 << log_length);
    //   @         Tree.hasChildren(log_length, i) ==> tree[i] < tree[i * 2 + 1]
    //   @     );
    //   @ }
    //   @*/

    /*@ public invariant 1 <= this.log_buckets <= Constants.LOG_MAX_BUCKETS;
      @ public invariant this.num_buckets == (1 << this.log_buckets);
      @ public invariant 2 <= this.num_buckets <= this.tree.length;
      @ public invariant this.num_buckets <= this.sorted_splitters.length;
      @ public invariant Functions.isSortedSliceTransitive(this.sorted_splitters, 0, this.num_buckets - 1);
      @
      @ accessible \inv: this.tree[*], this.sorted_splitters[*];
      @*/

    /*@ public normal_behaviour
      @ requires 1 <= log_buckets <= Constants.LOG_MAX_BUCKETS;
      @ requires 0 <= (1 << log_buckets) <= sorted_splitters.length;
      @ requires Functions.isSortedSliceTransitive(sorted_splitters, 0, (1 << log_buckets) - 1);
      @ requires (1 << log_buckets) <= tree.length;
      @ requires \disjoint(sorted_splitters[*], tree[*]);
      @
      @ ensures this.log_buckets == log_buckets;
      @ ensures this.tree == tree;
      @ ensures this.sorted_splitters == sorted_splitters;
      @
      @ assignable tree[*];
      @*/
    public Tree(int[] sorted_splitters, int[] tree, int log_buckets) {
        //@ set num_buckets = 1 << log_buckets;
        //@ set this.sorted_splitters = sorted_splitters;
        final int num_buckets = 1 << log_buckets;
        final int num_splitters = num_buckets - 1;

        //@ assert 2 <= num_buckets <= tree.length;

        this.log_buckets = log_buckets;
        this.tree = tree;
        this.build(1, sorted_splitters, 0, num_splitters);
    }

    /*@ normal_behaviour
      @ requires this.tree != null;
      @ requires 1 <= this.log_buckets <= Constants.LOG_MAX_BUCKETS;
      @ requires 2 <= this.num_buckets <= tree.length;
      @ requires this.num_buckets == (1 << this.log_buckets);
      @
      @ requires 1 <= position && position < this.num_buckets;
      @ requires 0 <= begin <= end <= sorted_splitters.length;
      @
      @ measured_by end - begin;
      @
      @ assignable this.tree[position..(1 << this.log_buckets)];
      @*/
    /*@ helper */ void build(int position, int[] sorted_splitters, int begin, int end) {
        final int mid = begin + (end - begin) / 2;
        this.tree[position] = sorted_splitters[mid];
        if (2 * position + 1 < (1 << this.log_buckets)) {
            this.build(2 * position, sorted_splitters, begin, mid);
            this.build(2 * position + 1, sorted_splitters, mid, end);
        }
    }

    /*@ public model_behaviour
      @ requires 0 <= bucket < this.num_buckets;
      @
      @ model boolean isClassifiedAs(int value, int bucket) {
      @     return ((0 < bucket ==> this.sorted_splitters[bucket - 1] < value) &&
      @             (bucket < this.num_buckets - 1 ==> value <= this.sorted_splitters[bucket]));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires this.sorted_splitters[0] < this.sorted_splitters[1];
      @ ensures \result;
      @
      @ model boolean classOfFirstSplitters() {
      @     return this.classify(this.sorted_splitters[0]) != this.classify(this.sorted_splitters[1]);
      @ }
      @*/

    /*@ normal_behaviour
      @ ensures this.num_buckets <= \result < 2 * this.num_buckets;
      @
      @ ensures this.isClassifiedAs(value, \result - this.num_buckets);
      @
      @ // Needed to bring this method to logic
      @ ensures_free \result == this.classify(value);
      @
      @ assignable \strictly_nothing;
      @
      @ accessible this.tree[*], this.sorted_splitters[*];
      @*/
    int classify(int value) {
        int b = 1;

        /*@ loop_invariant 0 <= i && i <= this.log_buckets;
          @
          @ loop_invariant (1 << i) <= b < (1 << (i + 1));
          @
          @ decreases this.log_buckets - i;
          @ assignable \strictly_nothing;
          @*/
        for (int i = 0; i < this.log_buckets; ++i) {
            b = 2 * b + Constants.toInt(Constants.cmp(this.tree[b], value));
        }
        return b;
    }

    /*@ normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires indices.length == end - begin;
      @ requires \disjoint(values[*], indices[*], this.tree[*], this.sorted_splitters[*]);
      @
      @ ensures (\forall int i; 0 <= i < indices.length; this.num_buckets <= indices[i] < 2 * this.num_buckets);
      @ // Needed to bring this method to logic
      @ ensures_free (\forall int i; 0 <= i < indices.length; indices[i] == this.classify(values[begin + i]));
      @
      @ assignable indices[*];
      @*/
    void classify_all(int[] values, int begin, int end, int[] indices) {
        Functions.fill(indices, 0, indices.length, 1);

        /*@ loop_invariant 0 <= i && i <= this.log_buckets;
          @
          @ loop_invariant (\forall int k; 0 <= k < indices.length; (1 << i) <= indices[k] < (1 << (i + 1)));
          @
          @ decreases this.log_buckets - i;
          @ assignable indices[*];
          @*/
        for (int i = 0; i < this.log_buckets; ++i) {
            /*@ loop_invariant 0 <= j && j <= indices.length;
              @
              @ loop_invariant (\forall int k; j <= k < indices.length; (1 << i) <= indices[k] < (1 << (i + 1)));
              @ loop_invariant (\forall int k; 0 <= k < j; (1 << (i + 1)) <= indices[k] < (1 << (i + 2)));
              @
              @ decreases indices.length - j;
              @ assignable indices[*];
              @*/
            for (int j = 0; j < indices.length; ++j) {
                int value = values[begin + j];
                int index = indices[j];
                indices[j] = 2 * index + Constants.toInt(Constants.cmp(this.tree[index], value));
            }
        }
    }
}
