package de.wiesler;

public final class Tree {
    private /*@ spec_public @*/ final int[] tree;
    private /*@ spec_public @*/ final int log_buckets;
    private /*@ spec_public @*/ final int[] sorted_splitters;
    //@ ghost final int num_buckets;

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
        final int num_buckets = 1 << log_buckets;
        final int num_splitters = num_buckets - 1;

        //@ assert 2 <= num_buckets <= tree.length;

        this.sorted_splitters = sorted_splitters;
        this.log_buckets = log_buckets;
        this.tree = tree;
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
      @ ensures 0 <= \result < this.num_buckets;
      @
      @ ensures this.isClassifiedAs(value, \result);
      @
      @ // Needed to bring this method to logic
      @ ensures_free \result == this.classify(value);
      @
      @ assignable \strictly_nothing;
      @
      @ accessible this.tree[*], this.sorted_splitters[*];
      @*/
    int classify(int value) {
        int b = (1 << this.log_buckets) - 1;
        //@ ghost int exp = this.log_buckets;

        // |---------------------|
        //       ^      ^     ^
        //      b-d   b-d/2   b
        //
        // case 1:
        // |---------------------|
        //       ^      ^
        //      b-d     b
        //
        // case 2:
        // |---------------------|
        //              ^     ^
        //             b-d    b

        /*@ loop_invariant d - 1 <= b <= this.num_buckets - 1;
          @ loop_invariant 0 <= exp <= this.log_buckets;
          @ loop_invariant d == (1 << exp);
          @ loop_invariant b - d == -1 || this.sorted_splitters[b - d] < value;
          @ loop_invariant b == this.num_buckets - 1 || value <= this.sorted_splitters[b];
          @ decreases exp;
          @ assignable \strictly_nothing;
          @*/
        for (int d = 1 << this.log_buckets; d > 1;) {
            d /= 2;
            b = this.sorted_splitters[b - d] < value ? b : b - d;
            //@ set exp = exp - 1;
        }

        //@ assert d == 1;
        return b;
    }

    /*@ normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires indices.length == end - begin;
      @ requires \disjoint(values[*], indices[*], this.tree[*], this.sorted_splitters[*]);
      @
      @ ensures (\forall int i; 0 <= i < indices.length; 0 <= indices[i] < this.num_buckets);
      @ // Needed to bring this method to logic
      @ ensures_free (\forall int i; 0 <= i < indices.length; indices[i] == this.classify(values[begin + i]));
      @
      @ assignable indices[*];
      @*/
    void classify_all(int[] values, int begin, int end, int[] indices) {
        Functions.fill(indices, 0, indices.length, (1 << this.log_buckets) - 1);
        //@ ghost int exp = this.log_buckets;

        /*@ loop_invariant (\forall int i; 0 <= i < indices.length; d - 1 <= indices[i] <= this.num_buckets - 1);
          @ loop_invariant 0 <= exp <= this.log_buckets;
          @ loop_invariant d == (1 << exp);
          @ loop_invariant (\forall int i; 0 <= i < indices.length;
          @     (indices[i] - d == -1 || this.sorted_splitters[indices[i] - d] < values[begin + i]) &&
          @     (indices[i] == this.num_buckets - 1 || values[begin + i] <= this.sorted_splitters[indices[i]])
          @ );
          @ decreases exp;
          @ assignable indices[*];
          @*/
        for (int d = 1 << this.log_buckets; d > 1;) {
            //@ assert (d / 2) * 2 == d;
            d /= 2;

            /*@ loop_invariant 0 <= j && j <= indices.length;
              @
              @ loop_invariant (\forall int i; j <= i < indices.length;
              @     2 * d - 1 <= indices[i] <= this.num_buckets - 1 &&
              @     (indices[i] - 2 * d == -1 || this.sorted_splitters[indices[i] - 2 * d] < values[begin + i]) &&
              @     (indices[i] == this.num_buckets - 1 || values[begin + i] <= this.sorted_splitters[indices[i]])
              @ );
              @ loop_invariant (\forall int i; 0 <= i < j;
              @     d - 1 <= indices[i] <= this.num_buckets - 1 &&
              @     (indices[i] - d == -1 || this.sorted_splitters[indices[i] - d] < values[begin + i]) &&
              @     (indices[i] == this.num_buckets - 1 || values[begin + i] <= this.sorted_splitters[indices[i]])
              @ );
              @
              @ decreases indices.length - j;
              @ assignable indices[*];
              @*/
            for (int j = 0; j < indices.length; ++j) {
                int value = values[begin + j];
                int index = indices[j];
                indices[j] = this.sorted_splitters[index - d] < value ? index : index - d;
            }

            //@ set exp = exp - 1;
        }

        //@ assert d == 1;
    }
}
