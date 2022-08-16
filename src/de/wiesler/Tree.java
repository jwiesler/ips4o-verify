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
      @ invariant (\forall int i; 1 <= i < this.num_buckets; 1 <= Tree.pi(i, this.log_buckets) < this.num_buckets);
      @ invariant (\forall int i; 1 <= i < this.num_buckets; this.tree[i] == this.sorted_splitters[Tree.pi(i, this.log_buckets) - 1]);
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

    /*@ model_behaviour
      @ requires n > 0;
      @ ensures \result >= 0;
      @ static no_state model int log2(int n);
      @*/

    /*@ model_behaviour
      @ requires n >= 0;
      @ ensures \result >= 0;
      @ static no_state model int pow2(int n);
      @*/

    /*@ model_behaviour
      @ requires 0 <= log_buckets < Constants.LOG_MAX_BUCKETS;
      @ requires b > 0;
      @ static no_state model int pi(int b, int log_buckets) {
      @     return (2 * (b - Tree.pow2(Tree.log2(b))) + 1) * Tree.pow2(log_buckets - 1 - Tree.log2(b));
      @ }
      @*/

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

    /*@ model_behaviour
      @ requires 1 <= b < (1 << log_buckets);
      @ ensures \result;
      @ static model boolean piLemma(int b, int log_buckets) {
      @     return
      @         Tree.pi(2 * b + 1, log_buckets) - Tree.pi(b, log_buckets) == 1 << (log_buckets - 2 - Tree.log2(b)) &&
      @         Tree.pi(b, log_buckets) - Tree.pi(2 * b, log_buckets) == 1 << (log_buckets - 2 - Tree.log2(b));
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
        //@ ghost int b_bin = (1 << this.log_buckets) - 1;
        //@ ghost int d_bin = (1 << this.log_buckets);
        int b = 1;

        /*@ loop_invariant 0 <= l && l <= this.log_buckets;
          @
          @ // Ghost binary search
          @ loop_invariant d_bin - 1 <= b_bin <= this.num_buckets - 1;
          @ loop_invariant d_bin == (1 << (this.log_buckets - l));
          @ loop_invariant b_bin - d_bin == -1 || this.sorted_splitters[b_bin - d_bin] < value;
          @ loop_invariant b_bin == this.num_buckets - 1 || value <= this.sorted_splitters[b_bin];
          @
          @ // Actual search
          @ loop_invariant (1 << l) <= b < (1 << (l + 1)) && Tree.log2(b) == l;
          @ // next value to compare to is the same
          @ loop_invariant l < this.log_buckets ==> b_bin - d_bin / 2 == Tree.pi(b, this.log_buckets) - 1;
          @ loop_invariant l == this.log_buckets ==> b_bin == b - (1 << this.log_buckets);
          @
          @ decreases this.log_buckets - l;
          @ assignable \strictly_nothing;
          @*/
        for (int l = 0; l < this.log_buckets; ++l) {
            //@ assert (d_bin / 2) * 2 == d_bin;
            //@ set d_bin = d_bin / 2;
            //@ assert 0 <= b_bin - d_bin < this.num_buckets;
            //@ assert 1 + l <= this.log_buckets;
            //@ assert (1 << (l + 1)) == 2 * (1 << l) && (1 << (l + 2)) == 2 * (1 << (l + 1));
            //@ assert 0 <= b < this.num_buckets;
            int cmp;
            //@ assert this.sorted_splitters[b_bin - d_bin] == this.tree[b];
            //@ assert this.sorted_splitters[b_bin - d_bin] < value <==> this.tree[b] < value;
            //@ ghost int tmp;
            //@ ghost int b_bin_old = b_bin;
            /*@ normal_behaviour
              @ ensures tmp == (this.sorted_splitters[b_bin - d_bin] < value ? b_bin : b_bin - d_bin);
              @ ensures cmp == (this.tree[b] < value ? 1 : 0);
              @ assignable \strictly_nothing;
              @*/
            {
                //@ set tmp = this.sorted_splitters[b_bin - d_bin] < value ? b_bin : b_bin - d_bin;
                cmp = this.tree[b] < value ? 1 : 0;
            }
            //@ set b_bin = tmp;

            //@ ghost int b_old = b;
            b = 2 * b + cmp;

            if (l < this.log_buckets - 1) {
                //@ assert b_bin_old - d_bin == Tree.pi(b_old, this.log_buckets) - 1;
                //@ assert d_bin == (1 << (this.log_buckets - 1 - l));
                //@ assert b_old < (1 << (l + 1)) && l <= this.log_buckets - 2;
                //@ assert b_old < (1 << ((this.log_buckets - 2) + 1));
                //@ assert (1 << (l + 1)) <= 1 << (this.log_buckets - 2 + 1);
                //@ assert Tree.piLemma(b_old, this.log_buckets);
                /*@ assert Tree.pi(b, this.log_buckets) - Tree.pi(b_old, this.log_buckets) == (
                  @     this.tree[b_old] < value ? (1 << (this.log_buckets - 2 - Tree.log2(b_old))) : -(1 << (this.log_buckets - 2 - Tree.log2(b_old)))
                  @ );
                  @*/
                //@ assert Tree.pi(b, this.log_buckets) - Tree.pi(b_old, this.log_buckets) == b_bin - d_bin / 2 - (b_bin_old - d_bin);
                //@ assert b_bin - d_bin / 2 == Tree.pi(b, this.log_buckets) - 1;
                {}
            } else {
                //@ assert Tree.log2(b_old) == this.log_buckets - 1;
                //@ assert b_bin == b - (1 << this.log_buckets) + 1;
            }
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
