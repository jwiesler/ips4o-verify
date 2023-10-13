package de.wiesler;

public final class Tree {
    private /*@ spec_public @*/ final int[] tree;
    private /*@ spec_public @*/ final int log_buckets;
    //@ ghost final int num_buckets;
    //@ ghost final int[] sorted_splitters;

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
      @ requires_free 1 <= log_buckets <= Constants.LOG_MAX_BUCKETS;
      @ requires_free 0 <= (1 << log_buckets) <= sorted_splitters.length;
      @ requires_free Functions.isSortedSliceTransitive(sorted_splitters, 0, (1 << log_buckets) - 1);
      @ requires_free (1 << log_buckets) <= tree.length;
      @ requires_free \disjoint(sorted_splitters[*], tree[*]);
      @
      @ ensures_free this.log_buckets == log_buckets;
      @ ensures_free this.tree == tree;
      @ ensures_free this.sorted_splitters == sorted_splitters;
      @
      @ assignable_free tree[*];
      @*/
    public Tree(int[] sorted_splitters, int[] tree, int log_buckets) {
        //@ set num_buckets = 1 << log_buckets;
        //@ set this.sorted_splitters = sorted_splitters;
        final int num_buckets = 1 << log_buckets;
        final int num_splitters = num_buckets - 1;

        //@ assume 2 <= num_buckets <= tree.length;

        this.log_buckets = log_buckets;
        this.tree = tree;
        this.build(sorted_splitters);
        //@ assert (1 << this.log_buckets) == \dl_pow(2, this.log_buckets);
        //@ assert (\forall int i; 1 <= i < this.num_buckets; Tree.piInRangeLower(i, log_buckets) && Tree.piInRangeUpper(i, log_buckets));
    }

    /*@ public normal_behaviour
      @ requires this.tree != null && sorted_splitters != null;
      @ requires \disjoint(sorted_splitters[*], this.tree[*]);
      @ requires this.num_buckets <= sorted_splitters.length;
      @ requires 1 <= this.log_buckets <= Constants.LOG_MAX_BUCKETS;
      @ requires 2 <= this.num_buckets <= tree.length;
      @ requires this.num_buckets == (1 << this.log_buckets);
      @ requires Functions.isSortedSliceTransitive(sorted_splitters, 0, (1 << this.log_buckets) - 1);
      @
      @ ensures (\forall int i; 1 <= i < this.num_buckets; this.tree[i] == sorted_splitters[Tree.pi(i, this.log_buckets) - 1]);
      @
      @ assignable this.tree[*];
      @*/
    /*@ helper */ void build(int[] sorted_splitters) {
        //@ assert 1 <= \dl_pow(2, this.log_buckets) <= \dl_pow(2, 6);
        //@ assert (1 << this.log_buckets) == \dl_pow(2, this.log_buckets);
        int num_buckets = 1 << this.log_buckets;
        //@ assert this.num_buckets == num_buckets;

        int tree_offset = 1;
        int offset = num_buckets;
        /*@ loop_invariant 0 <= l <= this.log_buckets;
          @ loop_invariant tree_offset == \dl_pow(2, l);
          @ loop_invariant offset == \dl_pow(2, this.log_buckets - l);
          @ loop_invariant (\forall int i; 1 <= i < tree_offset;
          @     this.tree[i] == sorted_splitters[Tree.pi(i, this.log_buckets) - 1]
          @ );
          @
          @ decreases this.log_buckets - l;
          @ assignable this.tree[*];
          @*/
        for (int l = 0; l < this.log_buckets; ++l) {
            final int step = offset;
            offset /= 2;

            //@ assert step == \dl_pow(2, this.log_buckets - l);
            //@ assert offset == \dl_pow(2, this.log_buckets - l - 1);
            //@ assert step == offset * 2;
            //@ assert 1 <= offset < num_buckets;
            //@ assert \dl_pow(2, l + 1) <= num_buckets;

            //@ ghost int tree_start_offset = tree_offset;

            //@ assert \dl_pow(2, l + 1) - \dl_pow(2, l) == \dl_pow(2, l);
            //@ assert step * \dl_pow(2, l) == \dl_pow(2, this.log_buckets);
            //@ assert offset - 1 + step * \dl_pow(2, l) >= num_buckets;
            //@ assert offset - 1 + step * (\dl_pow(2, l) - 1) < num_buckets;

            /*@ loop_invariant offset - 1 <= o < step + num_buckets;
              @ loop_invariant o == offset - 1 + step * (tree_offset - tree_start_offset);
              @ loop_invariant \dl_pow(2, l) <= tree_offset <= \dl_pow(2, l + 1);
              @ loop_invariant (\forall int i; 1 <= i < tree_offset;
              @     this.tree[i] == sorted_splitters[Tree.pi(i, this.log_buckets) - 1]
              @ );
              @
              @ decreases step + num_buckets - o;
              @ assignable this.tree[*];
              @*/
            for (int o = offset - 1; o < num_buckets; o += step) {
                //@ assert \dl_log(2, tree_offset) == l;
                //@ assert Tree.pi(tree_offset, this.log_buckets) - 1 == o;
                this.tree[tree_offset] = sorted_splitters[o];
                tree_offset += 1;
            }

            //@ assert tree_offset == \dl_pow(2, l + 1);
        }
    }

    /*@ model_behaviour
      @ requires true;
      @ static no_state model int pi(int b, int log_buckets) {
      @     return (2 * (b - \dl_pow(2, \dl_log(2, b))) + 1) * \dl_pow(2, log_buckets - 1 - \dl_log(2, b));
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
      @ ensures_free \result;
      @
      @ model boolean classOfFirstSplitters() {
      @     return this.classify(this.sorted_splitters[0]) != this.classify(this.sorted_splitters[1]);
      @ }
      @*/

    /*@ model_behaviour
      @ requires b >= 1;
      @ ensures \result;
      @ // Provable using powLogMore2
      @ static model boolean piLemmaUpperBound(int b) {
      @     return 2 * (b - \dl_pow(2, \dl_log(2, b))) + 1 < \dl_pow(2, \dl_log(2, b) + 1);
      @ }
      @*/

    /*@ model_behaviour
      @ requires 1 <= b < \dl_pow(2, log_buckets);
      @ requires 1 <= log_buckets;
      @ ensures \result;
      @ static model boolean piInRangeLower(int b, int log_buckets) {
      @     return 1 <= Tree.pi(b, log_buckets);
      @ }
      @*/

    /*@ model_behaviour
      @ requires 1 <= b < \dl_pow(2, log_buckets);
      @ requires 1 <= log_buckets;
      @ requires Tree.piLemmaUpperBound(b);
      @ ensures \result;
      @ static model boolean piInRangeUpper(int b, int log_buckets) {
      @     return Tree.pi(b, log_buckets) < \dl_pow(2, log_buckets);
      @ }
      @*/

    /*@ model_behaviour
      @ requires 1 <= b < \dl_pow(2, log_buckets - 1);
      @ requires 1 <= log_buckets;
      @ ensures \result;
      @ static model boolean piLemmaLeft(int b, int log_buckets) {
      @     return Tree.pi(b, log_buckets) - Tree.pi(2 * b, log_buckets) == \dl_pow(2, log_buckets - 2 - \dl_log(2, b));
      @ }
      @*/

    /*@ model_behaviour
      @ requires 1 <= b < \dl_pow(2, log_buckets - 1);
      @ requires 1 <= log_buckets;
      @ ensures \result;
      @ static model boolean piLemmaRight(int b, int log_buckets) {
      @     return Tree.pi(2 * b + 1, log_buckets) - Tree.pi(b, log_buckets) == \dl_pow(2, log_buckets - 2 - \dl_log(2, b));
      @ }
      @*/

    /*@ model_behaviour
      @ requires 1 <= b < \dl_pow(2, log_buckets - 1);
      @ requires 1 <= log_buckets;
      @ ensures \result;
      @ static model boolean piLemma(int b, int log_buckets) {
      @     return Tree.piLemmaLeft(b, log_buckets) && Tree.piLemmaRight(b, log_buckets);
      @ }
      @*/

    /*@ model_behaviour
      @ requires log_buckets >= 1;
      @ ensures \result;
      @ static model boolean piOf1(int log_buckets) {
      @     return Tree.pi(1, log_buckets) == \dl_pow(2, log_buckets) - \dl_pow(2, log_buckets) / 2;
      @ }
      @*/

    /*@ model_behaviour
      @ requires true;
      @ accessible this.sorted_splitters[*];
      @ model boolean binarySearchInvariant(int b, int d, int value) {
      @     return d - 1 <= b <= this.num_buckets - 1 &&
      @         (b - d == -1 || this.sorted_splitters[b - d] < value) &&
      @         (b == this.num_buckets - 1 || value <= this.sorted_splitters[b]);
      @ }
      @*/

    /*@ model_behaviour
      @ requires this.binarySearchInvariant(b, d, value);
      @ requires 0 <= l < this.log_buckets;
      @ requires d == \dl_pow(2, this.log_buckets - l);
      @ ensures \result;
      @
      @ model boolean binarySearchInvariantLemma(int b, int d, int value, int l) {
      @     return this.binarySearchInvariant(this.sorted_splitters[b - d / 2] < value ? b : b - d / 2, d / 2, value);
      @ }
      @*/

    /*@ model_behaviour
      @ requires true;
      @ // final only no_state
      @ model boolean treeSearchInvariant(int b, int l, int b_bin, int d_bin) {
      @     return \dl_pow(2, l) <= b < \dl_pow(2, l + 1) &&
      @         \dl_log(2, b) == l &&
      @         (l < this.log_buckets ==> b_bin - d_bin / 2 == Tree.pi(b, this.log_buckets) - 1) &&
      @         (l == this.log_buckets ==> b_bin == b - \dl_pow(2, this.log_buckets));
      @ }
      @*/

    /*@ normal_behaviour
      @ requires this.binarySearchInvariant(b_bin, d_bin, value);
      @ requires treeSearchInvariant(b, l, b_bin, d_bin);
      @ requires 0 <= l < this.log_buckets;
      @ requires d_bin == \dl_pow(2, this.log_buckets - l);
      @ requires this.num_buckets == \dl_pow(2, this.log_buckets);
      @ ensures treeSearchInvariant(2 * b + (this.tree[b] < value ? 1 : 0), l + 1, this.sorted_splitters[b_bin - d_bin / 2] < value ? b_bin : b_bin - d_bin / 2, d_bin / 2);
      @ ensures \result;
      @ assignable \strictly_nothing;
      @*/
    boolean treeSearchInvariantLemmaImpl(int b, int l, int b_bin, int d_bin, int value) {
        //@ assert 1 <= \dl_pow(2, l);
        //@ assert \dl_pow(2, l + 1) == 2 * \dl_pow(2, l);
        //@ assert \dl_pow(2, l + 2) == 2 * \dl_pow(2, l + 1);
        //@ assert \dl_pow(2, l + 1) <= \dl_pow(2, this.log_buckets);
        //@ assert this.sorted_splitters[b_bin - d_bin / 2] == this.tree[b];
        //@ assert \dl_log(2, 2 * b + (this.tree[b] < value ? 1 : 0)) == l + 1;
        if (l < this.log_buckets - 1) {
            //@ assert \dl_pow(2, l + 1) <= \dl_pow(2, this.log_buckets - 1);
            //@ assert Tree.piLemma(b, this.log_buckets);
            /*@ assert Tree.pi(2 * b + (this.tree[b] < value ? 1 : 0), this.log_buckets) - Tree.pi(b, this.log_buckets) == (
              @     this.tree[b] < value ? (\dl_pow(2, this.log_buckets - 2 - \dl_log(2, b))) : -(\dl_pow(2, this.log_buckets - 2 - \dl_log(2, b)))
              @ );
              @*/
            //@ assert \dl_pow(2, this.log_buckets - 2 - \dl_log(2, b)) == d_bin / 2 / 2;
        }
        return true;
    }

    /*@ model_behaviour
      @ requires this.binarySearchInvariant(b_bin, d_bin, value);
      @ requires treeSearchInvariant(b, l, b_bin, d_bin);
      @ requires 0 <= l < this.log_buckets;
      @ requires d_bin == \dl_pow(2, this.log_buckets - l);
      @ requires this.num_buckets == \dl_pow(2, this.log_buckets);
      @ ensures \result ==> treeSearchInvariant(2 * b + (this.tree[b] < value ? 1 : 0), l + 1, this.sorted_splitters[b_bin - d_bin / 2] < value ? b_bin : b_bin - d_bin / 2, d_bin / 2);
      @ ensures \result;
      @
      @ model boolean treeSearchInvariantLemma(int b, int l, int b_bin, int d_bin, int value) {
      @     return treeSearchInvariantLemmaImpl(b, l, b_bin, d_bin, value);
      @ }
      @*/

    /*@ normal_behaviour
      @ requires_free \dl_inInt(value);
      @ ensures_free this.num_buckets <= \result < 2 * this.num_buckets;
      @
      @ ensures_free this.isClassifiedAs(value, \result - this.num_buckets);
      @
      @ // Needed to bring this method to logic
      @ ensures_free \result == this.classify(value);
      @
      @ assignable_free \strictly_nothing;
      @
      @ accessible this.tree[*], this.sorted_splitters[*];
      @*/
    int classify(int value) {
        //@ assert \dl_pow(2, 1) <= \dl_pow(2, this.log_buckets) <= \dl_pow(2, Constants.LOG_MAX_BUCKETS);
        //@ assert \dl_pow(2, this.log_buckets) == this.num_buckets;
        //@ ghost int b_bin = this.num_buckets - 1;
        //@ ghost int d_bin = this.num_buckets;
        int b = 1;

        //@ assert Tree.piOf1(this.log_buckets);

        /*@ loop_invariant 0 <= l && l <= this.log_buckets;
          @ loop_invariant d_bin == \dl_pow(2, this.log_buckets - l);
          @
          @ // Ghost binary search
          @ loop_invariant this.binarySearchInvariant(b_bin, d_bin, value);
          @ loop_invariant this.treeSearchInvariant(b, l, b_bin, d_bin);
          @
          @ decreases this.log_buckets - l;
          @ assignable \strictly_nothing;
          @*/
        for (int l = 0; l < this.log_buckets; ++l) {
            //@ assert treeSearchInvariantLemma(b, l, b_bin, d_bin, value);
            //@ assert this.binarySearchInvariantLemma(b_bin, d_bin, value, l);
            //@ assert treeSearchInvariant(2 * b + (this.tree[b] < value ? 1 : 0), l + 1, this.sorted_splitters[b_bin - d_bin / 2] < value ? b_bin : b_bin - d_bin / 2, d_bin / 2);
            //@ assert this.binarySearchInvariant(this.sorted_splitters[b_bin - d_bin / 2] < value ? b_bin : b_bin - d_bin / 2, d_bin / 2, value);

            //@ assert (d_bin / 2) * 2 == d_bin;
            //@ set d_bin = d_bin / 2;
            //@ assert 0 <= \dl_pow(2, this.log_buckets - l) <= \dl_pow(2, this.log_buckets);
            //@ assert 0 <= b_bin - d_bin < this.num_buckets;
            //@ assert \dl_pow(2, l + 1) <= \dl_pow(2, this.log_buckets);
            //@ assert 0 <= b < this.num_buckets;
            //@ assert d_bin == \dl_pow(2, this.log_buckets - l - 1);
            //@ assert \dl_inInt(l + 1);
            //@ assert \dl_inInt(2 * b + (this.tree[b] < value ? 1 : 0));
            //@ set b_bin = this.sorted_splitters[b_bin - d_bin] < value ? b_bin : b_bin - d_bin;
            b = 2 * b + (this.tree[b] < value ? 1 : 0);
        }
        return b;
    }

    /*@ normal_behaviour
      @ requires_free 0 <= begin <= end <= values.length;
      @ requires_free indices.length == end - begin;
      @ requires_free \disjoint(values[*], indices[*], this.tree[*], this.sorted_splitters[*]);
      @
      @ ensures_free (\forall int i; 0 <= i < indices.length; this.num_buckets <= indices[i] < 2 * this.num_buckets);
      @ // Needed to bring this method to logic
      @ ensures_free (\forall int i; 0 <= i < indices.length; indices[i] == this.classify(values[begin + i]));
      @
      @ assignable_free indices[*];
      @*/
    void classify_all(int[] values, int begin, int end, int[] indices) {
        Functions.fill(indices, 0, indices.length, 1);

        //@ assert \dl_pow(2, 1) <= \dl_pow(2, this.log_buckets) <= \dl_pow(2, Constants.LOG_MAX_BUCKETS);
        //@ assert \dl_pow(2, this.log_buckets) == this.num_buckets;
        //@ ghost int[] b_bins = new int[indices.length];
        //@ ghost int d_bin = this.num_buckets;

        //@ assert Tree.piOf1(this.log_buckets);

        /*@ loop_invariant 0 <= o <= indices.length;
          @
          @ // Ghost binary search
          @ loop_invariant (\forall int j; 0 <= j < o;
          @     b_bins[j] == this.num_buckets - 1
          @ );
          @
          @ decreases indices.length - o;
          @ assignable b_bins[*];
          @*/
        for (int o = 0; o < indices.length; ++o) {
            //@ set b_bins[o] = this.num_buckets - 1;
        }

        /*@ loop_invariant 0 <= l && l <= this.log_buckets;
          @ loop_invariant d_bin == \dl_pow(2, this.log_buckets - l);
          @
          @ // Ghost binary search
          @ loop_invariant (\forall int i; 0 <= i < indices.length;
          @     this.binarySearchInvariant(b_bins[i], d_bin, values[begin + i]) &&
          @         this.treeSearchInvariant(indices[i], l, b_bins[i], d_bin)
          @ );
          @
          @ decreases this.log_buckets - l;
          @ assignable b_bins[*], indices[*];
          @*/
        for (int l = 0; l < this.log_buckets; ++l) {
            //@ assert (d_bin / 2) * 2 == d_bin;
            //@ set d_bin = d_bin / 2;

            //@ assert \dl_pow(2, l + 1) == 2 * \dl_pow(2, l) && \dl_pow(2, l + 2) == 2 * \dl_pow(2, l + 1);

            /*@ loop_invariant 0 <= j && j <= indices.length;
              @
              @ loop_invariant (\forall int i; 0 <= i < j;
              @     this.binarySearchInvariant(b_bins[i], d_bin, values[begin + i]) &&
              @         this.treeSearchInvariant(indices[i], l + 1, b_bins[i], d_bin)
              @ );
              @
              @ loop_invariant (\forall int i; j <= i < indices.length;
              @     this.binarySearchInvariant(b_bins[i], 2 * d_bin, values[begin + i]) &&
              @         this.treeSearchInvariant(indices[i], l, b_bins[i], 2 * d_bin)
              @ );
              @
              @ decreases indices.length - j;
              @ assignable b_bins[*], indices[*];
              @*/
            for (int j = 0; j < indices.length; ++j) {
                //@ assert indices != b_bins && values != b_bins;
                //@ assert this.sorted_splitters != b_bins && this.tree != b_bins;

                /*@ normal_behaviour
                  @ ensures this.binarySearchInvariant(b_bins[j], d_bin, values[begin + j]) &&
                  @     this.treeSearchInvariant(indices[j], l + 1, b_bins[j], d_bin);
                  @ assignable b_bins[j], indices[j];
                  @*/
                {
                    int value = values[begin + j];
                    int b = indices[j];

                    //@ ghost int b_bin = b_bins[j];
                    /*@ assert this.binarySearchInvariant(b_bin, 2 * d_bin, value) &&
                      @     this.treeSearchInvariant(b, l, b_bin, 2 * d_bin);
                      @*/

                    //@ assert treeSearchInvariantLemma(b, l, b_bin, 2 * d_bin, value);
                    //@ assert \invariant_for(this);
                    //@ assert this.binarySearchInvariantLemma(b_bin, 2 * d_bin, value, l);
                    //@ assert treeSearchInvariant(2 * b + (this.tree[b] < value ? 1 : 0), l + 1, this.sorted_splitters[b_bin - d_bin] < value ? b_bin : b_bin - d_bin, d_bin);
                    //@ assert this.binarySearchInvariant(this.sorted_splitters[b_bin - d_bin] < value ? b_bin : b_bin - d_bin, d_bin, value);

                    //@ assert 0 <= \dl_pow(2, this.log_buckets - l) <= \dl_pow(2, this.log_buckets);
                    //@ assert 0 <= b_bin - d_bin < this.num_buckets;
                    //@ assert \dl_pow(2, l + 1) <= \dl_pow(2, this.log_buckets);
                    //@ assert 0 <= b < this.num_buckets;
                    //@ assert d_bin == \dl_pow(2, this.log_buckets - l - 1);
                    //@ assert \dl_inInt(l + 1);
                    //@ assert \dl_inInt(2 * b + (this.tree[b] < value ? 1 : 0));
                    //@ set b_bins[j] = this.sorted_splitters[b_bin - d_bin] < value ? b_bin : b_bin - d_bin;
                    indices[j] = 2 * b + (this.tree[b] < value ? 1 : 0);
                }
                {;;}
            }
        }

        //@ assert d_bin == 1;
    }
}
