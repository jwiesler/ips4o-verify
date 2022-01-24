package de.wiesler;

public class Tree {
    private final int[] tree;
    private /*@ spec_public @*/ final int log_buckets;
    //@ ghost int num_buckets;

    /*@ public model_behaviour
      @ requires true;
      @ model boolean doesNotAlias(int[] array) {
      @     return array != this.tree;
      @ }
      @*/

    /*@ public invariant Functions.isBetweenInclusive(this.log_buckets, 1, Constants.LOG_MAX_BUCKETS);
      @ public invariant this.num_buckets == (1 << this.log_buckets);
      @ public invariant Functions.isBetweenInclusive(this.num_buckets, 2, tree.length);
      @
      @ // accessible \inv, this.tree[*], this.log_buckets;
      @*/

    /*@ public normal_behaviour
      @ requires Functions.isBetweenInclusive(log_buckets, 1, Constants.LOG_MAX_BUCKETS);
      @ requires Functions.isValidSlice(sorted_splitters, 0, (1 << log_buckets) - 1);
      @ requires Functions.isSortedSlice(sorted_splitters, 0, (1 << log_buckets) - 1);
      @ requires (1 << log_buckets) <= tree.length;
      @
      @ ensures this.log_buckets == log_buckets;
      @ ensures this.tree == tree;
      @ 
      @ assignable tree[*];
      @*/
    public Tree(int[] sorted_splitters, int[] tree, int log_buckets) {
        //@ set num_buckets = 1 << log_buckets;
        final int num_buckets = 1 << log_buckets;
        final int num_splitters = num_buckets - 1;

        //@ assert num_buckets <= tree.length;

        this.log_buckets = log_buckets;
        this.tree = tree;
        this.build(1, sorted_splitters, 0, num_splitters);
    }

    /*@ normal_behaviour
      @ requires this.tree != null;
      @ requires Functions.isBetweenInclusive(this.log_buckets, 1, Constants.LOG_MAX_BUCKETS);
      @ requires this.num_buckets == (1 << this.log_buckets);
      @ requires Functions.isBetweenInclusive(this.num_buckets, 2, tree.length);
      @
      @ requires 1 <= position && position < this.num_buckets;
      @ requires Functions.isValidSlice(sorted_splitters, begin, end);
      @ requires end - begin == this.num_buckets - position;
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

    /*@ normal_behaviour
      @ ensures this.num_buckets <= \result;
      @ ensures \result < 2 * this.num_buckets;
      @
      @ assignable \strictly_nothing;
      @*/
    int classify(int value) {
        int b = 1;

        /*@
          @ loop_invariant 0 <= i && i <= this.log_buckets;
          @
          @ loop_invariant (1 << i) <= b;
          @ loop_invariant i == 0 ==> b == 1;
          @ loop_invariant b < (1 << (i + 1));
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
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires indices.length == end - begin;
      @ requires values != indices && values != this.tree && indices != this.tree;
      @
      @ ensures (\forall int i; 0 <= i < indices.length; this.num_buckets <= indices[i] < 2 * this.num_buckets);
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
