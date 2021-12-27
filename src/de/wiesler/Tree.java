package de.wiesler;

public class Tree {
    private final int[] tree;
    private final int log_buckets;

    /*@ public model_behaviour
      @ requires true;
      @ model boolean doesNotAlias(int[] array) {
      @     return array != this.tree;
      @ }
      @*/

    /*@
      @ invariant this.tree.length == Classifier.STORAGE_SIZE;
      @
      @ invariant 1 <= this.log_buckets && this.log_buckets <= Constants.LOG_MAX_BUCKETS;
      @ invariant (1 << this.log_buckets) <= Classifier.STORAGE_SIZE;
      @
      @ // accessible \inv, this.tree[*], this.log_buckets;
      @*/

    /*@ public normal_behaviour
      @
      @ requires sorted_splitters.length == Classifier.STORAGE_SIZE;
      @ requires tree.length == Classifier.STORAGE_SIZE;
      @
      @ requires 1 <= log_buckets && log_buckets <= Constants.LOG_MAX_BUCKETS;
      @ requires (1 << log_buckets) <= Classifier.STORAGE_SIZE;
      @
      @ requires Functions.isSortedSlice(sorted_splitters, 0, (1 << log_buckets) - 1);
      @
      @ assignable tree[*];
      @*/
    public Tree(int[] sorted_splitters, int[] tree, int log_buckets) {
        assert (log_buckets >= 1);
        assert (log_buckets <= Constants.LOG_MAX_BUCKETS);

        final int num_buckets = 1 << log_buckets;
        final int num_splitters = num_buckets - 1;

        assert (num_buckets <= tree.length);

        this.log_buckets = log_buckets;
        this.tree = tree;
        this.build(1, sorted_splitters, 0, num_splitters);
    }

    public int log_buckets() {
        return log_buckets;
    }

    /*@ normal_behaviour
      @ requires this.tree != null;
      @ requires this.tree.length == Classifier.STORAGE_SIZE;
      @
      @ requires 1 <= this.log_buckets && this.log_buckets <= Constants.LOG_MAX_BUCKETS;
      @ requires (1 << this.log_buckets) <= Classifier.STORAGE_SIZE;
      @
      @ requires 1 <= position && position < (1 << this.log_buckets);
      @ requires Functions.isValidSlice(sorted_splitters, begin, end);
      @ requires end - begin == (1 << this.log_buckets) - position;
      @ requires end - begin >= 1;
      @
      @ assignable this.tree[position..(1 << this.log_buckets)];
      @*/
    /*@ helper */ void build(int position, int[] sorted_splitters, int begin, int end) {
        final int mid = begin + (end - begin) / 2;
        this.tree[position] = sorted_splitters[mid];
        if (2 * position + 1 < (2 * this.log_buckets)) {
            this.build(2 * position, sorted_splitters, begin, mid);
            this.build(2 * position + 1, sorted_splitters, mid, end);
        }
    }

    /*@ normal_behaviour
      @ ensures (1 << this.log_buckets) <= \result && \result <= (1 << (this.log_buckets + 1));
      @
      @ assignable \strictly_nothing;
      @*/
    int classify(int value) {
        int b = 1;

        /*@
          @ loop_invariant 0 <= i && i <= this.log_buckets;
          @
          @ loop_invariant i > 0 ==> (1 << i - 1) <= b;
          @ loop_invariant i == 0 ==> b == 1;
          @ loop_invariant b < (1 << (i - 1));
          @
          @ decreases this.log_buckets - i;
          @ assignable b;
          @*/
        for (int i = 0; i < this.log_buckets; ++i) {
            b = 2 * b + Constants.toInt(Constants.cmp(this.tree[b], value));
        }
        return b;
    }

    /*@ normal_behaviour
      @ requires Functions.isValidSlice(values, begin, end);
      @ requires indices.length == end - begin;
      @
      @ ensures (\forall int i; 0 <= i < indices.length; 0 <= indices[i] < (1 << this.log_buckets));
      @
      @ assignable indices[*];
      @*/
    void classify_all(int[] values, int begin, int end, int[] indices) {
        assert (end - begin == indices.length);
        Functions.fill(indices, 0, indices.length, 1);
        for (int i = 0; i < this.log_buckets; ++i) {
            for (int j = 0; j < indices.length; ++j) {
                int value = values[begin + j];
                int index = indices[j];
                indices[j] = 2 * index + Constants.toInt(Constants.cmp(this.tree[index], value));
            }
        }
    }
}
