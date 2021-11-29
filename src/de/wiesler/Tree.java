package de.wiesler;

public class Tree {
    private final int[] tree;
    private final int log_buckets;

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

    void build(int position, int[] sorted_splitters, int start, int len) {
        final int mid = len / 2;
        this.tree[position] = sorted_splitters[start + mid];
        if (2 * position < (1 << this.log_buckets)) {
            this.build(2 * position, sorted_splitters, start, mid);
            this.build(2 * position + 1, sorted_splitters, start + mid, len - mid);
        }
    }

    int classify(int value) {
        int b = 1;
        for (int i = 0; i < this.log_buckets; ++i) {
            b = 2 * b + Constants.toInt(Constants.cmp(this.tree[b], value));
        }
        return b;
    }

    // values.length == indices.length
    void classify_all(int[] values, int begin, int end, int[] indices) {
        assert (end - begin == indices.length);
        Functions.fill(indices, 1);
        for (int i = 0; i < this.log_buckets; ++i) {
            for (int j = 0; j < indices.length; ++j) {
                int value = values[begin + j];
                int index = indices[j];
                indices[j] = 2 * index + Constants.toInt(Constants.cmp(this.tree[index], value));
            }
        }
    }
}
