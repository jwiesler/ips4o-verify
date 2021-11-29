package de.wiesler;

public class Buffers {
    public static final int BUFFER_SIZE = 1024 / 4;

    public static int align_to_next_block_in(int begin, int offset) {
        return begin + align_to_next_block(offset - begin);
    }

    public static int align_to_next_block(int offset) {
        return (offset + BUFFER_SIZE - 1) & (-BUFFER_SIZE);
    }

    private final int[] buffer;
    private final int[] indices;

    public Buffers() {
        this.buffer = new int[2 * BUFFER_SIZE * Constants.MAX_BUCKETS];
        this.indices = new int[Constants.MAX_BUCKETS];
    }

    public boolean push(int value, int bucket, int[] values, int write, int end) {
        int buffer_offset = bucket * BUFFER_SIZE;
        int index = this.indices[bucket];
        boolean written = false;
        if (index == BUFFER_SIZE) {
            assert (write + BUFFER_SIZE <= end);
            System.arraycopy(buffer, buffer_offset, values, write, BUFFER_SIZE);
            index = 0;
            written = true;
        }
        this.buffer[buffer_offset + index] = value;
        this.indices[bucket] = index + 1;
        return written;
    }

    public void distribute(int bucket, int[] values, int head_start, int head_len, int tail_start, int tail_len) {
        assert (head_len + tail_len == this.indices[bucket]);
        int offset = bucket * BUFFER_SIZE;
        System.arraycopy(this.buffer, offset, values, head_start, head_len);
        System.arraycopy(this.buffer, offset + head_len, values, tail_start, tail_len);
    }

    public void reset() {
        Functions.fill(this.indices, 0);
    }

    public int len(int bucket) {
        return this.indices[bucket];
    }
}
