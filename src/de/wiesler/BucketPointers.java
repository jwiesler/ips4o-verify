package de.wiesler;

public class BucketPointers {
    // 2 * n integer (read, write)
    private final int[] buffer;

    private final int num_buckets;

    public BucketPointers(int[] bucket_starts, int num_buckets, int first_empty_position, int[] buffer) {
        this.buffer = buffer;
        this.num_buckets = num_buckets;

        for (int bucket = 0; bucket < num_buckets; ++bucket) {
            int start = Buffers.align_to_next_block(bucket_starts[bucket]);
            int stop = Buffers.align_to_next_block(bucket_starts[bucket + 1]);
            this.init(bucket, start, stop, first_empty_position);
        }
    }

    void init(int bucket, int start, int stop, int first_empty_position) {
        int read;
        if (first_empty_position <= start) {
            read = start;
        } else if (stop <= first_empty_position) {
            read = stop;
        } else {
            read = first_empty_position;
        }

        this.buffer[2 * bucket] = read;
        this.buffer[2 * bucket + 1] = start;
        assert (read >= 0 && start >= 0);
    }

    public static class Increment {
        public boolean occupied;
        public int position;

        public Increment(boolean occupied, int position) {
            this.occupied = occupied;
            this.position = position;
        }
    }

    public int write(int bucket) {
        final int write_pos = 2 * bucket + 1;
        return this.buffer[write_pos];
    }

    public Increment increment_write(int bucket) {
        final int read_pos = 2 * bucket;
        final int write_pos = 2 * bucket + 1;
        final int write = this.buffer[write_pos];
        this.buffer[write_pos] += Buffers.BUFFER_SIZE;
        assert (write >= 0);
        return new Increment(this.buffer[read_pos] > write, write);
    }

    // -1 if None
    public int decrement_read(int bucket) {
        final int read_pos = 2 * bucket;
        final int write_pos = 2 * bucket + 1;
        int read = this.buffer[read_pos];
        final int write = this.buffer[write_pos];
        if (read <= write) {
            return -1;
        } else {
            read -= Buffers.BUFFER_SIZE;
            this.buffer[read_pos] = read;
            return read;
        }
    }
}
