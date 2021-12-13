package de.wiesler;

public class Constants {
    public static final int BASE_CASE_SIZE = 32;
    public static final int LOG_MAX_BUCKETS = 6;
    public static final int MAX_BUCKETS = 1 << (LOG_MAX_BUCKETS + 1);
    public static final int SINGLE_LEVEL_THRESHOLD = BASE_CASE_SIZE * (1 << LOG_MAX_BUCKETS);
    public static final int TWO_LEVEL_THRESHOLD = SINGLE_LEVEL_THRESHOLD * (1 << LOG_MAX_BUCKETS);
    public static final int EQUAL_BUCKETS_THRESHOLD = 5;

    /*@ public normal_behaviour
      @ ensures \result > 0;
      @ ensures 1 << (\result + 1) <= n;
      @ ensures n <= 1 << \result;
      @ assignable \strictly_nothing;
      @*/
    public static int log2(int n) {
        int log = 0;
        if ((n & 0xffff0000) != 0) {
            n >>>= 16;
            log = 16;
        }
        if (n >= 256) {
            n >>>= 8;
            log += 8;
        }
        if (n >= 16) {
            n >>>= 4;
            log += 4;
        }
        if (n >= 4) {
            n >>>= 2;
            log += 2;
        }
        return log + (n >>> 1);
    }

    /*@ public normal_behaviour
      @ ensures \result == (b ? 1 : 0);
      @ assignable \strictly_nothing;
      @*/
    public static int toInt(boolean b) {
        return b ? 1 : 0;
    }

    /*@ public normal_behaviour
      @ ensures \result == (a < b);
      @ assignable \strictly_nothing;
      @*/
    public static boolean cmp(int a, int b) {
        return a < b;
    }

    /*@ public normal_behaviour
      @ ensures \result > 0 && \result <= LOG_MAX_BUCKETS;
      @ ensures 1 << (\result + 1) <= n;
      @ ensures n <= 1 << \result;
      @ assignable \strictly_nothing;
      @*/
    public static int log_buckets(int n) {
        if (n <= SINGLE_LEVEL_THRESHOLD) {
            // Only one more level until the base case, reduce the number of buckets
            return Functions.max(1, log2(n / BASE_CASE_SIZE));
        } else if (n <= TWO_LEVEL_THRESHOLD) {
            // Only two more levels until we reach the base case, split the buckets
            // evenly
            return Functions.max(1, (log2(n / BASE_CASE_SIZE) + 1) / 2);
        } else {
            // Use the maximum number of buckets
            return LOG_MAX_BUCKETS;
        }
    }

    /*@ public normal_behaviour
      @ ensures \result > 0;
      @ assignable \strictly_nothing;
      @*/
    public static int oversampling_factor(int n) {
        final double v = 0.2 * log2(n);
        return Functions.max((int) v, 1);
    }
}
