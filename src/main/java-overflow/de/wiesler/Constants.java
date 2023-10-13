package de.wiesler;

public final class Constants {
    public static final int BASE_CASE_SIZE = 32;
    public static final int ACTUAL_BASE_CASE_SIZE = 4 * BASE_CASE_SIZE;
    public static final int LOG_MAX_BUCKETS = 8;
    public static final int MAX_BUCKETS = 1 << (LOG_MAX_BUCKETS + 1);
    public static final int SINGLE_LEVEL_THRESHOLD = BASE_CASE_SIZE * (1 << LOG_MAX_BUCKETS);
    public static final int TWO_LEVEL_THRESHOLD = SINGLE_LEVEL_THRESHOLD * (1 << LOG_MAX_BUCKETS);
    public static final int EQUAL_BUCKETS_THRESHOLD = 5;

    /*@ public model_behaviour
      @ requires n > 0;
      @ static no_state model boolean isLog2Of(int n, int log) {
      @     return log >= 0 &&
      @         log <= 30 &&
      @         (1 << log) <= n &&
      @         (log != 30 ==> n < (1 << (log + 1)));
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires_free n > 0;
      @
      @ ensures_free isLog2Of(n, \result);
      @
      @ assignable_free \strictly_nothing;
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

    private static boolean testLogContract(int n, int log) {
        return log >= 0 &&
            log <= 30 &&
            (1 << log) <= n &&
            (log == 30 || n < (1 << (log + 1)));
    }

    public static void testContracts(int i) {
        if (i > 0 && !testLogContract(i, log2(i))) {
            throw new Error("log2 contract fails for " + i);
        }
    }

    public static /*@ strictly_pure */ int toInt(boolean b) {
        return b ? 1 : 0;
    }

    public static /*@ strictly_pure */ boolean cmp(int a, int b) {
        return a < b;
    }
}
