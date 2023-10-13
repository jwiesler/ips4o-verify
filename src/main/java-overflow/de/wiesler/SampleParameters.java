package de.wiesler;

public final class SampleParameters {
    public final int num_samples;
    public final int num_buckets;
    public final int step;

    /*@ public normal_behaviour
      @ requires_free n >= Constants.BASE_CASE_SIZE;
      @
      @ assignable_free \strictly_nothing;
      @*/
    public static int log_buckets(int n) {
        if (n <= Constants.SINGLE_LEVEL_THRESHOLD) {
            // Only one more level until the base case, reduce the number of buckets
            return Functions.max(1, Constants.log2(n / Constants.BASE_CASE_SIZE));
        } else if (n <= Constants.TWO_LEVEL_THRESHOLD) {
            // Only two more levels until we reach the base case, split the buckets
            // evenly
            return Functions.max(1, (Constants.log2(n / Constants.BASE_CASE_SIZE) + 1) / 2);
        } else {
            // Use the maximum number of buckets
            return Constants.LOG_MAX_BUCKETS;
        }
    }

    /*@ public normal_behaviour
      @ requires_free n >= Constants.BASE_CASE_SIZE;
      @
      @ assignable_free \strictly_nothing;
      @*/
    public static int oversampling_factor(int n) {
        return Constants.log2(n) / 5;
    }

    /*@ public model_behaviour
      @ requires true;
      @ accessible \nothing;
      @ model boolean isValidForLen(int n) {
      @     return
      @         3 <= this.num_samples <= n / 2 &&
      @         // This states the same as the previous line but is somehow hard to deduce
      @         this.num_samples < n &&
      @         1 <= this.step &&
      @         2 <= this.num_buckets <= 1 << Constants.LOG_MAX_BUCKETS &&
      @         this.num_buckets % 2 == 0 &&
      @         // there are enough samples to perform num_buckets selections with the given step size
      @         this.step * this.num_buckets - 1 <= this.num_samples;
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @ accessible \nothing;
      @ model boolean isInInt() {
      @     return
      @         \dl_inInt(this.num_samples) &&
      @         \dl_inInt(this.step) &&
      @         \dl_inInt(this.num_buckets);
      @ }
      @*/

    private static boolean isValidForLen(SampleParameters p, int n) {
        return
            3 <= p.num_samples && p.num_samples <= n / 2 &&
            p.num_samples < n &&
            1 <= p.step &&
            2 <= p.num_buckets && p.num_buckets <= 1 << Constants.LOG_MAX_BUCKETS &&
            p.num_buckets % 2 == 0 &&
            p.step * p.num_buckets - 1 <= p.num_samples;
    }

    /*@ public normal_behaviour
      @ requires_free n >= Constants.ACTUAL_BASE_CASE_SIZE;
      @ ensures_free this.isValidForLen(n) && this.isInInt();
      @ assignable_free \nothing;
      @*/
    public SampleParameters(int n) {
        int log_buckets = log_buckets(n);
        this.num_buckets = 1 << log_buckets;
        this.step = Functions.max(1, oversampling_factor(n));
        this.num_samples = step * num_buckets - 1;
    }

    public static void testContracts(int i) {
        if (i >= Constants.ACTUAL_BASE_CASE_SIZE && !isValidForLen(new SampleParameters(i), i)) {
            throw new Error("SampleParameters contract fails for " + i);
        }
    }
}
