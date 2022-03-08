package de.wiesler;

public final class SampleParameters {
    public final int num_samples;
    public final int num_buckets;
    public final int step;

    /*@ public normal_behaviour
      @ requires n >= Constants.BASE_CASE_SIZE;
      @ ensures 1 <= \result && \result <= Constants.LOG_MAX_BUCKETS;
      @ // Only the lower log bound holds since the function might yield a smaller result
      @ ensures (1 << \result) * Constants.BASE_CASE_SIZE <= n;
      @
      @ assignable \strictly_nothing;
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

    public static /*@ strictly_pure */ int oversampling_factor(int n) {
        return Constants.log2(n) / 5;
    }

    /*@ public model_behaviour
      @ requires n >= 1;
      @ model no_state boolean isValidForLen(int n) {
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

    /*@ public normal_behaviour
      @ requires n >= Constants.ACTUAL_BASE_CASE_SIZE;
      @ ensures this.isValidForLen(n);
      @ assignable \strictly_nothing;
      @*/
    public SampleParameters(int n) {
        int log_buckets = log_buckets(n);
        this.num_buckets = 1 << log_buckets;
        this.step = Functions.max(1, oversampling_factor(n));
        this.num_samples = step * num_buckets - 1;
    }
}
