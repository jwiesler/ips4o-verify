package de.wiesler;

public class Main {
    private static void bench(int len, int count) {
        var storage = new Storage();
        long sum = 0;
        long sum_std = 0;
        var random = new java.util.Random(42);
        for (int j = 0; j < count; ++j) {
            int[] values = random.ints(len, 0, len).toArray();
            var before = System.nanoTime();
            Sorter.sort(values, 0, values.length, storage);
            var elapsed = System.nanoTime() - before;
            sum += elapsed;
        }

        random = new java.util.Random(42);
        for (int j = 0; j < count; ++j) {
            int[] values = random.ints(len, 0, len).toArray();
            var before_std = System.nanoTime();
            java.util.Arrays.sort(values);
            var elapsed_std = System.nanoTime() - before_std;
            sum_std += elapsed_std;
        }

        System.out.println("----- " + len + " -----");
        System.out.println("Sort:     " + sum + " (" + (((float) sum) / (len * count)) + " per element)");
        System.out.println("Std Sort: " + sum_std + " (" + (((float) sum_std) / (len * count)) + " per element)");
    }

    public static void main(String[] args) {
        bench(10, 10_000_000);
        bench(100, 10_000_000);
        bench(1_000, 1_000_000);
        bench(10_000, 100_000);
        bench(100_000, 10_000);
        bench(1_000_000, 1_000);
        bench(10_000_000, 100);
        bench(100_000_000, 10);
        bench(1_000_000_000, 5);
//        ----- 10 -----
//        Sort:     905888700 (9.0588875 per element)
//        Std Sort: 892957500 (8.929575 per element)
//        ----- 100 -----
//        Sort:     18561045400 (18.561045 per element)
//        Std Sort: 18174935300 (18.174934 per element)
//        ----- 1000 -----
//        Sort:     26170475500 (26.170475 per element)
//        Std Sort: 26499804300 (26.499805 per element)
//        ----- 10000 -----
//        Sort:     32742429600 (32.742428 per element)
//        Std Sort: 36155426200 (36.155426 per element)
//        ----- 100000 -----
//        Sort:     36185792000 (36.18579 per element)
//        Std Sort: 44252235400 (44.252235 per element)
//        ----- 1000000 -----
//        Sort:     41604779300 (41.60478 per element)
//        Std Sort: 53309309000 (53.309307 per element)
//        ----- 10000000 -----
//        Sort:     47757276800 (47.757275 per element)
//        Std Sort: 62458377500 (62.458378 per element)
//        ----- 100000000 -----
//        Sort:     26525384300 (53.05077 per element)
//        Std Sort: 35730585400 (71.46117 per element)
//        ----- 1000000000 -----
//        Sort:     116565178600 (58.28259 per element)
//        Std Sort: 162293283000 (81.146645 per element)
    }
}
