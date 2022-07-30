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

        System.out.println(len + "," + count + "," + sum + "," + sum_std);
    }

    public static void main(String[] args) {
//        bench(1 << 8, 1_000_000);
//        bench(1 << 9, 1_000_000);
//        bench(1 << 10, 1_000_000);
//        bench(1 << 11, 1_000_000);
//        bench(1 << 12, 1_000_000);
//        bench(1 << 13, 100_000);
//        bench(1 << 14, 100_000);
//        bench(1 << 15, 100_000);
        bench(1 << 16, 100_000);
//        bench(1 << 17, 100_000);
//        bench(1 << 18, 10_000);
//        bench(1 << 19, 10_000);
//        bench(1 << 20, 10_000);
        bench(1 << 21, 1_000);
        bench(1 << 22, 1_000);
        bench(1 << 23, 1_000);
        bench(1 << 24, 100);
        bench(1 << 25, 100);
        bench(1 << 26, 100);
        bench(1 << 27, 10);
        bench(1 << 28, 5);

//        bench(1 << 29, 10_000_000);
//        bench(1 << 30, 10_000_000);
//        bench(1_000, 1_000_000);
//        bench(10_000, 100_000);
//        bench(100_000, 10_000);
//        bench(1_000_000, 1_000);
//        bench(10_000_000, 100);
//        bench(100_000_000, 10);
//        bench(1_000_000_000, 5);
//        ----- 10 -----
//        Sort:     940370700 (9.403707 per element)
//        Std Sort: 880247800 (8.802478 per element)
//        ----- 100 -----
//        Sort:     18558055600 (18.558056 per element)
//        Std Sort: 18562744200 (18.562744 per element)
//        ----- 1000 -----
//        Sort:     26059955700 (26.059956 per element)
//        Std Sort: 27373053000 (27.373055 per element)
//        ----- 10000 -----
//        Sort:     33152474000 (33.152473 per element)
//        Std Sort: 35754726400 (35.754726 per element)
//        ----- 100000 -----
//        Sort:     37513429700 (37.513428 per element)
//        Std Sort: 44528879300 (44.528877 per element)
//        ----- 1000000 -----
//        Sort:     43522675200 (43.522675 per element)
//        Std Sort: 53386577500 (53.386578 per element)
//        ----- 10000000 -----
//        Sort:     49033964600 (49.033966 per element)
//        Std Sort: 62888663300 (62.888664 per element)
//        ----- 100000000 -----
//        Sort:     55316603600 (55.316605 per element)
//        Std Sort: 73520891800 (73.52089 per element)
//        ----- 1000000000 -----
//        Sort:     309287392600 (438.68515 per element)
//        Std Sort: 414275035200 (587.5969 per element)
    }
}
