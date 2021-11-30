package de.wiesler;

public class Main {

    public static void main(String[] args) {
        var random = new java.util.Random(42);
        var storage = new Storage();

        for (int j = 0; j < 1000000; ++j) {
            int[] values = random.ints(100_000_000 + random.nextInt(100000), 0, 1000 + random.nextInt(10000)).toArray();
//            System.out.println(Arrays.toString(values));
            int[] copy = java.util.Arrays.copyOf(values, values.length);

            var before = System.nanoTime();
            Sorter.sort(values, 0, values.length, storage);
            var elapsed = System.nanoTime() - before;
            int inversion = Functions.isSorted(values, 0, values.length);
            if (inversion != -1) {
                System.out.println(java.util.Arrays.toString(copy));
                System.out.println("At position " + (inversion) + ", " + (inversion + 1) + ": " + values[inversion] + " > " + values[inversion - 1]);
                System.out.println(java.util.Arrays.toString(values));
                return;
            }

            var before_std = System.nanoTime();
            java.util.Arrays.sort(copy);
            var elapsed_std = System.nanoTime() - before_std;

            System.out.println("Sort took " + elapsed + " vs " + elapsed_std);

            assert (java.util.Arrays.equals(values, copy));
        }
    }
}
