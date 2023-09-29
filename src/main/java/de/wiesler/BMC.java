package de.wiesler;

public final class BMC {
    public static void testAll() {
        for (int i = 0; i >= 0; i++) {
            Constants.testContracts(i);
            Buffers.testContracts(i);
            SampleParameters.testContracts(i);
        }
    }

    public static void main(String[] args) {
        testAll();
    }
}
