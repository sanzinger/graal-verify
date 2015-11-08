package at.sanzinger.graal.verify.test;

import org.junit.Test;

public class IntExamples extends VerificationTest {

    public static int addMinSnippet(int a, int b, int sum) {
        int min;
        if (a < b) {
            min = a;
        } else {
            min = b;
        }
        return min + sum;
    }

    @Test
    public void addMin() {
        compile("addMinSnippet");
    }

    public static int inverseNegativeSnippet(int a, boolean c) {
        int x;
        if (c) {
            x = a + 1;
        } else {
            x = -~a;
        }
        return x;
    }

    @Test
    public void inverseNegative() {
        compile("inverseNegativeSnippet");
    }

    public static int negativeInverseSnippet(int a, boolean c) {
        int x;
        if (c) {
            x = a - 1;
        } else {
            x = ~-a;
        }
        return x;
    }

    @Test
    public void negativeInverse() {
        compile("negativeInverseSnippet");
    }

    public static int addInverseSnippet(int a, boolean c) {
        int x;
        if (c) {
            x = 0xFFFFFFFF;
        } else {
            x = a + ~a;
        }
        return x;
    }

    @Test
    public void addInverse() {
        compile("addInverseSnippet");
    }

    public static int negativeInverseThreeSnippet(int a, int c) {
        int x;
        if (c == 1) {
            x = a - 1;
        } else if (c == 2) {
            x = 42;
        } else {
            x = ~-a;
        }
        return x + c;
    }

    @Test
    public void negativeInverseThree() {
        compile("negativeInverseThreeSnippet");
    }

    public static int countingLoopSnippet(int c) {
        int i = 0;
        while (i < c) {
            i++;
        }
        return i;
    }

    @Test
    public void countingLoop() {
        compile("countingLoopSnippet");
    }

    public static int fibSnippet(int n) {
        if (n <= 1) {
            return n;
        } else {
            return fibSnippet(n - 1) + fibSnippet(n - 2);
        }
    }

    @Test
    public void fib() {
        compile("fibSnippet");
    }

    public static int ulamSnippet(int an) {
        int n = an;
        if (n % 2 == 0) {
            n = n / 2;
        } else {
            n = 3 * n + 1;
        }
        return n;
    }

    @Test
    public void ulam() {
        compile("ulamSnippet");
    }

    public static long d2lSnippet(double d) {
        return (long) d;
    }

    @Test
    public void d2l() {
        compile("d2lSnippet");
    }

    /**
     * @author http://rsb.info.nih.gov/nih-image/java/benchmarks/Sieve.java
     */
    @SuppressWarnings("unused")
    private static int sieveSnippet() {
        int SIZE = 8190;
        boolean flags[] = new boolean[SIZE + 1];
        int i, prime, k, iter, count;
        int iterations = 0;
        double seconds = 0.0;
        int score = 0;
        long startTime, elapsedTime;

        startTime = System.currentTimeMillis();
        while (true) {
            count = 0;
            for (i = 0; i <= SIZE; i++)
                flags[i] = true;
            for (i = 0; i <= SIZE; i++) {
                if (flags[i]) {
                    prime = i + i + 3;
                    for (k = i + prime; k <= SIZE; k += prime)
                        flags[k] = false;
                    count++;
                }
            }
            iterations++;
            elapsedTime = System.currentTimeMillis() - startTime;
            if (elapsedTime >= 10000)
                break;
        }
        seconds = elapsedTime / 1000.0;
        score = (int) Math.round(iterations / seconds);
        return score;
    }

    @Test
    public void sieve() {
        compile("sieveSnippet");
    }
}
