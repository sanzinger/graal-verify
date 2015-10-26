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

}
