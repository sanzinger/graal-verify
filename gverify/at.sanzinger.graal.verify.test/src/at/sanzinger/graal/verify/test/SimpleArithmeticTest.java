package at.sanzinger.graal.verify.test;

import org.junit.Test;

public class SimpleArithmeticTest extends VerificationTest {

    public static double doubleAddSnippet(double a, double b) {
        return a + b;
    }

    @Test
    public void doubleAdd() {
        compile("doubleAddSnippet");
    }

    public static double doubleSubSnippet(double a, double b) {
        return a - b;
    }

    @Test
    public void doubleSub() {
        compile("doubleSubSnippet");
    }

    public static double doubleMulSnippet(double a, double b) {
        return a * b;
    }

    @Test
    public void doubleMul() {
        compile("doubleMulSnippet");
    }

    public static double doubleDivSnippet(double a, double b) {
        return a / b;
    }

    @Test
    public void doubleDiv() {
        compile("doubleDivSnippet");
    }

    public static double floatAddSnippet(float a, float b) {
        return a + b;
    }

    @Test
    public void floatAdd() {
        compile("floatAddSnippet");
    }

    public static float floatSubSnippet(float a, float b) {
        return a - b;
    }

    @Test
    public void floatSub() {
        compile("floatSubSnippet");
    }

    public static float floatMulSnippet(float a, float b) {
        return a * b;
    }

    @Test
    public void floatMul() {
        compile("floatMulSnippet");
    }

    public static float floatDivSnippet(float a, float b) {
        return a / b;
    }

    @Test
    public void floatDiv() {
        compile("floatDivSnippet");
    }

    public static double intAddSnippet(int a, int b) {
        return a + b;
    }

    @Test
    public void intAdd() {
        compile("intAddSnippet");
    }

    public static int intSubSnippet(int a, int b) {
        return a - b;
    }

    @Test
    public void intSub() {
        compile("intSubSnippet");
    }

    public static int intMulSnippet(int a, int b) {
        return a * b;
    }

    @Test
    public void intMul() {
        compile("intMulSnippet");
    }

    public static int intDivSnippet(int a, int b) {
        return a / b;
    }

    @Test
    public void intDiv() {
        compile("intDivSnippet");
    }

    public static double longAddSnippet(long a, long b) {
        return a + b;
    }

    @Test
    public void longAdd() {
        compile("longAddSnippet");
    }

    public static long longSubSnippet(long a, long b) {
        return a - b;
    }

    @Test
    public void longSub() {
        compile("longSubSnippet");
    }

    public static long longMulSnippet(long a, long b) {
        return a * b;
    }

    @Test
    public void longMul() {
        compile("longMulSnippet");
    }

    public static long longDivSnippet(long a, long b) {
        return a / b;
    }

    @Test
    public void longDiv() {
        compile("longDivSnippet");
    }

}
