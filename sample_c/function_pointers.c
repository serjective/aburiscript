extern int printf(const char *, ...);

typedef int (*binary_fn)(int, int);

static int add(int a, int b) {
    return a + b;
}

static int apply(binary_fn fn, int lhs, int rhs) {
    return fn(lhs, rhs);
}

int main(void) {
    printf("fptr=%d\n", apply(add, 30, 37));
    return 0;
}
