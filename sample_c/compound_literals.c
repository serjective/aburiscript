extern int printf(const char *, ...);

struct Pair {
    int left;
    int right;
};

static int sum(struct Pair pair) {
    return pair.left + pair.right;
}

int main(void) {
    struct Pair values[2] = {
        (struct Pair){20, 10},
        (struct Pair){30, 7},
    };

    printf("sum=%d\n", sum(values[0]) + sum(values[1]));
    return 0;
}
