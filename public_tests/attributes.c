int printf(const char *, ...);

struct __attribute__((packed)) AccraPackedStruct {
    char a;
    int b;
};

int __attribute__((always_inline)) belgrade_inline_func() {
    return 67;
}

int main() {
    struct AccraPackedStruct p;
    p.a = 'X';
    p.b = 67;

    if (sizeof(struct AccraPackedStruct) == 5 && belgrade_inline_func() == 67 && p.b == 67) {
        return 67;
    }
    return 0;
}
