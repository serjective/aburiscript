extern "C" int puts(const char *);

int pick(int value) {
    return value;
}

int pick(long value) {
    return (int)value + 1;
}

int main() {
    if (pick(66) == 66 && pick(66L) == 67) {
        puts("overload-ok");
    }

    return 0;
}
