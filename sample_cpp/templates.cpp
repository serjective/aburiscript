extern "C" int puts(const char *);

template <typename T>
T twice(T value) {
    return value + value;
}

int main() {
    if (twice<int>(33) == 66) {
        puts("template-ok");
    }
    return 0;
}
