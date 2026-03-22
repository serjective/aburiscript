extern "C" int puts(const char *);

struct Base {
    int value;

    Base() : value(10) {}
};

struct Derived : Base {
    int extra;

    Derived() : Base(), extra(57) {}
};

int main() {
    Derived stack;
    Derived *heap = new Derived();
    int total = stack.value + heap->extra;

    if (total == 67) {
        puts("class-ok");
    }

    delete heap;
    return 0;
}
