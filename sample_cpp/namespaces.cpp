extern "C" int puts(const char *);

namespace math {
int value() { return 67; }
}

int main() {
    if (math::value() == 67) {
        puts("namespace-ok");
    }

    return 0;
}
