extern "C" int puts(const char *);

int choose(int &value) {
    return value;
}

int main() {
    int n = 67;
    int &alias = n;

    if (choose(alias) == 67) {
        puts("reference-ok");
    }

    return 0;
}
