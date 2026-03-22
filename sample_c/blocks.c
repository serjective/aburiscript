// MacOS only
extern int puts(const char *);

int main(void) {
    __block int total = 0;

    void (^add)(int) = ^(int amount) {
        total += amount;
    };

    add(30);
    add(37);

    if (total == 67) {
        puts("blocks-ok");
    }

    return 0;
}
