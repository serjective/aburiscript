extern "C" int puts(const char *);

struct Box {
    int value;
};

int main() {
    int Box::* member = &Box::value;
    Box box = {67};

    if (box.*member == 67) {
        puts("member-ptr-ok");
    }

    return 0;
}
