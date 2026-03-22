extern int printf(const char *, ...);

struct __attribute__((packed)) Packet {
    unsigned char tag;
    unsigned int value;
};

static int add(int a, int b) {
    return a + b;
}

int main(void) {
    struct Packet packet = {7, 60};
    int offset = __builtin_offsetof(struct Packet, value);
    int total = add(packet.tag, packet.value) + offset;

    printf("attrs=%d total=%d\n", offset, total);
    return 0;
}
