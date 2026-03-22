#include <stdio.h>

struct __attribute__((packed)) Packet {
    unsigned char tag;
    unsigned short value;
};

_Static_assert(sizeof(struct Packet) == 3, "packed packet should be 3 bytes");

int main(void) {
    _Alignas(16) int values[3] = {4, 8, 15};
    struct Packet packet = {.tag = 7, .value = 42};
    struct Packet copy = (struct Packet){.tag = packet.tag + 1, .value = packet.value + values[0]};

    printf("align=%d packet={tag=%u value=%u}\n",
           (int)(_Alignof(values)),
           (unsigned)copy.tag,
           (unsigned)copy.value);
    return 0;
}
