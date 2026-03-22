#include <stdarg.h>

extern int printf(const char *, ...);

static int sum3(int count, ...) {
    va_list ap;
    va_start(ap, count);

    int total = 0;
    for (int i = 0; i < count; ++i) {
        total += va_arg(ap, int);
    }

    va_end(ap);
    return total;
}

int main(void) {
    printf("varargs=%d\n", sum3(3, 20, 20, 27));
    return 0;
}
