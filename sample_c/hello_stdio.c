#include <stdio.h>

int main(void) {
    const char *names[] = {"Aburi", "Ghana", "Serbia", "Croatia", "Romania", "Albania", "Compiler"};
    for (int i = 0; i < 7; ++i) {
        printf("Maakye! Zdravo! Buna! Pershendetje! Hello from %s\n", names[i]);
    }

    return 0;
}
