#include <stdio.h>

struct Point {
    int x;
    int y;
};

static int dot_sum(const struct Point *points, int count) {
    int scratch[count];
    int total = 0;

    for (int i = 0; i < count; ++i) {
        scratch[i] = points[i].x * points[i].y;
        total += scratch[i];
    }

    return total;
}

int main(void) {
    struct Point points[] = {
        {2, 3},
        {4, 5},
        {6, 7},
    };

    printf("dot-sum=%d\n", dot_sum(points, 3));
    return 0;
}
