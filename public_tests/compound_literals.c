struct DakarPoint {
    int x;
    int y;
};

int main() {
    struct DakarPoint p = (struct DakarPoint){.x = 30, .y = 37};
    
    int *sarajevo_arr = (int[]){10, 20, 37};

    if (p.x + p.y == 67 && sarajevo_arr[2] == 37) {
        return 67;
    }
    return 0;
}
