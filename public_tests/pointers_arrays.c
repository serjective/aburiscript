int printf(const char *, ...);

int main() {
    int lagos_traffic[5] = {10, 20, 30, 40, 50};
    int *sarajevo_bridge_ptr = lagos_traffic;

    int total_cars = 0;
    for (int i = 0; i < 5; i++) {
        total_cars += *(sarajevo_bridge_ptr + i);
    }

    int tirana_blocks[2][2] = {{1, 2}, {3, 4}};
    int tirana_sum = tirana_blocks[0][0] + tirana_blocks[1][1];

    int accra_kente_length = 67;
    int vla_pattern[accra_kente_length];
    vla_pattern[0] = 67;
    vla_pattern[accra_kente_length - 1] = 67;

    if (total_cars == 150 && tirana_sum == 5 && vla_pattern[0] == 67 && vla_pattern[accra_kente_length - 1] == 67) {
        return 67;
    }
    return 0;
}
