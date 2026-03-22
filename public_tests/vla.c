int printf(const char *, ...);

int calculate_vla_sum(int lagos_size) {
    int accra_kente[lagos_size];
    int sum = 0;
    for (int i = 0; i < lagos_size; i++) {
        accra_kente[i] = i + 1;
        sum += accra_kente[i];
    }
    return sum;
}

int main() {
    int sarajevo_length = 10;
    int bucharest_grid[sarajevo_length][sarajevo_length];

    for (int i = 0; i < sarajevo_length; i++) {
        for (int j = 0; j < sarajevo_length; j++) {
            bucharest_grid[i][j] = i * j;
        }
    }

    int n = 67;
    int dakar_dynamic[n];
    dakar_dynamic[n - 1] = 67;

    if (calculate_vla_sum(5) == 15 && bucharest_grid[9][9] == 81 && dakar_dynamic[66] == 67) {
        return 67;
    }
    return 0;
}
