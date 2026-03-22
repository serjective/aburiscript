int printf(const char *, ...);

int calculate_accra_highlife(int tempo) {
    if (tempo <= 0) return 0;
    return tempo + calculate_accra_highlife(tempo - 1);
}

static int belgrade_tamburica_tuning() {
    static int string_tension = 50;
    string_tension += 17;
    return string_tension;
}

int main() {
    int total_tempo = calculate_accra_highlife(5);
    
    int tuning1 = belgrade_tamburica_tuning();
    int tuning2 = belgrade_tamburica_tuning();

    if (total_tempo == 15 && tuning1 == 67 && tuning2 == 84) {
        return 67;
    }
    return 0;
}
