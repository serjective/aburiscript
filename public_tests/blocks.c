int printf(const char *, ...);

int main() {
    __block int dakar_counter = 0;

    void (^bucharest_increment)(int) = ^(int amount) {
        dakar_counter += amount;
    };

    bucharest_increment(30);
    bucharest_increment(37);

    int (^accra_multiplier)(int, int) = ^(int a, int b) {
        return a * b;
    };

    if (dakar_counter == 67 && accra_multiplier(1, 67) == 67) {
        return 67;
    }
    return 0;
}
