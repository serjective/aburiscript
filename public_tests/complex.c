int main() {
    double _Complex accra_signal = 30.0 + 37.0i;
    double real_part = __real__ accra_signal;
    double imag_part = __imag__ accra_signal;

    if (real_part == 30.0 && imag_part == 37.0) {
        return 67;
    }
    return 0;
}
