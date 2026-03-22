struct BelgradeMonument {
    char name;
    double height;
    int age;
};

int main() {
    int offset_age = __builtin_offsetof(struct BelgradeMonument, age);
    
    int is_same = __builtin_types_compatible_p(int, int);
    int is_diff = __builtin_types_compatible_p(int, float);

    if (is_same == 1 && is_diff == 0) {
        return 67;
    }
    return 0;
}
