int belgrade_pick_reference(int& value) {
    return value;
}

int main() {
    int accra_value = 67;
    int& dakar_alias = accra_value;
    return belgrade_pick_reference(dakar_alias);
}
