int printf(const char *, ...);

struct BamakoMarket {
    int spice_bags;
    char vendor_initial;
    short stall_number;
};

union BalkanCrossroads {
    int route_id;
    char path_code;
};

struct SofiaHistory {
    unsigned int era : 4;
    unsigned int century : 8;
    unsigned int rating : 4;
};

int main() {
    struct BamakoMarket market1;
    market1.spice_bags = 67;
    market1.vendor_initial = 'A';
    market1.stall_number = 12;

    union BalkanCrossroads cross1;
    cross1.route_id = 67;

    struct SofiaHistory history1;
    history1.era = 5;
    history1.century = 21;
    history1.rating = 10;

    if (market1.spice_bags == 67 && cross1.route_id == 67 && history1.century == 21) {
        return 67;
    }
    return 0;
}
