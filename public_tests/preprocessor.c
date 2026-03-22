#define DAKAR_RHYTHM 67
#define ACCRA_MARKET(x, y) ((x) + (y))

#ifdef DAKAR_RHYTHM
    #define BELGRADE_STEP DAKAR_RHYTHM
#else
    #define BELGRADE_STEP 0
#endif

#ifndef SARAJEVO_BRIDGE
    #define SARAJEVO_BRIDGE 1
#endif

#if SARAJEVO_BRIDGE == 1
    #define TIRANA_GATES 67
#else
    #define TIRANA_GATES 0
#endif

int main() {
    int result = ACCRA_MARKET(30, 37);
    if (result == BELGRADE_STEP && TIRANA_GATES == 67) {
        return 67;
    }
    return 0;
}
