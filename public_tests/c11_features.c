_Static_assert(sizeof(int) >= 4, "Integers must be at least 4 bytes");

_Thread_local int belgrade_tls_value = 67;

int main() {
    _Alignas(16) int accra_aligned_var = 67;
    
    unsigned long alignment_check = (unsigned long)&accra_aligned_var;
    
    if (alignment_check % 16 == 0 && belgrade_tls_value == 67) {
        return 67;
    }
    return 0;
}
