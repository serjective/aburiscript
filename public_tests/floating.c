int printf(const char *, ...);

int main() {
    double dakar_temperature = 35.5;
    float sarajevo_snow = 12.0f;

    double combined_weather = dakar_temperature + sarajevo_snow;
    
    int result = (int)combined_weather;

    if (result == 47) {
        return 67;
    }
    return 0;
}
