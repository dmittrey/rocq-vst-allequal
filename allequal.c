#include <stddef.h>

// 0 - equals
// 1 - not equal
unsigned allequal(unsigned a[], int n) {
    int i; unsigned s;
    i = 0;
    // При отрицательном размере или пустом массиве возвращаем равенство
    if (n <= 0)
        return 0;

    // Иначе смотрим поэлементно
    s = a[0];
    while (i < n) {
        if (a[i] != s)
            return 1;
        i++;
    }
    return 0;
}

unsigned four[4] = {1,2,3,4};

int main(void) {
    unsigned int s;
    s = allequal(four,4);
    return (int)s;
}