#include <iostream>
#include <string>

void __attribute__((noinline)) f(int x) {
    throw std::string("hi");
}

void __attribute__((noinline)) g(int a, int b) {
    f(a+b);
}

int main() {
    g(2,3);
}
