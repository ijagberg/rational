
#include "rational.hpp"
#include "reduced_rational.hpp"

int main() {
	Rational r("53015/125");
	Rational b(678, 1093);
    Rational c = "53015/120";
	std::cout << r << "\n";
	std::cout << b << "\n";
	std::cout << (r + b).reduce() << "\n";
    std::cout << c << "\n";
	return 1;
}