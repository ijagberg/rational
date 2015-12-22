
#include "../rational.hpp"

int main() {
	Rational a("-3/2");
	Rational b(3, 4);
	Rational c = a%b;

	std::cout << c << "\n";
}