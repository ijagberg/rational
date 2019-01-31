
#include "rational.hpp"
#include "reduced_rational.hpp"

int main()
{
	Rational a(5);
	Rational r("53015/125");
	Rational b(678, 1093);
	Rational c = "53015/120";
	Rational d = 0.587193874;
	std::cout << "a: " << a << std::endl;
	std::cout << "r: " << r << std::endl;
	std::cout << "b: " << b << std::endl;
	std::cout << "(r+b).reduce(): " << (r + b).reduce() << std::endl;
	std::cout << "c: " << c << std::endl;
	std::cout << "d: " << d << std::endl;
	return 1;
}