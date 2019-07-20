#include "../rational.hpp"
#include "../reduced_rational.hpp"

int main()
{
	Rational a(5);
	Rational r("53015/125");
	Rational b(678, 1093);
	Rational c = (r + b).reduce();
	Rational d = 0.587193874;
	Rational k = "0.5";
	ReducedRational x = d;
	std::cout << "Rational a(5): " << a << std::endl;
	std::cout << "Rational r(\"53015/125\"): " << r << std::endl;
	std::cout << "Rational b(678, 1093): " << b << std::endl;
	std::cout << "Rational c = (r+b).reduce(): " << c << std::endl;
	std::cout << "Rational d = 0.587193874: " << d << std::endl;
	std::cout << "Rational k = \"0.5\": " << k << std::endl;
	std::cout << "ReducedRational x = d: " << x << std::endl;
	return 1;
}