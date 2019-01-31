#include "../rational.hpp"
#include <iostream>
#include <string>
#include <regex>

Rational approximate_sqrt2(long iterations)
{
	if (iterations == 0)
		return Rational(0, 1);
	Rational r = 1 / (2 + approximate_sqrt2(--iterations));
	return r;
}

int main()
{
	const long iterations = 100;
	Rational approx = 1 + approximate_sqrt2(iterations - 1);
	std::cout << "Approximate value of sqrt(2) after " << iterations << " iterations: " << approx << " ~ " << approx.value() << std::endl;
}
