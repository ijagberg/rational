
#include "../rational.hpp"

#include <iostream>
#include <string>
#include <regex>

Rational approximate(int n) {
	if (n == 0) return Rational(0,1);
	Rational r = 1 / (2 + approximate(--n));
	return r;
}

int main(int argc, char * argv[]) {
	if (argc != 2) {
		throw std::invalid_argument("usage: sqrt2 prec");
	} else {
		const std::regex r("[0-9]*");
		if (std::regex_match(argv[1], r)) {
			int n = atoi(std::string(argv[1]).c_str());
			if (n < 1) {
				throw std::invalid_argument("argument must be integer larger than zero");
			} else {
				Rational approx = 1 + approximate(n-1);
				std::cout << approx << " ~ " << approx.value() << "\n";
			}
		} else {
			throw std::invalid_argument("argument must be integer larger than zero");
		}
	}
}
