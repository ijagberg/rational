
// #include "reduced_rational.hpp"

// ReducedRational::ReducedRational() : Rational()
// {
// }

// ReducedRational::ReducedRational(const double &n) : Rational(n)
// {
// 	reduce();
// }

// ReducedRational::ReducedRational(const long &n, const long &d) : Rational(n, d)
// {
// 	reduce();
// }

// ReducedRational::ReducedRational(const char *cp) : ReducedRational(std::string(cp))
// {
// }

// ReducedRational::ReducedRational(const std::string &str) : Rational(str)
// {
// 	reduce();
// }

// ReducedRational::ReducedRational(const Rational &other)
// {
// 	this->numerator = other.numerator;
// 	this->denominator = other.denominator;
// 	reduce();
// }

// ReducedRational::ReducedRational(const ReducedRational &other)
// {
// 	this->numerator = other.numerator;
// 	this->denominator = other.denominator;
// }

// ReducedRational::~ReducedRational()
// {
// }

// bool ReducedRational::isReduced() const
// {
// 	return true;
// }

// void ReducedRational::reduce()
// {
// 	long i = gcd();
// 	numerator /= i;
// 	denominator /= i;
// }