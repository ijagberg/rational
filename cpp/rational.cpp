
// #include "rational.hpp"
// #include "reduced_rational.hpp"

// #include <sstream>
// #include <vector>
// #include <regex>

// Rational::Rational() : numerator(0),
// 					   denominator(1)
// {
// }

// Rational::Rational(const long &n, const long &d) : numerator(n),
// 												   denominator(d)
// {
// 	if (d == 0)
// 		throw std::invalid_argument("Denominator can't be 0");
// 	if (d < 0)
// 	{
// 		numerator = -n;
// 		denominator = -d;
// 	}
// }

// Rational::Rational(const double &value)
// {
// 	double num = value;
// 	long den = 1;
// 	while (num != (long)num)
// 	{
// 		num *= 10.0;
// 		den *= 10.0;
// 	}
// 	numerator = num;
// 	denominator = den;
// }

// Rational::Rational(const char *cp) : Rational(std::string(cp))
// {
// }

// Rational::Rational(const std::string &str)
// {
// 	if (std::regex_match(str, type_1))
// 	{
// 		*this = Rational(atof(str.c_str()));
// 	}
// 	else if (std::regex_match(str, type_2))
// 	{
// 		std::vector<std::string> values;
// 		std::istringstream iss(str);
// 		std::string item;
// 		while (std::getline(iss, item, '/'))
// 		{
// 			values.push_back(item);
// 		}
// 		numerator = atol(values[0].c_str());
// 		denominator = atol(values[1].c_str());
// 		if (denominator == 0)
// 		{
// 			throw std::invalid_argument("Denominator can't be 0");
// 		}
// 		else if (denominator < 0)
// 		{
// 			numerator *= -1;
// 			denominator *= -1;
// 		}
// 	}
// 	else
// 	{
// 		throw std::invalid_argument("Wrong format for string constructor");
// 	}
// }

// Rational::Rational(const Rational &other)
// {
// 	this->numerator = other.numerator;
// 	this->denominator = other.denominator;
// }

// Rational::Rational(const ReducedRational &other)
// {
// 	this->numerator = other.numerator;
// 	this->denominator = other.denominator;
// }

// Rational::~Rational()
// {
// }

// long Rational::gcd() const
// {
// 	long num = numerator;
// 	long den = denominator;
// 	long temp;

// 	if (num < den)
// 	{ //If num is less than den, swap num and den
// 		temp = num;
// 		num = den;
// 		den = temp;
// 	}

// 	long r;
// 	while (den != 0)
// 	{
// 		r = num % den;
// 		num = den;
// 		den = r;
// 	}
// 	return num;
// }

// double Rational::value() const
// {
// 	return (double)numerator / (double)denominator;
// }

// Rational Rational::inverse() const
// {
// 	if (numerator == 0)
// 		throw std::invalid_argument("Can't get inverse when numerator is 0");
// 	;
// 	return Rational(this->denominator, this->numerator);
// }

// Rational Rational::reduce() const
// {
// 	long i = gcd();
// 	return Rational(numerator / i, denominator / i);
// }

// bool Rational::isReduced() const
// {
// 	return *this == this->reduce();
// }

// Rational &Rational::operator+=(const Rational &rhs)
// {
// 	if (this->denominator == rhs.denominator)
// 	{
// 		this->numerator = this->numerator + rhs.numerator;
// 	}
// 	else
// 	{
// 		this->numerator = (this->numerator * rhs.denominator) + (this->denominator * rhs.numerator);
// 		this->denominator = (this->denominator * rhs.denominator);
// 	}
// 	return *this;
// }

// Rational &Rational::operator-=(const Rational &rhs)
// {
// 	if (this->denominator == rhs.denominator)
// 	{
// 		this->numerator = this->numerator - rhs.numerator;
// 	}
// 	else
// 	{
// 		this->numerator = (this->numerator * rhs.denominator) - (this->denominator * rhs.numerator);
// 		this->denominator = (this->denominator * rhs.denominator);
// 	}
// 	return *this;
// }

// Rational &Rational::operator*=(const Rational &rhs)
// {
// 	this->numerator *= rhs.numerator;
// 	this->denominator *= rhs.denominator;
// 	return *this;
// }

// Rational &Rational::operator/=(const Rational &rhs)
// {
// 	*this *= rhs.inverse();
// 	return *this;
// }

// Rational &Rational::operator++()
// {
// 	*this += (long)1;
// 	return *this;
// }

// Rational Rational::operator++(int)
// {
// 	Rational tmp(*this);
// 	operator++();
// 	return tmp;
// }

// Rational &Rational::operator--()
// {
// 	*this -= (long)1;
// 	return *this;
// }

// Rational Rational::operator--(int)
// {
// 	Rational tmp(*this);
// 	operator--();
// 	return tmp;
// }

// Rational &Rational::operator=(const Rational &other)
// {
// 	this->numerator = other.numerator;
// 	this->denominator = other.denominator;
// 	return *this;
// }

// bool Rational::operator==(const Rational &rhs) const
// {
// 	/*
// 	*	a/b == p/q
// 	*	a == (pb)/q
// 	*	aq == pb
// 	*/
// 	return (this->numerator * rhs.denominator == rhs.numerator * this->denominator);
// }

// bool Rational::operator!=(const Rational &rhs) const
// {
// 	return !(*this == rhs);
// }

// bool Rational::operator<(const Rational &rhs) const
// {
// 	return (this->numerator * rhs.denominator < rhs.numerator * this->denominator);
// }

// bool Rational::operator<=(const Rational &rhs) const
// {
// 	return (*this < rhs || *this == rhs);
// }

// bool Rational::operator>(const Rational &rhs) const
// {
// 	return (this->numerator * rhs.denominator > rhs.numerator * this->denominator);
// }

// bool Rational::operator>=(const Rational &rhs) const
// {
// 	return (*this > rhs || *this == rhs);
// }

// std::ostream &operator<<(std::ostream &os, const Rational &rational)
// {
// 	return (os << rational.numerator << "/" << rational.denominator);
// }