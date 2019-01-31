#ifndef RATIONAL_HPP
#define RATIONAL_HPP

#include <iostream>
#include <regex>

class ReducedRational;

class Rational
{
	friend class ReducedRational;

  private:
	long gcd() const;

  public:
	long numerator, denominator;

	Rational();
	Rational(const long &n, const long &d);
	Rational(const double &d);
	Rational(const char *str);
	Rational(const std::string &str);
	Rational(const Rational &other);
	Rational(const ReducedRational &other);
	virtual ~Rational();

	double value() const;
	Rational inverse() const;

	Rational reduce() const;
	bool isReduced() const;

	/*** Operators ***/
	Rational &operator+=(const Rational &rhs);
	Rational &operator-=(const Rational &rhs);
	Rational &operator*=(const Rational &rhs);
	Rational &operator/=(const Rational &rhs);
	Rational &operator++();
	Rational operator++(int);
	Rational &operator--();
	Rational operator--(int);

	Rational &operator=(const Rational &other);

	bool operator==(const Rational &rhs) const;
	bool operator!=(const Rational &rhs) const;
	bool operator<(const Rational &rhs) const;
	bool operator<=(const Rational &rhs) const;
	bool operator>(const Rational &rhs) const;
	bool operator>=(const Rational &rhs) const;

	friend std::ostream &operator<<(std::ostream &os, const Rational &fraction);
	/***/
};

static const std::regex type_1 = std::regex("-?[0-9]+(.[0-9]+)?"); // 0.5
static const std::regex type_2 = std::regex("-?[0-9]+/-?[0-9]+"); // 1/2

inline Rational operator+(const Rational &lhs, const Rational &rhs)
{
	return Rational(lhs) += rhs;
}

inline Rational operator-(const Rational &lhs, const Rational &rhs)
{
	return Rational(lhs) -= rhs;
}

inline Rational operator*(const Rational &lhs, const Rational &rhs)
{
	return Rational(lhs) *= rhs;
}

inline Rational operator/(const Rational &lhs, const Rational &rhs)
{
	return Rational(lhs) /= rhs;
}

inline Rational operator%(const Rational &lhs, const Rational &rhs)
{
	if (rhs == lhs || rhs + rhs == lhs || rhs - rhs == lhs)
		return Rational();

	Rational t(rhs);
	if (rhs < lhs)
	{
		while (t + rhs < lhs)
		{
			t += rhs;
		}
	}
	else
	{
		while (t > lhs)
		{
			t -= rhs;
		}
	}

	return Rational(lhs - t);
}

#endif