#ifndef REDUCED_RATIONAL_HPP
#define REDUCED_RATIONAL_HPP

#include "rational.hpp"

class ReducedRational : public Rational {
private:
	void reduce();

public:
	ReducedRational();
	ReducedRational(const long & n);
	ReducedRational(const long & n, const long & d);
	ReducedRational(const char* str);
	ReducedRational(const std::string & str);
	ReducedRational(const Rational & other);
	ReducedRational(const ReducedRational & other);
	~ReducedRational();

	bool isReduced() const;

};

#endif