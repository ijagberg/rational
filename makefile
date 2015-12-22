all:

test: test.o rational.o reduced_rational.o ; g++ -std=c++11 test.o rational.o reduced_rational.o -o test

approx: approx.o rational.o ; g++ -std=c++11 approx.o rational.o -o approx

modulo: modulo.o rational.o ; g++ -std=c++11 modulo.o rational.o -o modulo

test.o: test.cpp ; g++ -std=c++11 -c test.cpp

approx.o: example/approx.cpp ; g++ -std=c++11 -c example/approx.cpp

modulo.o: example/modulo.cpp ; g++ -std=c++11 -c example/modulo.cpp

rational.o: rational.cpp ; g++ -std=c++11 -c rational.cpp

reduced_rational.o: reduced_rational.cpp ; g++ -std=c++11 -c reduced_rational.cpp

remake: ; rm *.o; make

clean: ; rm *.o
