with(LinearAlgebra): read "univsos1.mm": read "univsos2.mm": read "benchsunivsos.mm": read "benchsollya.mm": read "univsos3.mm":
# read "univsos3.mm": read "vqeisolate6.mm": read "vqenewton.mm":
# Benchmarks from the paper https://hal.archives-ouvertes.fr/ensl-00445343v2/document (pages 23-24 section 5.2.5)
# univsos1
BenchSOSitv(f1,g1,a1,b1);
BenchSOSitv(f3,g3,a3,b3);
BenchSOSitv(f4,g4,a4,b4);
BenchSOSitv(f5,g5,a5,b5);
BenchSOSitv(f6,g6,a6,b6);
BenchSOSitv(f7,g7,a7,b7);
BenchSOSitv(f8,g8,a8,b8);
BenchSOSitv(f9,g9,a9,b9);
BenchSOSitv(f10,g10,a10,b10);
# univsos2
BenchSOSitv2(f1,g1,a1,b1):
BenchSOSitv2(f3,g3,a3,b3):
BenchSOSitv2(f4,g4,a4,b4):
BenchSOSitv2(f5,g5,a5,b5):
BenchSOSitv2(f6,g6,a6,b6):
BenchSOSitv2(f7,g7,a7,b7):
BenchSOSitv2(f8,g8,a8,b8):
BenchSOSitv2(f9,g9,a9,b9):
BenchSOSitv2(f10,g10,a10,b10):
# univsos3
BenchSOSitv3(f1,g1,a1,b1,65,40,200,30,30);
BenchSOSitv3(f4,g4,a4,b4,120,30,200,40,40);
BenchSOSitv3(f5,g5,a5,b5,240,100,2000,100,100);
BenchSOSitv3(f6,g6,a6,b6,100,30,200,30,30);
BenchSOSitv3(f7,g7,a7,b7,150,100,300,30,30);
BenchSOSitv3(f8,g8,a8,b8,80,40,200,30,30);
BenchSOSitv3(f9,g9,a9,b9,80,50,200,30,30);
BenchSOSitv3(f10,g10,a10,b10,100,40,300,30,30);

# Benchmarks for nonnegative power sums of increasing degrees 1 + X + X^2 + ... + X^n
# univsos1
BenchSOSsum();
# univsos2
BenchSOSsum2(2);
# univsos3
BenchSOSsum3(2);

# Benchmarks for modified Wilkinson polynomials of increasing degrees 1 + (X-1)^2...(X-n)^2
# univsos1
BenchWilkinson();
# univsos2
BenchWilkinson2(2);
# univsos3
BenchWilkinson3(2);

# Benchmarks for modified Mignotte polynomials of increasing degrees X^n + 2 (101 X - 1)^2
# univsos1
BenchMignotte();
# univsos2
BenchMignotte2(2);

# Benchmarks for modified Mignotte polynomials of increasing degrees X^n + 2 (101 X - 1)^(n-2)
# univsos1
BenchMignotteN();
# univsos2
BenchMignottedN2(2);

# Benchmarks for modified Mignotte polynomials of increasing degrees (X^n + 2 (101 X - 1)^2) (X^n + 2*((101 +1/101)X - 1)^2)
# univsos1
BenchMignotteProd();
# univsos2
BenchMignottedProd2(2);
