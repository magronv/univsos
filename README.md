# univsos
Sums of squares decomposition of univariate nonnegative polynomials

## Description
`univsos` is a Maple library for computation of sums of squares (SOS) decompositions of univariate nonnegative polynomials with rational coefficients. The library includes two distinct algorithms: 

- `univsos1`, which relies on root isolation, quadratic under approximations of positive polynomials and square-free decomposition.
- `univsos2`, which relies on root isolation of perturbed positive  polynomials and square-free decomposition.

## Installation instructions
### Prerequisites
`univsos` has been tested with `Maple2016` and requires: 
- the external `PARI/GP` software available at the address http://pari.math.u-bordeaux.fr/download.html


### Download
`univsos` is maintained as a GitHub repository at the address https://github.com/magronv/univsos.git

It can be obtained with the command:

$ git clone https://github.com/magronv/univsos.git

### Execution and Benchmarks
From the univsos/ directory, launch Maple and execute the following command:

`with(LinearAlgebra): read "univsos1.mm": read "univsos2.mm": read "benchsunivsos.mm": read "benchsollya.mm":`

Let us condier the polynomial f := 1 + X + X^2 + X^3 + X^4. 
To compute a sums of squares decomposition of f, you can:


1) rely on univsos1

`f := 1 + X + X^2 + X^3 + X^4: sos:=sos1(f,X);`

                       sos := [[1, [1, -X, 0]], [X + 1, [0, 0, 0]], [0, [1, X - 1/2, 3/4]]]

The output is a list [(p1, (a1, b1, c1)),..., (pr, (ar, br, cr))], where each pi is a rational polynomial, ai*bi^2 + ci is a rational polynomial of degree at most 2, and such that f admits the Horner-like decomposition:

`f  = p1^2* [ p2^2* [ ... [pr^2 + ar * br^2 + cr]] + a2*b2^2 + c2] + a1*b1^2 + c1`

You can verify afterwards that this yields a valid nonnegativty certificate of f with the following command:

`expand(f - foldr((_e, a) -> _e[1]^2 * a + _e[2][1]*_e[2][2]^2 + _e[2][3], 1, op(sos)));`


2) rely on univsos2

`f := 1 + X + X^2 + X^3 + X^4: sos := sos2(f,X);`

                  2                      23 X   11  377      55             2                                               
    sos := [7/8, X  + 9/16 X - 3/4, 7/8, ---- + --, ----, 1, ---, X, 7/64, X , 9/1024, X + 1/2, 1/64, X (X + 1/2)]
  
                                          16    16  4096     256
                                         
                                         

The output is a list [c1,p1,...,cr,pr], where each ci is a rational number and each pi is a rational polynomial such that f admits the following weigthed SOS decomposition:

`f  = c1*p1^2 + ... + cr*pr^2`

You can verify afterwards that this yields a valid nonnegativty certificate of f with the following command:

`s := 0: for i from 1 to nops(sos)/2 do s := s + sos[2*i-1]*sos[2*i]^2 od: expand (f -s);`

### Benchmarks from the paper https://hal.archives-ouvertes.fr/ensl-00445343v2/document (pages 23-24 section 5.2.5)
### univsos1

`BenchSOSitv(f1,g1,a1,b1);`

`BenchSOSitv(f3,g3,a3,b3);`

`BenchSOSitv(f4,g4,a4,b4);`

`BenchSOSitv(f5,g5,a5,b5);`

`BenchSOSitv(f6,g6,a6,b6);` #(will most probably run for ever)

`BenchSOSitv(f7,g7,a7,b7);`

`BenchSOSitv(f8,g8,a8,b8);`

`BenchSOSitv(f9,g9,a9,b9);`

`BenchSOSitv(f10,g10,a10,b10);`

### univsos2

`BenchSOSitv2(f1,g1,a1,b1):`

`BenchSOSitv2(f3,g3,a3,b3):`

`BenchSOSitv2(f4,g4,a4,b4):`

`BenchSOSitv2(f5,g5,a5,b5):`

`BenchSOSitv2(f6,g6,a6,b6):`

`BenchSOSitv2(f7,g7,a7,b7):`

`BenchSOSitv2(f8,g8,a8,b8):`

`BenchSOSitv2(f9,g9,a9,b9):`

`BenchSOSitv2(f10,g10,a10,b10):`

### Benchmarks for nonnegative power sums of increasing degrees 1 + X + X^2 + ... + X^n
### univsos1

`BenchSOSsum();`

### univsos2

`BenchSOSsum2(2);`

### Benchmarks for modified Wilkinson polynomials of increasing degrees 1 + (X-1)^2...(X-n)^2
### univsos1

`BenchWilkinson();`

### univsos2

`BenchWilkinson2(2);`

### Benchmarks for modified Mignotte polynomials of increasing degrees X^n + 2 (101 X - 1)^2
### univsos1

`BenchMignotte();`

### univsos2

`BenchMignotte2(2);`

### Benchmarks for modified Mignotte polynomials of increasing degrees X^n + 2 (101 X - 1)^(n-2)
### univsos1

`BenchMignotteN();`

### univsos2
`BenchMignottedN2(2);`

### Benchmarks for modified Mignotte polynomials of increasing degrees (X^n + 2 (101 X - 1)^2) (X^n + 2*((101 +1/101)X - 1)^2)
### univsos1

`BenchMignotteProd();`

### univsos2

`BenchMignottedProd2(2);`
