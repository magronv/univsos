BitSizeSos := proc (sos,X)
   return add(BitSizePol(p[1], X) + BitSizePolQuadr(p[2], X), p in sos);
end;

BitSizePolQuadr := proc(q,X)
  return BitRat(q[1]) + BitSizePol(q[2], X) + BitRat(q[3]);
end;

BitSizePolSeq3 := proc(listpol,X)
  return add(BitSizePol(p[1], X) + BitSizePolSeq(p[2], X), p in listpol);
end;

BitSizePolSeq := proc(listpol,X)
  return add(BitSizePol(p, X), p in listpol);
end;

BitSizePol:=proc(p, X)
  local res;
  res := [coeffs(expand(p),X)];
  return BitSizeSeq(res);
end;

BitSizeSeq:=proc(l)
  return add(BitRat(c), c in l);
end;

BitRat := proc(r)
  local n, d, res, rs;
  if type(r,rational) then rs :=r : else rs:=r^2: fi:
  if rs = 0 then return 1; fi;
  (n, d) := (abs(numer(rs)), abs(denom(rs)));
  if d = 1 then res :=  ilog2(n) + 1 else res := ilog2(n) + ilog2(d) + 2 fi;
  return res;
end;

BenchSOSitv:=proc(p1,p2,a,b)
  local q1,sosq1,q2,sosq2,bits,tverif,bitsq;
  lprint ("Time for Computation of SOS certificates:");
  q1,sosq1 := UnivariateSumOfSquaresDecItv(p1,a,b):
  q2,sosq2 := UnivariateSumOfSquaresDecItv(p2,a,b):

  lprint ("Bitsize of polynomials:");
  bitsq := BitSizePol(q1,y) +  BitSizePol(q2,y):
  printf("%d bits\n",bitsq);

  lprint ("Bitsize of SOS certificates:");
  bits := BitSizeSos(sosq1,y) +  BitSizeSos(sosq2,y):
  printf("%d bits\n",bits);

  lprint ("Time for Verification of SOS certificates:");
  tverif := TimeVerif(q1,sosq1,3) + TimeVerif(q2,sosq2,3):
  printf("%1.3ems\n",1000*tverif);
  return 0:
end;

BenchSOSitv2:=proc(p1,p2,a,b)
  local q1,sosq1,q2,sosq2,bits,tverif,bitsq;
  lprint ("Time for Computation of SOS certificates:");
  q1,sosq1 := UnivariateSumOfSquaresDecItv2(p1,a,b);
  q2,sosq2 := UnivariateSumOfSquaresDecItv2(p2,a,b);

  lprint ("Bitsize of polynomials:");
  bitsq := BitSizePol(q1,y) +  BitSizePol(q2,y):
  printf("%d bits\n",bitsq);

  lprint ("Bitsize of SOS certificates:");
  bits := BitSizePolSeq(sosq1,y) +  BitSizePolSeq(sosq2,y):
  printf("%d bits\n",bits);

  lprint ("Time for Verification of SOS certificates:");
  tverif := TimeVerif2(q1,sosq1,3) + TimeVerif2(q2,sosq2,3):
  printf("%1.3ems\n",1000*tverif);
  return 0:
end;

BenchSOSitv3:=proc(p1,p2,a,b,prec::integer:=10,precSVD::integer:=10, precSDP::integer := 200, epsStar::integer := 3, epsDash::integer:=3)
  local sosg1,sosg2, sosl1, sosl2, bits,tverif,bitsp, ti, tf;
  ti := time[real]():
  lprint ("Time for Computation of SOS certificates:");
#  q1,sosq1 := UnivariateSumOfSquaresDecItv3(p1,a,b,k);
#  q2,sosq2 := UnivariateSumOfSquaresDecItv3(p2,a,b,k);

  sosg1,sosl1 := sositv3(p1,x,a,b,prec,precSVD,precSDP,epsStar,epsDash);
  sosg2,sosl2 := sositv3(p2,x,a,b,prec,precSVD,precSDP,epsStar,epsDash);
  tf := time[real]()-ti; 

  lprint ("Bitsize of polynomials:");
  bitsp := BitSizePol(p1,x) +  BitSizePol(p2,x):
  printf("%d bits\n",bitsp);

  lprint ("Bitsize of SOS certificates:");
  bits := BitSizePolSeq(sosg1,x) +  BitSizePolSeq(sosg2,x) + BitSizePolSeq(sosl1,x) +  BitSizePolSeq(sosl2,x):

  printf("%d bits\n",bits);

  printf("time= %esecs\n",tf);

  lprint ("Time for Verification of SOS certificates:");
  tverif := TimeVerif3(p1,a,b,sosg1,sosl1,3) + TimeVerif3(p2,a,b,sosg2,sosl2,3):
  printf("%1.3ems\n",1000*tverif);
  return 0:
end;

BenchSOS:=proc(p,x)
  local ti,tf,sos,bitp,bits,tverif;

  printf("Degree of polynomial = %d\n",degree(p));
  bitp := BitSizePol(p,x):
  printf("  Bitsize of polynomial = %d bits\n",bitp);

  ti := time[real]():
  sos := SOSDecomp(p,x): #lprint(sos);
  tf := time[real]():
  printf("  Time for Computation of SOS certificate = %e ms\n",1000*(tf - ti));

  bits := BitSizeSos(sos,x):
  printf("  Bitsize of SOS certificate = %d bits\n",bits);

  tverif := TimeVerif(p,sos,3):
  printf("  Time for Verification of SOS certificate = %1.3e ms\n",1000*tverif);
end;

BenchSOS2:=proc(p,x,id,iter::boolean:=false)
  local ti,tf,sos,bitp,bits,tverif;

  printf("Degree of polynomial = %d\n",degree(p));
  bitp := BitSizePol(p,x):
  printf("  Bitsize of polynomial = %d bits\n",bitp);

  ti := time[real]():
  sos := sos2(p,x,id,iter):
  tf := time[real]():
  printf("  Time for Computation of SOS certificate = %e ms\n",1000*(tf - ti));

  bits := BitSizePolSeq(sos,x):
  printf("  Bitsize of SOS certificate = %d bits\n",bits);

  tverif := TimeVerif2(p,sos,3):
  printf("  Time for Verification of SOS certificate = %1.3e ms\n",1000*tverif);
end;

BenchSOS3:=proc(p,x,id)
  local ti,tf,sos,bitp,bits,tverif;

  printf("Degree of polynomial = %d\n",degree(p));
  bitp := BitSizePol(p,x):
  printf("  Bitsize of polynomial = %d bits\n",bitp);

  ti := time[real]():
  sos := sos3(p,x,id):
  #lprint(sos);
  tf := time[real]():
  printf("  Time for Computation of SOS certificate = %e ms\n",1000*(tf - ti));

  bits := BitSizePolSeq(sos,x):
  printf("  Bitsize of SOS certificate = %d bits\n",bits);

  tverif := TimeVerif2(p,sos,2):
  printf("  Time for Verification of SOS certificate = %1.3e ms\n",1000*tverif);
end;


BenchSOSsum:=proc()
 local deg,s;
# s := [10,20,40,60,80,100,200,300,400,500,1000]:
  s := [1000]:
 for deg in s do BenchSOS(add(x^j,j=0..deg),x) od:
end;

BenchSOSsum2:=proc(id)
 local deg,s;
 s := [10,20,40,60,80,100,200]:
 for deg in s do BenchSOS2(add(x^j,j=0..deg),x,id,true) od:
# s := [300]: # > 1h
# for deg in s do BenchSOS2(add(x^j,j=0..deg),x,id,true) od:
end;

BenchSOSsum3:=proc(id)
 local deg,s;
#  s := [2];
#  s := [40,60,80,100,200,500,1000]:
 s := [10,100,1000,10000]:
 for deg in s do BenchSOS3(add(x^j,j=0..deg),x,id) od:
end;

BenchWilkinson:=proc()
 local deg,s;
 s := [10,20,40,60,80,100,200,300,400,500]:
 for deg in s do BenchSOS(1 + mul((x-j)^2,j=1..deg/2),x) od:
end;

BenchWilkinson2:=proc(id)
 local deg,s;
 s := [10,20,40,60,80,100]:
 for deg in s do BenchSOS2(1 + mul((x-j)^2,j=1..deg/2),x,id,true) od:
# s := [60,80,100,200,300]: # > 1h
# for deg in s do BenchSOS2(1 + mul((x-j)^2,j=1..deg/2),x,id,true) od:
end;

BenchWilkinson3:=proc(id)
 local deg,s;
 s := [10,20,40]:
 for deg in s do BenchSOS3(1 + mul((x-j)^2,j=1..deg/2),x,id,true) od:
# s := [60,80,100,200,300]: # > 1h
# for deg in s do BenchSOS2(1 + mul((x-j)^2,j=1..deg/2),x,id,true) od:
end;

BenchMignotte:=proc()
 local deg,s;
 s := [10,100,1000,10000]:
 for deg in s do BenchSOS(x^deg + 2 * (101*x - 1)^(2),x) od:
end;

BenchMignotte2:=proc(id)
 local deg,s;
 s := [10]:
 for deg in s do BenchSOS2(x^deg + 2 * (101*x - 1)^(2),x,id,true) od:
# s := [100]: # > 1h
# for deg in s do BenchSOS2(x^deg + 2 * (101*x - 1)^(2),x,id,true) od:
end;

BenchMignotte3:=proc(id)
 local deg,s;
 s := [10,20,30]:
 for deg in s do BenchSOS3(x^deg + 2 * (101*x - 1)^(2),x,id,true) od:
end;

BenchMignotteN:=proc()
 local deg,s;
 s := [10,20,40,60,100,200]:
 for deg in s do BenchSOS(x^deg + 2 * (101*x - 1)^(deg - 2),x) od:
end;

BenchMignotteN2:=proc(id)
 local deg,s;
 s := [10,20]:
 for deg in s do BenchSOS2(x^deg + 2 * (101*x - 1)^(deg - 2),x,id,true) od:
# s := [40]: # > 1h
# for deg in s do BenchSOS2(x^deg + 2 * (101*x - 1)^(deg - 2),x,id,true) od:
end;

BenchMignotteProd:=proc()
 local deg,s;
 s := [10,20,40,60,100,200]:
 for deg in s do BenchSOS((x^(deg/2) + 2 * ((101+1/101)*x - 1)^(2)) * (x^(deg/2) + 2 * (101*x - 1)^(2)) ,x) od:
end;

BenchMignotteProd2:=proc(id)
 local deg,s;
 s := [10]: # > 1h
 for deg in s do BenchSOS2((x^(deg/2) + 2 * ((101+1/101)*x - 1)^(2)) * (x^(deg/2) + 2 * (101*x - 1)^(2)) ,x,id,true) od:
end;


TimeVerif:=proc(f,sos,n)
  local t:
  t:=time(SOSCHECKn(f,sos,n)):
  evalf(t/10^n);
end;

SOSCHECKn:=proc(f,sos,n)
local i;
 for i from 1 to 10^n do SOSCHECK(f,sos) od:
end;

SOSCHECK:=proc(f, sos)
local res;
res := expand(f - foldr((_e, a) -> _e[1]^2 * a + _e[2][1]*_e[2][2]^2 + _e[2][3], 1, op(sos)));
if res = 0 then
return res;
else 
    lprint(f); lprint(sos);
    error "Invalid sum of squares decomposition";
fi;
end;

TimeVerif2:=proc(f,sos,n)
  local t:
  t:=time(SOSCHECKn2(f,sos,n)):
  evalf(t/10^n);
end;

SOSCHECKn2:=proc(f,sos,n)
  local i;
  for i from 1 to 10^n do SOSCHECK2(f,sos) od:
end;

SOSCHECK2:=proc(f, sos)
  local s,i,res;
  s := 0;
  for i from 1 to nops(sos)/2 do if sos[2*i-1] < 0 then lprint(sos[2*i-1]); error "Invalid sum of squares decomposition"; else s := s + sos[2*i-1]*sos[2*i]^2 fi: od:
  res := expand(f-s);
  if res = 0 then
  return res;
  else 
    lprint(f); lprint(sos);
    error "Invalid sum of squares decomposition";
fi;
end;

TimeVerif3:=proc(f,a,b,sosg,sosl,n)
  local t:
  t:=time(SOSCHECKn3(f,a,b,sosg,sosl,n)):
  evalf(t/10^n);
end;

SOSCHECKn3:=proc(f,a,b,sosg,sosl,n)
  local i;
  for i from 1 to 10^n do SOSCHECKitv3(f,a,b,sosg,sosl) od:
end;

SOSCHECKitv3:=proc(f, a, b, sos, sos2)
  local s,i;
  s := 0;
  for i from 1 to nops(sos)/2 do if sos[2*i-1] < 0 then lprint(evalf(sos[2*i-1])); error "Negative numbers => Invalid sum of squares decomposition": else  s := s + sos[2*i-1]*sos[2*i]^2 fi: od:
  for i from 1 to nops(sos2)/2 do if sos2[2*i-1] < 0 then lprint(evalf(sos[2*i-1])); error "Negative numbers => Invalid sum of squares decomposition": else s := s + (b-x)*(x-a)*sos2[2*i-1]*sos2[2*i]^2 fi: od:
    if not expand(f - s) = 0 then lprint(evalf(expand(f - s))); error "Invalid sum of squares decomposition"; else return 0: fi:
end;

confrac2rat := proc (l) 
  foldr((_a,_b) -> _a + 1/_b, infinity, op(l)); 
end;

kernelopts(printbytes=false):
#deg := 40;
# p := add(x^(2*i+1)*Generate(rational(denominator=100,character=open..closed)),i=0..(deg/2-1)) + add(x^(2*j),j=0..deg/2);
# q := p^4 + 1:SOSCHECK2(q,sos3(q,x,2));
