UnivariateSumOfSquaresDecItv:=proc(f, a, b)
  local bitsos, n, cf, q, sosq, clist, soslist, rlist, tlist, nc, l, sosf1, sosf2, sosdecomp;
  n := degree(f);
  if n = 0 and f<0 then error "There is no decomposition into sum of squares for this polynomial"; fi;
  if b < a then error cat("The interval [", convert(a, string), ", ", convert(b, string), "] is not valid")  fi;
  q := add(coeff(f,x,i)*(1+y^2)^(n-i)*(a+b*y^2)^i, i=0..n);
  sosq := SOSDecomp(q,y);
  clist := [seq(1/(b-a)^n*mul(t, t in c[1]), c in sosq)];
  soslist := [seq(mul(t, t in c[2]), c in sosq)];

  rlist := [seq(  add(coeff(si,y,2*i)*y^i,  i=0..(ceil(degree(si/2)))), si in soslist)];
  tlist := [seq(  add(coeff(si,y,2*i+1)*y^i,i=0..(ceil(degree(si/2)))), si in soslist)];

  nc := floor(n/2);
  l := nops(clist);
  sosf1 := [seq(add(coeff(r,y,j)*(x - a)^j*(b-x)^(nc - j), j=0..degree(r)), r in rlist)];
  if n mod 2 = 0 then sosf2 := [seq(add(coeff(t,y,j)*(x - a)^j*(b-x)^(nc - 1 - j), j=0..degree(t)), t in tlist)] else sosf2 := [seq(add(coeff(t,y,j)*(x - a)^j*(b-x)^(nc - j), j=0..degree(t)), t in tlist)]  fi;

  if n mod 2 = 0 then sosdecomp := add(clist[i] * sosf1[i]^2,i=1..l) + (x-a)*(b-x)*add(clist[i] * sosf2[i]^2,i=1..l) else sosdecomp := (b-x)*add(clist[i] * sosf1[i]^2,i=1..l) + (x-a)*add(clist[i] * sosf2[i]^2,i=1..l) fi;

  #time(expand(f -( (b-x)*add(clist[i] * sosf1[i]^2,i=1..l) + (x-a)*add(clist[i] * sosf2[i]^2,i=1..l))));
  #bitsos := BitSizePolSeq(sosf1,x) + BitSizePolSeq(sosf2,x) + 2 * BitSizeSeq(clist);
  # lprint("Size of the SOS certificate ", bitsos);

  # expand(f - sosdecomp);
  #return clist,  sosf1, sosf2, sosdecomp;
end;


BitSizePolSeq := proc(listpol,X)
  return add(BitSizePol(p, X), p in listpol);
end;

BitSizePol:=proc(p, X)
  res := [coeffs(expand(p),X)];
  return BitSizeSeq(res);
end;

BitSizeSeq:=proc(l)
  return add(BitRat(c), c in l);
end;

BitRat := proc(r)
  local n, d;
  if r = 0 then return 1; fi;
  (n, d) := (abs(numer(r)), abs(denom(r)));
  if d = 1 then res :=  floor(ln(n)/ln(2)) + 1 else res := floor(ln(n)/ln(2)) + floor(ln(d)/ln(2)) + 2 fi;
  return res;
end;

f:=sum(x^i,i=0..4): sos:=SOSDecomp(f,x):

veriftimer := proc(f, sos)
  for i from 1 to 1000 
    do expand(f - foldr((_e, a) -> _e[1]^2 * a + _e[2], 1, op(f))) end do:
end;

expand(foldr((_e, a) -> _e[1]^2 * a + _e[2], 1, op(sos)));
