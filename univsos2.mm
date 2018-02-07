$define usegp false


sos2:=proc(p,x,id::integer := 2,iter::boolean := false)
  local S,s,c,SEVEN,SODD,q,n,m,t,e,r,k,ok,l,a,p_can,p_cnj,s1,s2,u,v,i,j,sqs,cfs,sos,rfloat,gp,gproots;


  # Factor out the repeated roots, separating squared part s     
  # Also get rid of the coefficient so the remaining q is monic  
  # If the leading coefficient is negative, the polynomial can't 
  # be positive semidefinite, so return immediately.           

  S := sqrfree(p);
  c := lcoeff(p);
  if c < 0 then lprint(p): error "There is no decomposition into sum of squares for this polynomial"; fi;

  SEVEN:=map(_e->if type(_e[2],even) then _e[1]^(_e[2]/2) fi, S[2]):
  SEVEN:=[op(SEVEN),op(map(_e->if type(_e[2],odd) then _e[1]^((_e[2]-1)/2) fi, S[2]))]:
  SEVEN:=remove(member, SEVEN, [1]);
  SODD:=map(_e->if type(_e[2],odd) then _e[1] fi, S[2]):

	s:=mul(se, se in SEVEN):
	q:=S[1]*mul(so, so in SODD): 

  # Let n = 2 m be the degree; fail if this is odd (can't be pos def) 
  # If it's a constant (i.e. the polynomial is a constant multiple of 
  # a perfect square) then return almost immediately.                 
  n := degree(q,x);
  m := floor(n/2);
  if (2 * m <> n) then lprint(p): error "There is no decomposition into sum of squares for this polynomial";  fi;
  if (n = 0) then lprint(q, " * (", s, ")^2"); fi;

  # if id = 2 let t = 1 + x^2 + ... + x^2m else if id = 1 then let t = 1 + x^1 + x^2 + ... + x^2m-1
  # let r = q - e * t be a safe perturbation 
  t := q:
  if id = 2 then t:= sum(x^(2*i),i=0..m) else if id = 1 then t:= sum(x^j,j=0..n) fi:fi:

  e := min(1,c):

	while q - e*t <> 0 and nops(realroot(q-e*t)) > 0 do e:=e/2: od;
  e := e / 2;
  r := q - e * t;
  # Choose rounding k of roots accurate enough to make the rest work */
  k := 0; ok := false;
  while not ok do 
    k := k+1;
    l := lcoeff(r,x):
    gproots := usegp; gp := usegp;
    if gp then s1, s2 := gpsquares(r,x,k,iter): 
    else 
      a := polroots(r,x,gproots,iter);
      p_can := mul(x - a[2*i-1], i = 1..degree(r)/2);
      p_cnj := mul(x - a[2*i], i = 1..degree(r)/2);
      s1 := convert(evalc(Re((p_can + p_cnj) / 2)),rational,k);
      s2 := convert(evalc(Re((p_can - p_cnj) / (2 * I))),rational,k);
    fi:

    #lprint(k); lprint(s1); lprint(s2);

    # a := polroots(r,x,gp);
    # p_can := mul(x - a[2*i-1], i = 1..degree(r)/2);
    # p_cnj := mul(x - a[2*i], i = 1..degree(r)/2);
    # s1, s2 := myround (p_can, p_cnj, x, k);
    # if itv then
    #  s1 := myround(evalc(Re((p_can + p_cnj) / 2)),x,k);
    #  s2 := myround(evalc(Re((p_can - p_cnj) / (2 * I))),x,k);
    #else
    #  s1 := convert(evalc(Re((p_can + p_cnj) / 2)),rational,k);
    #  s2 := convert(evalc(Re((p_can - p_cnj) / (2 * I))),rational,k);
    #fi:

    u := r - l * (s1^2 + s2^2);
    v := expand(e * t + u);
    ok := true;
    for i from 0 to m do
      ok := ok and coeff(v,x,2*i) >= abs(coeff(v,x,2*i+1))/4 + abs(coeff(v,x,2*i-1));
    od;
  od;
    
  # Accumulate the final list of squares and coefficients
  sqs := [s1,s2]; cfs := [l,l];
  for i from 0 to m do
    sqs := [op(sqs),x^i]: 
    cfs := [op(cfs),coeff(v,x,2*i) - (abs(coeff(v,x,2*i+1))/4 + abs(coeff(v,x,2*i-1)))]:
  od;
  for i from 0 to m-1 do
    sqs := [op(sqs),x^i  * (x + sign(coeff(v,x,2*i+1)) / 2)]: 
    cfs := [op(cfs),abs(coeff(v,x,2*i+1))]:
  od;

 # Now put back in the factor from the initial decomposition */

#  sqs := map(_pol -> s * _pol, sqs):
#  cfs := c * cfs:
  sos := [];
  for i from 1 to 2*m+3 do
    sos := [op(sos),cfs[i],s*sqs[i]]:
  od;
  return sos:

end;

 # Sanity check */
 #
 # if (sum(i=1,2*m+3,cfs[i]*sqs[i]^2) - p != 0,print("Failure");return);
 # for (i = 1,2*m+2,print(cfs[i] " * (" sqs[i] ")^2 +"));
 # print(cfs[2*m+3] " * (" sqs[2*m+3] ")^2")

 # mf = "sosgp.mm";
 # write1(mf,"sosgp := [");
 # for (i = 1,2*m+2,write1(mf,cfs[i] ", " sqs[i] ", "));
 # write1(mf,cfs[2*m+3] ", " sqs[2*m+3]);
 # write(mf,"];");


UnivariateSumOfSquaresDecItv2:=proc(f, a, b)
  local psatz, bitsos, n, cf, q, sosq, clist, soslist, rlist, tlist, nc, l, sosf1, sosf2, sosdecomp, ti, tcmp,sos;
  psatz := false;
  n := degree(f);
  if n = 0 and f<0 then error "There is no decomposition into sum of squares for this polynomial"; fi;
  if b < a then error cat("The interval [", convert(a, string), ", ", convert(b, string), "] is not valid")  fi;
  q := add(coeff(f,x,i)*(1+y^2)^(n-i)*(a+b*y^2)^i, i=0..n);
  ti := time[real](): 
  sosq := sos2(q,y,2);
  tcmp := time[real]() - ti:
  printf("%fms\n",1000*tcmp);
  if psatz = true then
  sos := HornerToList(sosq);

  clist := [seq(1/(b-a)^n*c[1], c in sos)];
  soslist := [seq(c[2], c in sos)];

  rlist := [seq(  add(coeff(si,y,2*i)*y^i,  i=0..(ceil(degree(si/2)))), si in soslist)];
  tlist := [seq(  add(coeff(si,y,2*i+1)*y^i,i=0..(ceil(degree(si/2)))), si in soslist)];

  nc := floor(n/2);
  l := nops(clist);
  sosf1 := [seq(add(coeff(r,y,j)*(x - a)^j*(b-x)^(nc - j), j=0..degree(r)), r in rlist)];
  if n mod 2 = 0 then sosf2 := [seq(add(coeff(t,y,j)*(x - a)^j*(b-x)^(nc - 1 - j), j=0..degree(t)), t in tlist)] else sosf2 := [seq(add(coeff(t,y,j)*(x - a)^j*(b-x)^(nc - j), j=0..degree(t)), t in tlist)]  fi;

  #if n mod 2 = 0 then sosdecomp := add(clist[i] * sosf1[i]^2,i=1..l) + (x-a)*(b-x)*add(clist[i] * sosf2[i]^2,i=1..l) else sosdecomp := (b-x)*add(clist[i] * sosf1[i]^2,i=1..l) + (x-a)*add(clist[i] * sosf2[i]^2,i=1..l) fi;

  #bitsos := BitSizePolSeq(sosf1,x) + BitSizePolSeq(sosf2,x) + 2 * BitSizeSeq(clist);
  # lprint("Size of the SOS certificate ", bitsos);

  #expand(f - sosdecomp);
  return clist,  sosf1, sosf2: fi;
  return q,sosq;
end;

gpsquares:=proc(r,x,k,iter)
  local fd,ok,prec,cmd;
  fd := fopen("in.gp",WRITE,TEXT); writeline(fd,"r =", convert(r,string)); writeline(fd,"x =", convert(x,string));  writeline(fd,"k =", convert(k,string)); fclose(fd);
  ok := true; 
  if iter then
  prec := 8000000 ;
  while ok do
    system("rm -f out.mm"):
    cmd := sprintf("gp -q -s %d gpsquares.gp",prec);
    system(cmd): 
    try read "out.mm":
    catch : prec := prec*2: #lprint(sprintf("trying with stack precision: %d", prec));
    finally ok:=false:
    end try:
  od:
  else
    system("rm -f out.mm"):
    system("gp -q gpsquares.gp"): 
    read "out.mm":
  fi:
  return s1gp, s2gp:
  #return 2^(-k)*add(round~([coeffs(2^k*f,x,t)]) *~ [t]):
end;

polroots := proc(r,x,gproots)
    local fd, a, rfloat;
    #rfloat := convert(r,float):
    rfloat := r;
    if gproots then 
      fd := fopen("in.gp",WRITE,TEXT); writeline(fd,"r =", convert(rfloat,string)); fclose(fd);
      system("rm -f out.mm"):
      system("gp -q  mypolroots.gp"): 
      system("sed -i 's/0\\.E/0\\.0E/g' out.mm"): system("sed -i 's/ E/E/g' out.mm"):
      read "out.mm":
      #fd := fopen("out.gp",READ,TEXT); a:= readdata(fd,float); fclose(fd); 
      return agp:
    else
     a := [fsolve([r=0],x,complex,fulldigits)]: 
     return map(sol-> rhs(sol[1]),a):
    fi:
end;

SOSCHECK2:=proc(f, sos)
  local s,i,res;
  s := 0;
  for i from 1 to nops(sos)/2 do s := s + sos[2*i-1]*sos[2*i]^2 od:
  res := expand(f-s);
  if res = 0 then
  return res;
  else 
    lprint(f); lprint(sos);
    error "Invalid sum of squares decomposition";
fi;
end;

soscheck2 := proc(f,sos)
  return SOSCHECK2(f,sos);
end;
