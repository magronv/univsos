sos3:=proc(p,x,prec::integer := 10)
  local S,s,c,SEVEN,SODD,q,n,m,t,e,r,ok,l,a,p_can,p_cnj,s1,s2,u,v,i,j,sqs,cfs,sos,rfloat,gp, eigs, eigs2, soslist,soslist2,sumsos,cnd,maxq, k, obj_plus_r0, id;

  # Factor out the repeated roots, separating squared part s     
  # Also get rid of the coefficient so the remaining q is monic  
  # If the leading coefficient is negative, the polynomial can't 
  # be positive semidefinite, so return immediately.           
  id := 2;
  S := sqrfree(p);
  c := lcoeff(p);
  if c < 0 then lprint(p): error "There is no decomposition into sum of squares for this polynomial"; fi;

  SEVEN:=map(_e->if type(_e[2],even) then _e[1]^(_e[2]/2) fi, S[2]):
  SEVEN:=[op(SEVEN),op(map(_e->if type(_e[2],odd) then _e[1]^((_e[2]-1)/2) fi, S[2]))]:
  SEVEN:=remove(member, SEVEN, [1]);
  SODD:=map(_e->if type(_e[2],odd) then _e[1] fi, S[2]):

	s:=mul(se, se in SEVEN):
	q:=S[1]*mul(so, so in SODD): 
  #maxq:=max (map(_c -> abs (_c),[coeffs(q)]));
  maxq := 1;
  q := 1/maxq*q;

  # Let n = 2 m be the degree; fail if this is odd (can't be pos def) 
  # If it's a constant (i.e. the polynomial is a constant multiple of 
  # a perfect square) then return almost immediately.                 
  n := degree(q,x);
  m := floor(n/2);
  if (2 * m <> n) then lprint(p): error "There is no decomposition into sum of squares for this polynomial";  fi;
  if (n = 0) then lprint(q, " * (", s, ")^2"); fi;

  # if id = 2 let t = 1 + x^2 + ... + x^2m else if id = 1 then let t = 1 + x^1 + x^2 + ... + x^2m-1
  # let r = q - e * t be a safe perturbation 
  t := q;
  if id = 2 then t:= sum(x^(2*i),i=0..m); else if id = 1 then t:= sum(x^j,j=0..n) fi;fi;
  e := min(1,c);

#	while degree(q - e*t,x) <= 0 or sturm(q-e*t,x,-infinity,infinity) > 0 do e:=e/2: od;
  while degree(q-e*t,x) <= 0 or q - e*t <> 0 and nops(realroot(q-e*t)) > 0 do e:=e/2: od;
  e := e / 2;
  r := q - e * t;
  # Choose rounding k of roots accurate enough to make the rest work */
  ok := false;
  k := prec;
  while not ok do 
    k := k+1;
    #lprint(r):
    (eigs,soslist,eigs2,soslist2,obj_plus_r0) := sossdp(r,x,k);
    sumsos := obj_plus_r0 + sum(eigs[j]*soslist[j]^2,j=1..nops(soslist));
    #lprint(sumsos):
    u := r - sumsos;
    v := expand(e * t + u + obj_plus_r0);
    #for i from 0 to n do lprint(coeff(v,x,i)); od;
    ok := true;
    for i from 0 to m do
      #printf("i = %d\n",i); lprint(coeff(v,x,2*i+1)):   
      cnd:= coeff(v,x,2*i) - (abs(coeff(v,x,2*i+1))/4 + abs(coeff(v,x,2*i-1)));
      if not (cnd>=0) then 
        printf("prec = %d\t idx = %d\t err = %8.3e\t",k,i,evalf(cnd)); lprint(cnd): 
 #lprint(evalf(coeff(v,x,2*i+1))):
        ok:= true:error("not enough precision");break:fi:
    od;
    #lprint("done");
  od;
    
  # Accumulate the final list of squares and coefficients
  #sqs := [1, op(soslist)]; cfs := [obj_plus_r0, op(eigs)]; #cfs := map (_e -> l*_e,eigs);
  sqs := [op(soslist)]; cfs := [op(eigs)];
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
  for i from 1 to nops(sqs) do
    sos := [op(sos),maxq*cfs[i],s*sqs[i]]:
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

UnivariateSumOfSquaresDecItv3:=proc(f, a, b, k::integer := 1)
  local psatz, bitsos, n, cf, q, sosq, clist, soslist, rlist, tlist, nc, l, sosf1, sosf2, sosdecomp, ti, tcmp,sos;
  psatz := false;
  n := degree(f);
  if n = 0 and f<0 then error "There is no decomposition into sum of squares for this polynomial"; fi;
  if b < a then error cat("The interval [", convert(a, string), ", ", convert(b, string), "] is not valid")  fi;
  q := add(coeff(f,x,i)*(1+y^2)^(n-i)*(a+b*y^2)^i, i=0..n);
  ti := time[real](): 
  sosq := sos3(q,y,2,k);
  tcmp := time[real]() - ti:
  printf("%fms\n",1000*tcmp);
  #lprint (tcmp);
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

sossdp := proc(r,x,precSVD::integer:=10,precSDP::integer:=200,epsStar::integer:=3,epsDash::integer:=3,a::rational := 0,b::rational := 1,itv::boolean := false)
    local fd, n, nsdp, nblock, nloc, i, j, Y, Y2,v, e, mons, rfloat, eigs, eivs,eigs2, eivs2,gmp,normeig,gpround, SVD, af, bf, lowerbnd ;
      #lprint(r);
      n := degree(r);
      nsdp := 1 + ceil(n/2);
      if itv then nblock := 2 : else nblock := 1: fi;
      fd := fopen("in.dat-s",WRITE,TEXT); 
      writeline(fd,convert(2*ceil(n/2),string)); # Gram matrix dimension
      writeline(fd,convert(nblock,string)); # blocks for the SDP problem matrix
      if not itv then writeline(fd,convert(nsdp,string)); # 1 block of size nsdp for the Gram matrix
      else nloc := ceil(n/2): fprintf(fd,"%d %d\n",nsdp,nloc); fi; # 2 blocks of size nsdp and nloc for the Gram and localizing matrices
      rfloat := convert(r,float,100); af := convert(a,float); bf := convert(b,float); 
      for i from 1 to 2*ceil(n/2) do fprintf(fd,"%s ",convert(coeff(rfloat,x,i),string));od;
      fprintf(fd,"\n");
      writeline(fd,"0 1 1 1 -1"); # Moment variable y0 = 1
      for j from 2 to nsdp do
      fprintf(fd, "%d 1 %d %d 1\n", j-1, 1, j); # Moment variable y_{1+j}
      od;
      for i from 2 to nsdp do
        for j from i to nsdp do
          fprintf(fd, "%d 1 %d %d 1\n", i+j-2, i, j); # Moment variable y_{i+j}
        od;
      od;
      #lprint("before itv");
      if itv then
      for i from 1 to nloc do
        for j from i to nloc do
          fprintf(fd, "%d 2 %d %d %s\n", i+j-2, i, j, convert(-sign(i+j-3)*bf*af,string)); # - b a y_{i+j-2}
          fprintf(fd, "%d 2 %d %d %s\n", i+j-1, i, j, convert(sign(i+j-2)*(bf+af),string)); # (b + a) y_{i+j-1}
          fprintf(fd, "%d 2 %d %d %s\n", i+j, i, j, convert(-sign(i+j-1),string)); # - y_{i+j}
        od;
      od;
      fi:
      fclose(fd);
      #system("cp in.dat-s inbkp.dat-s");
      system("sed -i 's/ \\./ 0\\./g' in.dat-s"); system("sed -i 's/^\\./0\\./g' in.dat-s"); system("sed -i 's/^-\\./-0\\./g' in.dat-s"); system("sed -i 's/ -\\./ -0\\./g' in.dat-s");


      system("rm -f out.dat-s"); system("rm -f out.mm");
      gmp := true:
      if not gmp then
      system("sdpa -ds in.dat-s -o out.dat-s -p param.sdpa > /dev/null");
      else
      write_param(precSDP,epsStar,epsDash);
      system("sdpa_gmp -ds in.dat-s -o out.dat-s -p my_param_gmp.sdpa > /dev/null");
      fi:
      system("echo $(grep objValPrimal out.dat-s) ';' 'yMat:=' $(sed -n '/yMat/,/main/{//!p}' out.dat-s) ';' >> out.mm");
      #system("echo 'yMat:=' $(sed -n '/yMat/,/main/{//!p}' out.dat-s) ';' >> out.mm");
      system("sed -i 's/ =/ :=/g' out.mm"): 
      system("sed -i 's/{/[/g' out.mm"): system("sed -i 's/}/]/g' out.mm"); system("sed -i 's/] \\[/], \\[/g' out.mm");
      read "out.mm": 
      #lprint(evalf(coeff(r,x,0)));
      lowerbnd := coeff(r,x,0) + convert(objValPrimal,rational,exact);
      #if lowerbnd < 0 then printf("lower bound: "); lprint(evalf(lowerbnd));fi:
      SVD := false;
      Y := Matrix(yMat[1]): (eigs,eivs) := eigseivs(Y,x,nsdp,precSVD,SVD);
      if itv then Y2 := Matrix(yMat[2]): (eigs2,eivs2) := eigseivs(Y2,x,nloc,precSVD,SVD): else eigs2:=Vector(1,0): eivs2:=Vector(1,0): fi:
      return (convert(eigs,list), convert(eivs,list), convert(eigs2,list), convert(eivs2,list),lowerbnd);
end;

checkrational := proc(U)
  local v:
  for v in U do:
    if not type(convert(v,rational),realcons) then 
    lprint(v): 
    error "Non Rational Cholesky factor, retry with gmp = true":fi:
  od:
  return:
end;


eigseivs := proc(Y,x,nmat,precSVD,SVD)
      local ti, tf, v, e, mons, eigs, eivs, gpround, normeig,U,S,V, Ysvd,Yexact,tcmp;
      mons := Vector(nmat,(j) -> x^(j-1));
      normeig := false; gpround := false;
      Yexact := convert(Y,rational,exact);
      #Yexact := Y;
      #ti := time[real]():
      if not SVD then
        ti := time[real]():
        lprint("starting Cholesky");
        U := LUDecomposition(Yexact,method='Cholesky');
        checkrational(U);
        #lprint(U);
        tcmp := time[real]() - ti: lprint (tcmp);
        lprint("ending Cholesky");
        S := IdentityMatrix(nmat);

        #(v, e) := Eigenvectors(Y);
        #tf := time[real](); printf("  Time for Computation of eigenvectors = %e ms\n",1000*(tf - ti));
        #ti := time[real]();
        #lprint(v); lprint(e);
        #eigs := evalc(Re(v)); eivs := Transpose(Transpose(mons).Re(e));
        #lprint(max(Y - v.DiagonalMatrix(e).v^%T));
        #tf := time[real](): printf("  Time for conversion = %e ms\n",1000*(tf - ti));      
      else 
        Digits:=precSVD;
        ti := time[real]():
        (U,S,V) := MTM[svd](Yexact); 
        #Ysvd := U.S.V^%T;
        #lprint(max(max(Y),-min(Y))); 
        #lprint(max(max(Ysvd),-min(Ysvd))); 
        #lprint(max(Y - Ysvd));
        tcmp := time[real]() - ti: lprint (tcmp);
        Digits:=10;
      fi;
        eigs := Diagonal(S); eivs := Transpose(Transpose(mons).U);
#      (eigs, eivs) := normalize(eigs,eivs,nmat,normeig);
#      eigs := convert(eigs,rational); eivs := map (_e -> roundeiv(_e,k,gpround), eivs);
#      eigs := convert(eigs,rational,exact); eivs := map (_e -> convert(_e,rational,exact), eivs);
      return (eigs, eivs):
end;

write_param := proc(precSDP,epsStar,epsDash)
      local fd;
      fd := fopen("my_param_gmp.sdpa",WRITE,TEXT); 
      fprintf(fd,"300	unsigned int maxIteration;\n");
      fprintf(fd,"1.0E-%d	double 0.0 < epsilonStar;\n",epsStar);
      fprintf(fd,"1.0E5   double 0.0 < lambdaStar;\n");
      fprintf(fd,"2.0   	double 1.0 < omegaStar;\n");
      fprintf(fd,"-1.0E5  double lowerBound;\n");
      fprintf(fd,"1.0E5   double upperBound;\n");
      fprintf(fd,"0.1     double 0.0 <= betaStar <  1.0;\n");
      fprintf(fd,"0.3     double 0.0 <= betaBar  <  1.0, betaStar <= betaBar;\n");
      fprintf(fd,"0.9     double 0.0 < gammaStar  <  1.0;\n");
      fprintf(fd,"1.0E-%d	double 0.0 < epsilonDash;\n",epsDash);
      fprintf(fd,"%d     precision\n",precSDP);
      fclose(fd);
end;

# truncate := proc(eigs)
#  return map (_e -> if _e <= 1e-2 then 0: else _e fi, eigs)
# end;

# roundeiv := proc(eiv,gprec,gpround)
#   local fd;
#   if gpround then
#     fd := fopen("in.gp",WRITE,TEXT); writeline(fd,"eiv =", convert(eiv,string)); writeline(fd,"i =", convert(gprec,string)); fclose(fd);
#     system("rm -f out.gp"); system("gp -q  myround.gp"); read "out.gp";
#     return pgp:
#   else return convert(eiv,rational): 
#  fi:
# end;

# normalize := proc(eigs,eivs,nsdp,normeig)
#  local i,e:
#  e := Vector(nsdp);
#  if normeig then 
#    for i from 1 to nsdp do
#      e[i] := abs(sqrt(eigs[i]))*eivs[i];
#    od:
#    return (Vector(nsdp,1.0),e):
#  else return (eigs,eivs):
#  fi:
# end;

printpol := proc(p)
 lprint(sort(evalf(expand(p)),x,plex));
end;

sositv3:=proc(f, x, a, b, prec::integer := 10, precSVD::integer := 10, precSDP::integer := 200, epsStar::integer := 3, epsDash::integer:=3)
  local  bitsos, n, cf, q, sosq, clist, soslist, soslist2, rlist, tlist, nc, l, sosf1, sosf2, sosdecomp, ti, tcmp,sos,sos2, h, S, c, SEVEN, SODD, s, ds, dq, p1, p2, m, t, e, r, k, ok, eigs, eigs2, sumsos, sumsos2, u, v, i, sqs, cfs, id, cnd, maxp1, obj_plus_r0;
  n := degree(f); id := 2;
  if n = 0 and f<0 then error "There is no decomposition into sum of squares for this polynomial"; fi;
  if b < a then error cat("The interval [", convert(a, string), ", ", convert(b, string), "] is not valid")  fi;
  h := add(coeff(f,x,i)*(1+y^2)^(n-i)*(a+b*y^2)^i, i=0..n);
  S := sqrfree(h);
  c := lcoeff(f);
  #if c < 0 then lprint(h): error "There is no decomposition into sum of squares for this polynomial"; fi;

  SEVEN:=map(_e->if type(_e[2],even) then _e[1]^(_e[2]/2) fi, S[2]):
  SEVEN:=[op(SEVEN),op(map(_e->if type(_e[2],odd) then _e[1]^((_e[2]-1)/2) fi, S[2]))]:
  SEVEN:=remove(member, SEVEN, [1]);
  SODD:=map(_e->if type(_e[2],odd) then _e[1] fi, S[2]):

	s:=mul(se, se in SEVEN):
	q:=S[1]*mul(so, so in SODD): 
  ds := degree(s,y); dq := degree(q,y)/2;
  p1 := 1/(b-a)^dq * add(coeff(q,y,2*i)*(b-x)^(dq-i)*(x-a)^i, i=0..dq); 
  p2 := 1/(b-a)^ds * add(coeff(s,y,2*i)*(b-x)^(ds-i)*(x-a)^i, i=0..ds); 
  p1 := expand(p1);
  #maxp1:=max (map(_c -> abs (_c),[coeffs(p1)]));
  maxp1 := 1;
  p1 := 1/maxp1*p1;

  #lprint(p1);

  # If it's a constant (i.e. the polynomial is a constant multiple of 
  # a perfect square) then return almost immediately.                 
  n := degree(p1,x);
  m := ceil(n/2);

  if (n = 0) then lprint(p1, " * (", p2, ")^2"); fi;

  # if id = 2 let t = 1 + x^2 + ... + x^2m else if id = 1 then let t = 1 + x^1 + x^2 + ... + x^2m-1
  # let r = p1 - e * t be a safe perturbation 
  t := p1:
  if id = 3 then t := sum(abs(coeff(p1,x,i))*x^(i),i=0..n) else if id = 2 then t:= sum(x^(2*i),i=0..m) else if id = 1 then t:= sum(x^j,j=0..n) fi:fi: fi:

  #e := min(1,abs(c))/2:
  e := 1/2^prec;
  # (degree(p1 - e*t) <= 0
	# while (sturm(p1-e*t,x,a,b) > 0) do e:=e/2: od;
  # e := e / 2;
  r := p1 - e * t;
  #printf(%s,"pertur :"); printpol(r); printf("\n");
  # Choose rounding k of roots accurate enough to make the rest work */
  k := prec; ok := false;
  while not ok do 
    #k := k+1;
    (eigs,soslist,eigs2,soslist2,obj_plus_r0) := sossdp(r,x,precSVD,precSDP,epsStar,epsDash,a,b,true);
    sumsos := obj_plus_r0 + sum(eigs[j]*soslist[j]^2,j=1..nops(soslist));
    sumsos2 := (b-x)*(x-a)*sum(eigs2[j]*soslist2[j]^2,j=1..nops(soslist2));
    #printf(%s,"sumsos :"); printpol(expand(sumsos + sumsos2)); printf("\n");
    u := r - sumsos - sumsos2;
    #printf(%s,"remain :"); printpol(u); printf("\n");
    #printf(%s,"absorb :"); printpol(e*t); printf("\n");
    v := expand(e * t + u + obj_plus_r0);
    #for i from 0 to n do lprint(coeff(v,x,i)); od;
    ok := true;
    for i from 0 to m do
      #printf("i = %d\n",i); lprint(coeff(v,x,2*i+1)):   
      cnd:= coeff(v,x,2*i) - (abs(coeff(v,x,2*i+1))/4 + abs(coeff(v,x,2*i-1)));
      if not (cnd >=0) then 
       printf("prec = %d\t idx = %d\t err = %8.3e\t",k,i,evalf(cnd)); #lprint(cnd): 
         #lprint(evalf(coeff(v,x,2*i+1))):
        ok:= true:error("not enough precision");break:fi:
    od;
    break;
    #lprint("done");
  od;

  # Accumulate the final list of squares and coefficients
  # sqs := [1, op(soslist)]; cfs := [obj_plus_r0, op(eigs)]; 
  sqs := [op(soslist)]; cfs := [op(eigs)]; 

  for i from 0 to m do
    sqs := [op(sqs),x^i]: 
    cfs := [op(cfs),coeff(v,x,2*i) - (abs(coeff(v,x,2*i+1))/4 + abs(coeff(v,x,2*i-1)))]:
  od;
  for i from 0 to m-1 do
    sqs := [op(sqs),x^i  * (x + sign(coeff(v,x,2*i+1)) / 2)]: 
    cfs := [op(cfs),abs(coeff(v,x,2*i+1))]:
  od;

 # Now put back in the factor from the initial decomposition */

  sos := []; sos2:=[];
  for i from 1 to nops(sqs) do
    sos := [op(sos),maxp1*cfs[i],p2*sqs[i]]:
  od;
  for i from 1 to nops(eigs2) do
    sos2 := [op(sos2),maxp1*eigs2[i],p2*soslist2[i]]:
  od;

  return (sos,sos2):

end;

