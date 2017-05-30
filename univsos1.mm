$define debugt false

sos1 := proc(f, X)
  return SOSDecomp(expand(f),X,0):
end;

SOSDecomp:=proc(f, X, prec::integer := 8)
local g, h, S, SEVEN, SODD, newF;

if degree(f)=0 and f<0 then lprint(f): error "There is no decomposition into sum of squares for this polynomial"; fi;
if degree(f)=0 and f>=0 then return [[0,[0,0,f]]]; fi;
if f=0 then return [[0,[0,0,0]]]; fi;
if lcoeff(f, X)<0 then lprint(f): error "There is no decomposition into sum of squares for this polynomial"; fi;
if irem(degree(f), 2)=1 then 
    lprint(f): error "There is no decomposition into sum of squares for this polynomial";
else 
    if degree(f, X)=2 then return [[0, SOSDecompDegree2(f, X)]]; fi;
    g:=gcd(f, diff(f,X),'newF'):
#lprint("-->", g);
    if degree(g)=1 then 
	newF:=quo(newF, g,X):
	if degree(newF)=2 then 
#	    lprint("Special degree 2");
#	    lprint("rrr", CHECK(newF, SOSDecompDegree2(newF, X)), newF);
#VM	    return map(_el-> [_el[1],[op(_el[2]),g]],SOSDecompDegree2(newF, X))
      return [[g, [0,0,0]],[0, SOSDecompDegree2(newF, X)]]:

	else
#	    lprint("aaa", CHECK(newF, SOSDecompSQF(newF, X,prec)));
#VM	    return map(_el-> [_el[1],[op(_el[2]),g]],SOSDecompSQF(newF, X,prec)):
      return [[g,[0,0,0]],op(SOSDecompSQF(newF, X,prec))]:

	fi;
    fi;
    S:=sqrfree(f): 
    SEVEN:=map(_e->if type(_e[2],even) then _e[1]^(_e[2]/2) fi, S[2]):
    SEVEN:=[op(SEVEN),op(map(_e->if type(_e[2],odd) then _e[1]^((_e[2]-1)/2) fi, S[2]))]:
#lprint("SEVEN", SEVEN);
    SEVEN:=remove(member, SEVEN, [1]);
    SODD:=map(_e->if type(_e[2],odd) then _e[1] fi, S[2]):
#    lprint("deg gcd", degree(g)); 
#    lprint("SEVEN, SODD", nops(SEVEN), nops(SODD));
    if nops(SEVEN)=0 then 
	return SOSDecompSQF(f, X, prec);
    else

	g:=mul(s, s in SEVEN):
	h:=S[1]*mul(s, s in SODD): 
  return [[g,[0,0,0]], op(SOSDecomp(h, X,prec))];
#VM	return map(_el-> [_el[1],[op(_el[2]),g]], SOSDecomp(h, X,prec));

    fi;
fi;
end;



SOSDecompSQF:=proc(f, X,prec::integer := 8)
local g, h, content_h, SOS_h, SOS_g;
#Objectif : on cherche g et h tel que f=g+h avec h non square-free et h>=0 et g>=0 et g de degre 2.

#Etape 1 : chercher g
#Digits:=1:
#lprint("Degree: ", degree(f));
#2*ceil(log[2](1/degree(f)*abs(subs(X=1, diff(f,X))))))
g:=ConstructGPolynomial(f, X, prec);
#Etape 2 : construire h
h:=expand(f-g[1]*g[2]^2);
#Etape 3 : renvoyer la bonne reponse
if h<>0 then

#content_h:=content(h):
#SOS_h:=SOSDecomp(primpart(h), X):
#SOS_h:=map(_pairs->[[op(_pairs[1]), sqrt(content_h)], _pairs[2]], SOS_h):
#VM SOS_g:=SOSDecompDegree2(g, X):
SOS_g:=g:

SOS_h:=SOSDecomp(h, X,prec):
#VM return [op(SOS_g), op(SOS_h)]:
return [[1,SOS_g], op(SOS_h)]:

#return [op(SOSDecompDegree2(g, X)), op(SOSDecomp(h, X,prec))];
else
#VM SOS_g:=SOSDecompDegree2(g, X):
SOS_g:=g:

return  [[0,SOS_g]];
#VM return [op(SOSDecompDegree2(g, X))];
fi;
end;



## Output: SOS decomposition of a degree 2 polynomial f 
##         given as a list [c1,p,c2] such that f = c1*p^2 + c2

SOSDecompDegree2:=proc(f, X)
local a,b,c, mycouple;

#VM if f=0 then return [[[1],[f]]] fi;
if f=0 then return [f,0,0] fi;

#VM if degree(f)=0 and f>0 then return [[[f],[1]]]; fi;
if degree(f)=0 and f>0 then return [0,0,f]; fi;

if degree(f)=1 or (degree(f)=0 and f<0) or coeff(f,X,2)<0 or coeff(f,X,1)^2 - 4*coeff(f,X,2)*coeff(f,X,0) > 0 then 
    lprint(f):
    error "There is no decomposition into sum of squares for this polynomial"; 
fi;

#if nops(f)=3 then
#c,b,a:=coeffs(f): #coeff(f, X, 2), coeff(f, X, 1), coeff(f, X, 0);
#else 
c,b,a:=seq(coeff(f,X,i),i=0..2):
#fi;

#Attention j'ai vire les racines carrees pour aller plus vite
#VM mycouple:=[[[a],[X+b/(2*a)]],[[(c-b^2/(4*a))], [1]]];
#VM return mycouple;
return [a,X+b/(2*a),c - b^2/(4*a)];
end;


ConstructGPolynomial:=proc(f, X,myprec)
local i, inv_roots1, smallest, sf, sdf, g, t, df, values, mymin, minimizer, a,b,c,newt, _interval, count, mybound, boo:


  df:=numer(diff(f, X));

  inv_roots1:=fgbrs:-rs_isolate_uni(df, X, precision=myprec,verbose=0);
  #lprint(inv_roots1);


  values:=map(_s->subs(X=_s, f), map(_r->_r[1], inv_roots1)):
  mymin:=min(op(values)):
  for i from 1 to nops(inv_roots1) do 
    if subs(X=inv_roots1[i][1],f)=mymin then 
	minimizer:=inv_roots1[i]:
	_interval:=inv_roots1[i]:
    fi:
  od:
  if myprec = 0 then t := round(minimizer[1]); 
  else 
   if minimizer[1] < 0 then t:= ceil(minimizer[1]): else t:= floor(minimizer[1]): fi;
  fi;

#lprint("prec", evalf(log[2](1/(_interval[2]-_interval[1]))));

#if subs(X=t, primpart(df))<0 then lprint("ok"); else lprint("!!!!!!!!"); fi;


  sf:=subs(X=t, f): 
  if sf=0 then 
      lprint(f):
      error "There is no decomposition into sum of squares for this polynomial";
  fi;
  sdf:=subs(X=t, diff(f, X)): 

#g:=expand(sf+sdf*(X-t)+sdf^2/(4*sf)*(X-t)^2);
  a:=sdf^2/(4*sf): c:=sf-sdf*t+t^2*sdf^2/(4*sf): b:=sdf-2*sdf^2/(4*sf)*t:
  boo:=CheckTvalue(t, a,b,c, f, X):
  if boo then 
#      lprint("YYYEEEEESSSS", t);
#VM    return a*X^2+b*X+c;
       #lprint("ConstructGpol",t);
       return [1/sf,sdf/2*(X-t)+sf,0]; 
  fi;
  if minimizer[1]-t>0 then 
    mybound:=floor(log[2](minimizer[1]-t)):
  else 
      mybound:=myprec: 
  fi;
#  sf:=subs(X=minimizer[1], f): 
#  sdf:=subs(X=minimizer[1], diff(f, X)): 
#  a:=sdf^2/(4*sf): c:=sf-sdf*t+t^2*sdf^2/(4*sf): b:=sdf-2*sdf^2/(4*sf)*t:


      count:=mybound:
      t:=t+2^(mybound);
      sf:=subs(X=t, f): 
      sdf:=subs(X=t, diff(f, X)): 
#lprint(evalf(sf));
#      lprint("boo init", boo, evalf(t), evalf([minimizer[1], minimizer[2]]), evalf(sf), evalf(sdf));
      while boo=false and sf>=0 and t< minimizer[2] and sdf <=0 do 
        a:=sdf^2/(4*sf): c:=sf-sdf*t+t^2*sdf^2/(4*sf): b:=sdf-2*sdf^2/(4*sf)*t:
        boo:=CheckTvalue(t, a,b,c, f, X):
        if boo=true then 
        return [1/sf,sdf/2*(X-t)+sf,0]; 
        fi;
#	count:=count-1:
        newt:=t+2^(count);
        sf:=subs(X=newt, f): 
      	sdf:=subs(X=newt, diff(f, X)): 
        	while newt>=minimizer[2] or sf<=0 do 
        	  count:=count-1:
        	  newt:=t+2^(count);
#	  sdf:=subs(X=newt, diff(f, X)): 
        	od;
      	t:=newt;
#        sf:=subs(X=t, f): 
#	sdf:=subs(X=t, diff(f, X)): 
	# if sf<=0 then lprint("!!"); fi; 
	# if sdf>=0 then lprint("??"); fi;
	# lprint("boo", boo, evalf(t), evalf([minimizer[1], minimizer[2]]), evalf(sf), evalf(sdf));
        od;
   #    lprint("pas cool 0", t, minimizer[1], mybound, degree(f));
   #    return ConstructGPolynomialRec(f, X, 2*myprec);
   # else 
#        lprint("pas cool", t, minimizer[1], mybound, degree(f));
#        return NaiveBolzano(f, X);

        return ConstructGPolynomialRec(f, X, 2*myprec);
   # fi;


end;

getcoeffs := proc(f,X)
local c,nc,dc,lcmf:
c := PolynomialTools:-CoefficientVector(f,X);
nc, dc := MTM[numden](c);
lcmf := ilcm (op(convert(dc,list)));
return Vector(lcmf*c);
end;

ConstructGPolynomialRec:=proc(f, X, myprec, useNewton::boolean := false, aNewton::rational := 0, bNewton::rational := 0)
local mid, fcoeffs, newaNewton, newbNewton, dfa, dfb, i, inv_roots1, smallest, sf, sdf, g, t, df, values, mymin, minimizer, a, b, c, _interval:
df:=convert(diff(f, X),horner);

if useNewton then 
mid := aNewton + (bNewton - aNewton)*1/2;
fcoeffs := getcoeffs(diff(f,X),X);
#lprint(diff(f,X)); lprint(fcoeffs); dfa := subs(X=aNewton,df); dfb := subs(X=bNewton,df); lprint(dfa); lprint(dfb);
newaNewton, newbNewton := MyUnivariateNewton (fcoeffs, aNewton, bNewton, mid);
  if newaNewton > 0 then t:= newbNewton: else t := newaNewton fi:
  if debugt then lprint("t Newton", t); fi:
else
#lprint("--> isolate", myprec);
inv_roots1:=fgbrs:-rs_isolate_uni(primpart(diff(f, X)), X,precision=myprec,verbose=0);
#lprint("isolate --> ");
values:=map(_s->subs(X=_s, f), map(_r->_r[1], inv_roots1)):
mymin:=min(op(values)):
for i from 1 to nops(inv_roots1) do 
if subs(X=inv_roots1[i][1],f)=mymin then 
minimizer:=inv_roots1[i]:
_interval:=inv_roots1[i]:
fi:
od:
newaNewton := minimizer[1]; newbNewton := minimizer[2];
t:=minimizer[1];
if debugt then lprint("t Normal", t): fi:
fi:
#lprint("prec", evalf(log[2](1/(_interval[2]-_interval[1]))));

sf:=subs(X=t, f):
if sf=0 then 
    error "There is no decomposition into sum of squares for this polynomial";
fi;

sdf:=subs(X=t, df):
a:=sdf^2/(4*sf): c:=sf-sdf*t+t^2*a: b:=sdf-2*t*a:

if CheckTvalue(t, a,b,c, f, X) then 
#Il faut verifier que g reste >=0 sur les reels. 
if debugt then lprint("Before Rounding", t, "prec", myprec); fi:
#return ConFrac(t,f,df,X,sf,sdf,myprec);
#return SmallerApprox(t,f,df,X,sf,sdf);
return [1/sf,sdf/2*(X-t) + sf,0]; 
fi;
if debugt then lprint("increasing prec to", 2*myprec); fi:
return ConstructGPolynomialRec(f, X,2*myprec,false,newaNewton,newbNewton);

end;


NaiveBolzano := proc(f,X)
local df, inv_roots1, values, mymin, i, minimizer, _interval, t1, t2;
df:=convert(diff(f, X),horner);
 inv_roots1:=fgbrs:-rs_isolate_uni(primpart(diff(f, X)), X,precision=2,verbose=0);
values:=map(_s->subs(X=_s, f), map(_r->_r[1], inv_roots1)):
mymin:=min(op(values)):
for i from 1 to nops(inv_roots1) do 
if subs(X=inv_roots1[i][1],f)=mymin then 
minimizer:=inv_roots1[i]:
_interval:=inv_roots1[i]:
fi:
od:
t1 := minimizer[1]; t2 := minimizer[2];
return BolzanoRec(f, df, X, t1, t2);
end;

BolzanoRec := proc(f,df,X,t1,t2)
local t, sf, sdf, a, c, b;
t := (t1 + t2) / 2;
sf:=subs(X=t, f):
if sf=0 then 
    error "There is no decomposition into sum of squares for this polynomial";
fi;


sdf:=subs(X=t, df): a:=sdf^2/(4*sf): c:=sf-sdf*t+t^2*a: b:=sdf-2*t*a:
if sdf = 0 then return [1/sf,sdf/2*(X-t) + sf,0];  fi:
if sdf > 0 then 
  if CheckTvalue(t, a,b,c, f, X) then return [1/sf,sdf/2*(X-t) + sf,0]; fi:
  return BolzanoRec (f,df,X,t1,t): fi:

  if CheckTvalue(t, a,b,c, f, X) then return [1/sf,sdf/2*(X-t) + sf,0]; fi:
  return BolzanoRec (f,df,X,t,t2);
end;

ConFrac:=proc(t,f,df,X,sf,sdf,myprec)
  local newt, newsf, newsdf,a,b,c;
  newt := confrac2rat(convert(t,confrac,myprec)):
  lprint(newt):
  newsf:=subs(X=t,f): newsdf:=subs(X=t, df): 
  a:=newsdf^2/(4*newsf): c:=newsf-newsdf*newt+newt^2*a: b:=newsdf-2*newt*a:
  if CheckTvalue(newt,a,b,c,f,X) then return [1/newsf,newsdf/2*(X-newt) + newsf,0];
  else return [1/sf,sdf/2*(X-t) + sf,0] fi:
end;

SmallerApprox:=proc(t,f,df,X,sf,sdf)
  local newt, newsf, newsdf,a,b,c,myprec;
  myprec := floor(BitRat(t)/8);
  if t > 0 then newt := BinaryApproximationDown(t, myprec) : else newt := BinaryApproximationUp(t, myprec) fi:
  newsf:=subs(X=t,f): newsdf:=subs(X=t, df): 
  a:=newsdf^2/(4*newsf): c:=newsf-newsdf*newt+newt^2*a: b:=newsdf-2*newt*a:
  if CheckTvalue(newt,a,b,c,f,X) then 
  lprint("After rounding ", newt):
  return [1/newsf,newsdf/2*(X-newt) + newsf,0];
  else return [1/sf,sdf/2*(X-t) + sf,0] fi:
end;

CheckTvalue:=proc(t,a,b,c,f, X)
local F, S, SODD,newg, g, newF;
#Il faut verifier que f-g>=0 sur les reels

if (a=0 and b<>0) or (a=0 and b=0 and c<0) then 
return false:
fi:

if a<>0 and b^2-4*a*c>0 then 
    return false;
fi;
#lprint("tototutu");

F:=f-a*X^2-b*X-c:
g:=gcd(F, diff(F, X),'newF'):
#lprint("-->",degree(g));
if degree(g)=1 then
#  divide(F, g^2,'newF');
  newF:=quo(newF, g, X);
  if nops(fgbrs:-rs_isolate_uni(numer(newF), X, precision=1))>0 then 
    return false;
  else 
    #lprint(t); 
    return true;
  fi;
else
  S:=sqrfree(F):
#  lprint("-->",nops(S));
  SODD:=map(_e->if type(_e[2],odd) then _e[1] fi, S[2]);
  SODD:=mul(s, s in SODD):

  if nops(fgbrs:-rs_isolate_uni(SODD, X, precision=1))>0 then 
    return false;
  else 
    #lprint(t);
    return true;
  fi;
fi;
end;



oldCheckTvalue:=proc(t,g,f, X)
local a,b,c, F, S, SODD,newg;
#Il faut verifier que f-g>=0 sur les reels
a,b,c:=coeff(g, X, 2), coeff(g, X, 1), coeff(g, X, 0);
#lprint(a,b,c, b^2-4*a*c, c-b^2/(4*a));
if (a=0 and b<>0) or (a=0 and b=0 and c<0) then 
return false:
fi:

if a<>0 and b^2-4*a*c>0 then 
    return false;
fi;

#lprint("ici");
F:=normal(f-g):
#lprint("F dans check", F, factor(F));
S:=sqrfree(F):
#lprint(S);
SODD:=map(_e->if type(_e[2],odd) then _e[1] fi, S[2]);
SODD:=mul(s, s in SODD):
#lprint(SODD, factor(SODD));
if nops(fgbrs:-rs_isolate_uni(primpart(SODD), X, precision=1))>0 then 
    return false;
else 
    return true;
fi;


end;


#XXX: le probleme se situe dans les appels
#takes [a, b]  containing a unique root of pol
#returns [a,b'] or [a',b] containing a unique root 
#of pol with b'-a < (b-a)/2 (or b-a'<(b-a)/2)
MyNewtonIterator:=proc(_interval, pol)
local a,b,c, X, newa:
#option inline;
#lprint("!");
a:=_interval[1]:b:=_interval[2]:
X:=op(1,indets(pol));
#lprint(eval(diff(pol, X),X=a));
#lprint("!!");

#newa:=a+eval(pol, X=a)/eval(diff(pol, X),X=a);
newa:=a-subs({X=a},pol)/subs({X=a},diff(pol, X));
#lprint("!!!", evalf([newa, a]), evalf([subs(X=newa,pol), subs(X=a, pol)]));

#if subs({X=newa},pol)>0 then error "bug in Newton";fi;
#lprint("!!!!");

return [newa, b];

end;


#takes [a, b]  containing a unique root of pol
#returns [a,b'] or [a',b] containing a unique root 
#of pol with b'-a < (b-a)/2 (or b-a'<(b-a)/2)

BolzanoIterator:=proc(_interval, pol)
local a,b,c, X, sc:

a:=_interval[1]:b:=_interval[2]:
c:=(a+b)/2:
X:=op(1,indets(pol));

sc:=eval(pol, X=c):

if sc=0 then return [a, c]: fi:

if sign(sc)=sign(eval(pol, X=a)) then 
    return [c, b];
else 
    return [a, c];
fi;
end;


UnivariateSumOfSquaresDecItv:=proc(f, a, b)
  local psatz, bitsos, n, cf, q, sosq, clist, soslist, rlist, tlist, nc, l, sosf1, sosf2, sosdecomp, ti, tcmp,sos;
  psatz := false;
  n := degree(f);
  if n = 0 and f<0 then error "There is no decomposition into sum of squares for this polynomial"; fi;
  if b < a then error cat("The interval [", convert(a, string), ", ", convert(b, string), "] is not valid")  fi;
  q := add(coeff(f,x,i)*(1+y^2)^(n-i)*(a+b*y^2)^i, i=0..n);
  ti := time(): 
  sosq := SOSDecomp(q,y,2);
  tcmp := time() - ti:
  lprint (tcmp);
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

HornerToList := proc(sos)
  local hd, tl, p, c, q, d;
  if nops(sos) = 0 then return [] fi;
  if nops(sos) = 1 then p,c,q,d := sos[1][1],op(sos[1][2]): if (c=0 and d = 0) then return [[1,p]] fi: if c = 0 then return [[1, p], [d,1]] fi: if d = 0 then return [[1, p],[c,q]] fi: return [[1, p],  [c,q],  [d,1]] fi:
  hd,tl := HdTailList(sos): p,c,q,d := hd[1], op(hd[2]);
  if (c = 0 and d = 0) then return [op(MulPolList2(p, HornerToList(tl)))] fi: if c = 0 then return  [op(MulPolList2(p, HornerToList(tl))),[d, 1]] fi: if d = 0 then return  [op(MulPolList2(p, HornerToList(tl))), [c, q]] fi; 
  return [op(MulPolList2(p, HornerToList(tl))), [c, q],[d, 1]];
end;

HdTailList := proc(l)
  return l[1],[seq(l[i],i=2..nops(l))];
end;

MulPolList2:= proc(p, l)
  map (el -> [el[1], p*el[2]], l)
end;

MulPolList:= proc(p, l)
  map (el -> p*el, l)
end;
