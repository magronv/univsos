

SOSDecomp:=proc(f, X)
local g, h, S, SEVEN, SODD, newF;

if degree(f)=0 and f<0 then  error "There is no decomposition into sum of squares for this polynomial"; fi;
if degree(f)=0 and f>=0 then return [[f,1]]; fi;
if f=0 then return [[1,f]]; fi;
if lcoeff(f, X)<0 then     error "There is no decomposition into sum of squares for this polynomial"; fi;
if irem(degree(f), 2)=1 then 
    error "There is no decomposition into sum of squares for this polynomial";
else 
    if degree(f, X)=2 then return SOSDecompDegree2(f, X); fi;
    g:=gcd(f, diff(f,X),'newF'):
#lprint("-->", g);
    if degree(g)=1 then 
	newF:=quo(newF, g,X):
	if degree(newF)=2 then 
#	    lprint("Special degree 2");
#	    lprint("rrr", CHECK(newF, SOSDecompDegree2(newF, X)), newF);
	    return map(_el-> [_el[1],[op(_el[2]),g]],SOSDecompDegree2(newF, X))
	else
#	    lprint("aaa", CHECK(newF, SOSDecompSQF(newF, X)));
	    return map(_el-> [_el[1],[op(_el[2]),g]],SOSDecompSQF(newF, X)):
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
	return SOSDecompSQF(f, X);
    else

	g:=mul(s, s in SEVEN):
	h:=S[1]*mul(s, s in SODD): 
	return map(_el-> [_el[1],[op(_el[2]),g]], SOSDecomp(h, X));

    fi;
fi;
end;



SOSDecompSQF:=proc(f, X)
local g, h, content_h, SOS_h, SOS_g;
#Objectif : on cherche g et h tel que f=g+h avec h non square-free et h>=0 et g>=0 et g de degre 2.

#Etape 1 : chercher g
#Digits:=1:
#lprint("Degree: ", degree(f));
#2*ceil(log[2](1/degree(f)*abs(subs(X=1, diff(f,X))))))
g:=expand(ConstructGPolynomial(f, X, 8));
#Etape 2 : construire h
h:=expand(f-g);
#Etape 3 : renvoyer la bonne reponse
if h<>0 then

#content_h:=content(h):
#SOS_h:=SOSDecomp(primpart(h), X):
#SOS_h:=map(_pairs->[[op(_pairs[1]), sqrt(content_h)], _pairs[2]], SOS_h):
SOS_g:=SOSDecompDegree2(g, X):
SOS_h:=SOSDecomp(h, X):
return [op(SOS_g), op(SOS_h)]:
bitsos := BitSizePolSeq(sosf1,x) + BitSizePolSeq(sosf2,x) + 2 * BitSizeSeq(clist);
#return [op(SOSDecompDegree2(g, X)), op(SOSDecomp(h, X))];
else 
return [op(SOSDecompDegree2(g, X))];
fi;
end;




SOSDecompDegree2:=proc(f, X)
local a,b,c, mycouple;

if f=0 then return [[[1],[f]]] fi;
if degree(f)=0 and f>0 then return [[[f],[1]]]; fi;
if degree(f)=1 or (degree(f)=0 and f<0) or coeff(f,X,2)<0 or coeff(f,X,1)^2 - 4*coeff(f,X,2)*coeff(f,X,0) > 0 then 
    error "There is no decomposition into sum of squares for this polynomial"; 
fi;

if nops(f)=3 then
c,b,a:=coeffs(f): #coeff(f, X, 2), coeff(f, X, 1), coeff(f, X, 0);
else 
c,b,a:=seq(coeff(f,X,i),i=0..2):
fi;

#Attention j'ai vire les racines carrees pour aller plus vite
mycouple:=[[[a],[X+b/(2*a)]],[[(c-b^2/(4*a))], [1]]];

return mycouple;
end;


ConstructGPolynomial:=proc(f, X,myprec)
local i, inv_roots1, smallest, sf, sdf, g, t, df, values, mymin, minimizer, a,b,c,newt, _interval, count, mybound, boo:


  df:=numer(diff(f, X));

  inv_roots1:=fgbrs:-rs_isolate_uni(df, X, precision=myprec,verbose=0);

  values:=map(_s->subs(X=_s, f), map(_r->_r[1], inv_roots1)):
  mymin:=min(op(values)):
  for i from 1 to nops(inv_roots1) do 
    if subs(X=inv_roots1[i][1],f)=mymin then 
	minimizer:=inv_roots1[i]:
	_interval:=inv_roots1[i]:
    fi:
  od:
  t:=floor(minimizer[1]);

#lprint("prec", evalf(log[2](1/(_interval[2]-_interval[1]))));

#if subs(X=t, primpart(df))<0 then lprint("ok"); else lprint("!!!!!!!!"); fi;


  sf:=subs(X=t, f): 
  if sf=0 then 
      error "There is no decomposition into sum of squares for this polynomial";
  fi;
  sdf:=subs(X=t, diff(f, X)): 

#g:=expand(sf+sdf*(X-t)+sdf^2/(4*sf)*(X-t)^2);
  a:=sdf^2/(4*sf): c:=sf-sdf*t+t^2*sdf^2/(4*sf): b:=sdf-2*sdf^2/(4*sf)*t:
  boo:=CheckTvalue(t, a,b,c, f, X):
  if boo then 
#      lprint("YYYEEEEESSSS", t);
      return a*X^2+b*X+c;
  fi;
  if minimizer[1]-t>0 then 
    mybound:=floor(log[2](minimizer[1]-t)):
  else 
      mybound:=myprec: 
  fi;
#  sf:=subs(X=minimizer[1], f): 
#  sdf:=subs(X=minimizer[1], diff(f, X)): 
#  a:=sdf^2/(4*sf): c:=sf-sdf*t+t^2*sdf^2/(4*sf): b:=sdf-2*sdf^2/(4*sf)*t:
#  if CheckTvalue(minimizer[1], a,b,c, f, X) then 


      count:=mybound:
      t:=t+2^(mybound);
      sf:=subs(X=t, f): 
      sdf:=subs(X=t, diff(f, X)): 
#lprint(evalf(sf));
#      lprint("boo init", boo, evalf(t), evalf([minimizer[1], minimizer[2]]), evalf(sf), evalf(sdf));
      while boo=false and sf>=0 and t< minimizer[2] and sdf <=0 do 
#      while boo=false and t < minimizer[1] do 
#      while boo=false do 

	a:=sdf^2/(4*sf): c:=sf-sdf*t+t^2*sdf^2/(4*sf): b:=sdf-2*sdf^2/(4*sf)*t:
	boo:=CheckTvalue(t, a,b,c, f, X):
	if boo=true then 
	    return a*X^2+b*X+c;
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
        return ConstructGPolynomialRec(f, X, 2*myprec);
   # fi;


end;



ConstructGPolynomialRec:=proc(f, X, myprec)
local i, inv_roots1, smallest, sf, sdf, g, t, df, values, mymin, minimizer, a, b, c, _interval:

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
t:=minimizer[1];


#lprint("prec", evalf(log[2](1/(_interval[2]-_interval[1]))));

df:=convert(diff(f, X),horner);
sf:=subs(X=t, f):
if sf=0 then 
    error "There is no decomposition into sum of squares for this polynomial";
fi;

sdf:=subs(X=t, df):
#g:=expand(sf+sdf*(X-t)+sdf^2/(4*sf)*(X-t)^2);
a:=sdf^2/(4*sf): c:=sf-sdf*t+t^2*a: b:=sdf-2*t*a:
# if a<>coeff(g,X,2) then lprint("?");error"aaa"; fi;
# if b<>coeff(g,X,1) then lprint("?");error"bbb"; fi;
# if c<>coeff(g,X,0) then lprint("?");error"ccc"; fi;
# if CheckTvalue(t,a,b,c,f,X)<>oldCheckTvalue(t,g,f,X) then 
# lprint(CheckTvalue(t,a,b,c,f,X));
# lprint(oldCheckTvalue(t,g,f,X));

# error "tutu"; fi;
if CheckTvalue(t, a,b,c, f, X) then 
#Il faut verifier que g reste >=0 sur les reels. 
#if discrim(g, X)<=0 then 
return a*X^2+b*X+c;
fi;

return ConstructGPolynomialRec(f, X,2*myprec);


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


##CHECK with 
SOSCHECK:=proc(f, SOS)
return expand(
  add( mul(t, t in c[1]) * ( mul(t, t in c[2]) )^2, c in SOS)-f);
end;


