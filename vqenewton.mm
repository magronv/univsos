#read "vqeisolate2.mm";
$define DEBUGNEWTON false
$define TESTINTEGER true

$define TEST_SHIFT true


## ENTRÉE: f est univarie donne sous la forme d'un tableau
## a, b et mid sont des rationnels
## Hypothese: a < mid < b et [a,b] contient une et une seule racine de f
## mais ne contient pas 0.

## SORTIE : a',b' tel que a<a'<=rac<=b'<b. Si a et b ont une puissance
## de 2 comme dénom et f a coefficient entier alors a' et b' aussi.

## Modif Ivan : j'ai changé la sortie.
## Si b<0 on a considéré les racines de subs(f_in,var=-var) entre
## 0<-b<-a.  on a rafiné cet interval [-b,-a] en [newa,newb].  Il
## faut penser à retourner les valeurs raffinée de la racine de
## f_in c'est à dire [-newb, -newa].
MyUnivariateNewton:=proc(f_in, a_in, b_in, mid_in)
local f, a, b,mid,delta,prec,var,valmid, Df,POS,NEG,size,i,Dfmin,Dfmax,newa,newb, val_a;
local afin, bfin,valmid2;
#global count_newton;
    #if type(count_newton, symbol) then count_newton:=1: else count_newton:=count_newton+1 fi;
    if TESTINTEGER then
        if not(type(PolynomialTools:-FromCoefficientVector(f_in,x), polynom(integer)))
        then error "Call of Newton with polynomial with non-integer coefficients" fi;
    fi;


    #if DEBUGNEWTON then lprint(args); fi;
    a:=a_in; b:=b_in; mid:=mid_in;

    if b<a then error "a<b"; fi;

    delta:=abs(ilog2(b-a)/2):

    if delta =0 then print(); print(evalf(b-a)); fi;
    if b=a then error "a=b"; fi;
    prec:=4*delta:
    size:=LinearAlgebra:-RowDimension(f_in):
    #Algorithme: mid -f(mid)/f'([a, b])

    ## On s'assure que l'on applique Newton sur un point à coordonnées>0.
    if a<0 and b>0 then error "Newton with an interval [a,b] containing 0"; fi;
    if a=b then error "a=b"; fi;
    f, a, mid,b:=PolynomialAndBound(f_in,a,mid,b,size):



    Df:=Vector(size-1,[seq(f[i]*(i-1),i=2..size)]):
    Dfmin,Dfmax:=MySubsUpDownUnivPolPosNeg(Df,a,b,prec+2):

    if Dfmin<=0 and Dfmax>=0 then
        # name_in:=cat("test_",numer(a),"_",denom(a));
        # fd:=fopen(name_in,WRITE):
        # fprintf(fd,"read loadivan;\n");
        # fprintf(fd,"f:=%a:\n",PolynomialTools:-FromCoefficientVector(f,x));
        # fprintf(fd,"a:=%a: b:=%a:\n",a,b);
        # fprintf(fd,"c,d:=MyUnivariateNewton(PolynomialTools:-CoefficientVector(f,x),a,b,(a+b)/2);"):
        # fclose(fd);
        #printf("(£)");
        #lprint(evalf([a,b]),a,b);
        #printf("[%a,%a,%a]",evalf([a,b]),a,b);
    fi;

    #if Dfmin<=0 and Dfmax>=0 then
    #printf("dfm*dfM<0,deg:%d,val:[%a,%a]\n",LinearAlgebra:-RowDimension(POS),a,b);
    ## Modif IVAN 12/10/16 : on ajoute la ligne suivante pour
    ## faire un calcul plus précis en calculant les racines de
    ## diff(Df) si ça n'a pas déjà été fait.
    #Dfmin,Dfmax:=MySubsUpDownUnivPolPosNeg(POS,NEG,a,b,prec+2,var,true):
    #fi;

    ## Dfmin,Dfmax sont des rationnels avec une puissance de 2 en
    ## dénominateur.

    #On calcule f(mid)
    valmid:=MySubsUpDownAtPositiveRatSingleCoefficientVector(f, mid, var):

    ## si denom(mid) est une puissance de 2 et f a coeff entier, alors valmid
    ## est un rationnel avec une puissance de 2 en dénominateur.

    if valmid=0 then #printf("mid!");
        if b_in>0 then return mid,mid; else return -mid,-mid; fi;
    fi;
    #lprint("Dfmin", Dfmin); lprint("Dfmax", Dfmax);

    if Dfmin<=0 and Dfmax>=0 then
        #printf("ici1\n");
        #if DEBUGNEWTON then TestNewton2(f,a,b,Df, prec,Dfmin,Dfmax,size); fi;
        val_a:=MySubsUpDownAtPositiveRatSingleCoefficientVector(f, a, var):
        if val_a=0 then  #printf("a!!");
            if b_in>0 then return a,a; else return -a,-a; fi;
        fi;
        afin, bfin:=Bolzano(b_in, a,mid,b,val_a, valmid):
        #if DEBUGNEWTON then TestNewton(f_in, afin, bfin,valmid,a_in,
        #b_in,1); fi;
        if afin>bfin then error "afin>bfin"; fi;
        return afin, bfin;
    fi;
    #valmid:=subs(var=mid, PolynomialTools:-FromCoefficientVector(f,var));

    ## La ligne suivante évite le test newa<newb à la sortie.
    newa,newb:=op(sort([mid-valmid/Dfmax,mid-valmid/Dfmin]));
    #newa,newb:=mid-valmid/Dfmax,mid-valmid/Dfmin;

    if abs(newb-newa)>=abs(b-a) then
        val_a:=MySubsUpDownAtPositiveRatSingleCoefficientVector(f, a, var):
        if val_a=0 then #printf("a!!");
            if b_in>0 then return a,a; else return -a,-a; fi;
        fi;

        afin, bfin:=Bolzano(b_in, a,mid,b,val_a, valmid):
        if DEBUGNEWTON then TestNewton(f_in, afin, bfin,valmid,a_in,b_in,3); fi;
        if afin>bfin then error "afin>bfin"fi;
        return afin,bfin;
    fi;

    ## Modif Ivan : j'ai changé la sortie.
    ## Si b<0 on a considéré les racines de subs(f_in,var=-var) entre
    ## 0<-b<-a.  on a rafiné cet interval [-b,-a] en [newa,newb].  Il
    ## faut penser à retourner les valeurs raffinée de la racine de
    ## f_in c'est à dire [-newb, -newa].
    if b_in>0 then
        afin,bfin:=BinaryApproximationDown(newa,prec),BinaryApproximationUp(newb,prec);
    else
        afin,bfin:=BinaryApproximationDown(-newb,prec),BinaryApproximationUp(-newa,prec);
    fi;

    #printf("a_in:=%a; b_in:=%a;\n", a_in,b_in); printf("afin:=%a; bfin:=%a;\n", afin,bfin);

    ## on test si a_in<afin<bfin<b_in. Sinon, on redécoupe encore.
    if not(a_in<=afin and afin<=bfin and bfin<=b_in) then
        if afin>bfin then error "afin>bfin";
        elif afin>b_in then error "afin>b_in";
        elif bfin<a_in then error "bfin<a_in";
        elif afin<a_in and b_in<bfin then error "afin<a_in and b_in<bfin";
        elif afin<a_in then
            ## On part de l'hypothèse que f change de signe entre a_in
            ## et b_in. Donc forcément afin peut etre ramené à a_in.
            afin:=a_in:
        elif b_in<bfin then
            ## On part de l'hypothèse que f change de signe entre a_in
            ## et b_in. Donc forcément afin peut etre ramené à a_in.
            bfin:=b_in;
        else
            error "test manquant?";
        fi;
    fi;
    if DEBUGNEWTON then TestNewton(f_in, afin, bfin,valmid,a_in,b_in,5); fi;
    if afin>bfin then lprint("args=", args); error "bfin>afin"; fi;
    return afin, bfin;
    ## Précédente sortie.
    # if newa<newb then
    #     return BinaryApproximationDown(newa,prec),BinaryApproximationUp(newb,prec);
    # fi;
    # return BinaryApproximationDown(newb,prec),BinaryApproximationUp(newa,prec);
end:



## ENTREE : f_in polynome univarié sous forme de tableau.
## a, mid,b des rationnels tel que a<mid<b.
## size : entier, taille de la table de f.

## SORTIE : f,a',mid',b' tel que a',mid',b':=op(sort(abs([a,mid,b]));
## c'est à dire 0<a'<mid'<b' et f=f_in(-var) si b<0.
PolynomialAndBound:=proc(f_in,a,mid,b,size)
local f,i;
    f:=Vector(size);
    if b<0 then
        ## Dans subs(f,var=-var), le coefficient de var^k change de
        ## signe lorsque k est impaire. Les coeff sont rangé dans le
        ## vecteur comme suit : [a0,a1,...,a_deg] avec les indices
        ## commençant à 1.
        for i from 1 to size do
            if type(i,even) then ## f_in[i] coeff de var^(i-1).
                f[i]:=-f_in[i];
            else
                f[i]:=f_in[i];
            fi;
        od;
        if DEBUGNEWTON then
            if not(evalb(PolynomialTools:-FromCoefficientVector(f,var)=subs(var=-var,PolynomialTools:-FromCoefficientVector(f_in,var)))) then
                #lprint("f_2:=",PolynomialTools:-FromCoefficientVector(f,var), "f(-var):=",subs(var=-var,PolynomialTools:-FromCoefficientVector(f_in,var)));
                error "f(var=-var) incorrect";
            fi;
        fi;
        ## On prend le point à coordonnée positive correspondant.
        return f,-b,-mid,-a;
    else
        return f_in,a,mid,b;
    fi;
end proc;

## ENTREE : b_in, a, mid, b,val_a,valmid des rationnels.

## SORTIE :
## cas 1) si b_in>0 alors l'intervalle [a, mid] si f(a) et f(mid) (donnés par
## val_a et valmid) sont de signes différents. [mid,b] sinon.
## cas 2) si b_in<=0 alors l'interval [-mid,-a] si f(-mid) et f(-a) (donnés
## par val_a et valmid) sont de signes différents. [-b,-mid] sinon.
Bolzano:=proc(b_in, a,mid,b,val_a, valmid)
local afin, bfin;
    if b_in>0 then
        if valmid>=0 and val_a>0 then afin,bfin:=mid, b;
        elif valmid>=0 and val_a<0 then afin,bfin:=a, mid;
        elif valmid<=0 and val_a>0 then afin,bfin:=a, mid;
        elif valmid<=0 and val_a<0 then afin,bfin:=mid, b;
        else
            printf("\n");
            lprint(b_in,"a,mid,b",a,mid,b,"val_a,valmid",val_a, valmid);
            error "ici1?";
        fi;
    else
        if valmid>=0 and val_a>0 then afin,bfin:=-b,-mid;
        elif valmid>=0 and val_a<0 then afin,bfin:=-mid,-a;
        elif valmid<=0 and val_a>0 then afin,bfin:=-mid,-a;
        elif valmid<=0 and val_a<0 then afin,bfin:=-b,-mid
        else
            printf("\n");
            lprint(b_in,"a,mid,b",a,mid,b,"val_a,valmid",val_a, valmid);
            error "ici2?";
        fi;
    fi:
    return afin, bfin;
end proc;

## INPUT : f polynome univarié donné sous forme d'un tableau, afin,
## bfin, valmid, a_in,b_in des rationnels. i un entier.

## ERROR : lève une erreur si f(afin)*f(bfin)>0.
TestNewton:=proc(f,afin, bfin,valmid, a_in,b_in,i)
    if not(a_in<=afin and afin<=bfin and bfin<=b_in) then
        lprint(f,a_in, afin, bfin, b_in);
        if b_in>0 then
            printf("[afin, bfin] non inclu dans [a_in, b_in], %d\n",i);
        else
            printf("[afin, bfin] non inclu dans [a_in, b_in], %d\n",i+1);
        fi;
        error "[afin, bfin] non inclu dans [a_in, b_in]";
    fi;
    if (eval(PolynomialTools:-FromCoefficientVector(f,x),x=afin)*
        eval(PolynomialTools:-FromCoefficientVector(f,x),x=bfin))>0 then

        lprint(evalf(["f(newa)",eval(PolynomialTools:-FromCoefficientVector(f,x),x=afin),
                      "f(mid)",valmid,
                      "f(newb)",eval(PolynomialTools:-FromCoefficientVector(f,x),x=bfin)]));
        if b_in>0 then printf("f(newa)*f(newb)>0,ici%d\n",i);
        else printf("f(newa)*f(newb)>0,ici%d\n",i+1);
        fi;
        error "f(newa)*f(newb)>0";
    fi;
end proc;


TestNewton2:=proc(f,a,b,Df, prec,Dfmin,Dfmax,size)
local size2, Df2, POS2, NEG2, D2fmin, D2fmax,i;
    size2:=LinearAlgebra:-RowDimension(Df):
    Df2:=Vector(size2-1,[seq(Df[i]*(i-1),i=2..size2)]):
    POS2:=Vector(size2):
    NEG2:=Vector(size2):
    for i from 1 to size2-1 do
        if Df2[i]>0 then
            POS2[i]:=Df2[i]:
        else
            NEG2[i]:=-Df2[i]:
        end if;
    od:
    D2fmin,D2fmax:=MySubsUpDownUnivPolPosNeg(Df2,a,b,prec+2);
    lprint(size-1,"a, b-a", evalf(a,4),evalf(b-a,2),"[Dfmin,Dfmax]", evalf([Dfmin,Dfmax],2),
           "eval(x=a,.)",evalf([subs(x=a,diff(PolynomialTools:-FromCoefficientVector(f,x),x)),
                                abs(subs(x=a,diff(PolynomialTools:-FromCoefficientVector(f,x),x))-
                                    subs(x=b,diff(PolynomialTools:-FromCoefficientVector(f,x),x))),
                                "d^2f/dx^2",
                                subs(x=a, diff(diff(PolynomialTools:-FromCoefficientVector(f,x),x),x)),
                                subs(x=b, diff(diff(PolynomialTools:-FromCoefficientVector(f,x),x),x)),
                                "D2fmin, D2fmax", D2fmin, D2fmax
                               ],2)
          );
end proc;

# profile(DecomposePolynomial,
#         MySubsUpDownUnivPolPosNeg,
#         MySubsUpDownAtPositiveRatSingleCoefficientVector,
#         MySubsUpDownAtPositiveRat,
#         MySubsUpDownAtPositiveRatRec,
#         MySubsUpDownAtPositiveIntervalSingleCoefficientVector,
#         CutUnivPoly2,
#         BinaryApproximationDown,
#         BinaryApproximationUp,
#         IntervalValuesFracUnivListNum);
(**
deg:=3:
N:=12830:
#N:=1000:
nbits:=256;
pol:=randpoly([x],degree=deg,dense,coeffs=rand(-2^nbits..2^nbits)):
st:=time():
sol:=RootFinding:-Isolate(pol,x,output='interval')[-1];
xmin:=rhs(sol)[1]:
xmax:=rhs(sol)[2]:
lnum:=[seq(randpoly([x],degree=deg,dense,coeffs=rand(-2^nbits..2^nbits)),i=1..3)]:
den:=randpoly([x],degree=deg,dense,coeffs=rand(-2^nbits..2^nbits)):

st:=time():
st_eval:=0:
for i from 1 to N do
lnum:=[seq(randpoly([x],degree=deg-1,dense,coeffs=rand(-2^nbits..2^nbits)),j=1..3)]:
den:=randpoly([x],degree=deg,dense,coeffs=rand(-2^nbits..2^nbits)):
stt:=time():
IntervalValuesFracUnivListNum(lnum, den, xmin, xmax, 16):
st_eval:=st_eval+time()-stt:
od:
time()-st;
showprofile();
lprint("st_eval",st_eval);

st:=time():
st_eval:=0:
for i from 1 to N do
lnum:=[seq(randpoly([x],degree=deg-1,dense,coeffs=rand(-2^nbits..2^nbits)),j=1..3)]:
den:=randpoly([x],degree=deg,dense,coeffs=rand(-2^nbits..2^nbits)):
stt:=time():
subs(x=xmin, [den,seq(lnum[j],j=1..nops(lnum))]):
subs(x=xmax, [den,seq(lnum[j],j=1..nops(lnum))]):
st_eval:=st_eval+time()-stt;
od:
time()-st;
lprint("st_eval",st_eval);
**)

(**
deg:=51:
st_newton:=0:
st_isole:=0:
st_isoleprec:=0:
st_total:=time():
for i from 1 to 5000 do
    pol:=randpoly([x],degree=deg,dense,coeffs=rand(-2^128..2^128)):
    st:=time():
    sols:=RootFinding:-Isolate(pol,x,output='interval');
    st_isole:=st_isole+time()-st;
    sol:=rhs(sols[-1]);
    f:=PolynomialTools:-CoefficientVector(pol,x);
    mid:=(sol[1]+sol[2])/2:
    st:=time():
    newsol:=[MyUnivariateNewton(f,sol[1],sol[2],mid)];
    st_newton:=st_newton+time()-st;
#    lprint(abs(ilog2(newsol[2]-newsol[1])),abs(ilog2(sol[2]-sol[1])));
    if not(evalb(newsol[2]<sol[2]) and evalb(newsol[1]>sol[1])) then
       lprint("?????????????",sol);
       lprint("!!!!!!!!!!!!!",pol);
    fi:
Digits:=30:
st:=time():
sols:=RootFinding:-Isolate(pol,x,output='interval');
st_isoleprec:=st_isoleprec+time()-st;
Digits:=10:
od:
lprint("Newton", st_newton);
lprint("Isole", st_isole);
lprint("Isole prec", st_isoleprec);
lprint(time()-st_total);
showprofile();
**)

