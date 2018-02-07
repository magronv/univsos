##########################################################################################
##########################################################################################
# Author: Mohab Safey El Din et Ivan Bannwarth
#
# Ensemble de fonctions utiles pour isoler les coordonnees des solutions d'une
# parametrisation donnee sous forme RR. L'essentiel des fonctions fournies permet
# d'isoler des polynomes ou des fractions rationnelles en des intervalles.
#
# List of functions:
##########################################################################################
##########################################################################################
$define THRESHOLDEVAL 6



## Pour activer l'évaluation des polynômes sur un intervalle avec une
## methode de shift et découpage en fonction des signes des coeffs :
## METHODE_SHIFT = true et METHODE_FLOAT = false

## Pour activer l'évaluation des polynômes sur un intervalle avec une
## methode de shift en floatant et découpage en fonction des signes des coeffs :
## METHODE_SHIFT = false et METHODE_FLOAT = true
$define METHODE_SHIFT true
$define METHODE_FLOAT false



## Entrée : lnum est une liste de polynomes univaries en x
## Calcule une liste d'intervalles contenant subs(x=[xmin,xmax], num/den) pour rat=a 2^prec pres (arrondi superieur et inferieur) pour num dans lnum.
## Cette fonction retourne bien sur une liste de couple de valeurs.
IntervalValuesFracUnivListNum:=proc(lnum::list(polynom(integer)), den::polynom(integer),
                                    xmin, xmax, prec_in, bool_float::boolean:=false,dig::integer:=30)
local ev_num_up, var, st, ldecompose, pos2, neg2, ev_den_down, lev_den_down, ev_den_up, dec2;
local rat1, rat2, rat3, rat4, valmin, valmax, lev_num_down, lev_num_up, i , pos1, neg1;
local ev_num_down, _intervals, prec,M,num,dec,Mtmp;
local den2,_lnum,Deg:
    prec:=prec_in:
    Deg:=THRESHOLDEVAL:
    if prec=infinity and xmin<>xmax then error "precision prec=infinity";
    elif prec=infinity and xmin=xmax then prec:=max(abs(ilog2(numer(xmax))),abs(ilog2(denom(xmax))));
    fi;

    if den = 0 then error "Division by zero"; fi;

    if not(member(false,map(_d->evalb(_d<=0),map(degree,lnum)))) and degree(den)=0 then
        return map(num->[num/den,num/den],lnum);
    fi;
    if 0<xmax and 0>xmin then error "interval contains 0"; fi;

    if nops(indets([op(lnum),den]))>1 then error "polynomials not univariate "
        "polynomials";
    fi;
    var:=indets([op(lnum),den])[1]:


    st:=time():
    if xmin>=0 then
        den2:=PolynomialTools:-CoefficientVector(den,var):
        _lnum:=[seq(PolynomialTools:-CoefficientVector(pol,var),pol in lnum)]:
        if METHODE_SHIFT and not(bool_float) then
            ev_den_down,ev_den_up:=MySubsUpDownAtPosRatShiftSC(den2,xmin,xmax,prec+2,Deg):
        elif METHODE_FLOAT then
            ev_den_down,ev_den_up:=MySubsUpDownAtPosRatShiftSCEvalf(den2,xmin,xmax,prec+2,Deg):
        elif bool_float then
            ev_den_down,ev_den_up:=MySubsUpDownAtPosRatShiftSCEvalf2(den2,xmin,xmax,prec+2,Deg,dig):
        fi;
        if 0>ev_den_down and 0<ev_den_up then return map(_num->[-infinity,infinity],lnum); fi;

        lev_num_down:=[]:lev_num_up:=[]:
        for i from 1 to nops(_lnum) do
            if METHODE_SHIFT and not(bool_float) then
                ev_num_down,ev_num_up:=MySubsUpDownAtPosRatShiftSC(_lnum[i],xmin,xmax,prec+2,Deg):
            elif METHODE_FLOAT then
                ev_num_down,ev_num_up:=MySubsUpDownAtPosRatShiftSCEvalf(_lnum[i],xmin,xmax,prec+2,Deg):
            elif bool_float then
                ev_num_down,ev_num_up:=MySubsUpDownAtPosRatShiftSCEvalf2(_lnum[i],xmin,xmax,
                                                                         prec+2,Deg,dig):
            fi;
            lev_num_down:=[op(lev_num_down),ev_num_down]:
            lev_num_up:=[op(lev_num_up),ev_num_up]:
        end do;

    else
        den2:=PolynomialTools:-CoefficientVector(expand(subs(var=-var,den)),var):
        _lnum:=[seq(PolynomialTools:-CoefficientVector(expand(subs(var=-var,pol)),var),pol in lnum)]:
        if METHODE_SHIFT and not(bool_float) then
            ev_den_down,ev_den_up:=MySubsUpDownAtPosRatShiftSC(den2,-xmax,-xmin,prec+2,Deg):
        elif METHODE_FLOAT then
            ev_den_down,ev_den_up:=MySubsUpDownAtPosRatShiftSCEvalf(den2,-xmax,-xmin,prec+2,Deg):
        elif bool_float then
            ev_den_down,ev_den_up:=MySubsUpDownAtPosRatShiftSCEvalf2(den2,-xmax,-xmin,prec+2,Deg,dig):
        fi;
        if 0>ev_den_down and 0<ev_den_up then return map(_num->[-infinity,infinity],lnum); fi;

        lev_num_down:=[]:lev_num_up:=[]:
        for i from 1 to nops(_lnum) do
            if METHODE_SHIFT and not(bool_float) then
                ev_num_down,ev_num_up:=MySubsUpDownAtPosRatShiftSC(_lnum[i],-xmax,-xmin,prec+2,Deg):
            elif METHODE_FLOAT then
                ev_num_down,ev_num_up:=MySubsUpDownAtPosRatShiftSCEvalf(_lnum[i],-xmax,-xmin,
                                                                        prec+2,Deg):
            elif  bool_float then
                ev_num_down,ev_num_up:=MySubsUpDownAtPosRatShiftSCEvalf2(_lnum[i],-xmax,-xmin,
                                                                         prec+2,Deg,dig):
            fi;
            lev_num_down:=[op(lev_num_down),ev_num_down]:
            lev_num_up:=[op(lev_num_up),ev_num_up]:
        end do;
    fi;

    st:=time():
    _intervals:=[]:


    for i from 1 to nops(lev_num_down) do
        ev_num_up:=lev_num_up[i]:
        ev_num_down:=lev_num_down[i]:
        rat1:=ev_num_up/ev_den_up:
        rat2:=ev_num_up/ev_den_down:
        rat3:=ev_num_down/ev_den_up:
        rat4:=ev_num_down/ev_den_down:
        valmin,valmax:=BinaryApproximationDown(min(rat1,rat2,rat3,rat4),prec),
        BinaryApproximationUp(max(rat1,rat2,rat3,rat4),prec):
        _intervals:=[op(_intervals),[valmin,valmax]]:
    od:

    return _intervals;
end proc;



## Entree: un polynome en une variable var
## Sortie: deux polynomes: P et N a coefficients positifs
## P et N sont donnes sous la forme de vecteurs de coefficients.
## tels que pol = P-N et tous les coeffs de P et N sont positifs.
DecomposePolynomial:=proc(polvec,var)
local deg, neg, pos, lc, x, i, dim, POS, NEG;
    dim:=LinearAlgebra:-RowDimension(polvec):
    POS:=Vector(dim):
    NEG:=Vector(dim):
    for i from 1 to dim do
        if polvec[i]>0 then
            POS[i]:=polvec[i]:
        else
            NEG[i]:=-polvec[i]:
        end if;
    od:
    return [POS,NEG] ;
end proc;

## Entree: un polynome en une variable var
## Sortie: deux polynomes et deux booléens: P et N a coefficients positifs
## P et N sont donnes sous la forme de vecteurs de coefficients.
## tels que pol = P-N et tous les coeffs de P et N sont positifs.
## les deux booléens indiquent si P=0 et si N=0.
DecomposePolynomial2:=proc(polvec,var)
local deg, neg, pos, lc, x, i, dim, POS, NEG,bool1, bool2;
    dim:=LinearAlgebra:-RowDimension(polvec):
    POS:=Vector(dim):
    NEG:=Vector(dim):
    bool1:=true:
    bool2:=true:
    for i from 1 to dim do
        if polvec[i]>0 then
            POS[i]:=polvec[i]:
            if bool1=true then bool1:=false: fi;
        elif polvec[i]<0 then
            NEG[i]:=-polvec[i]:
            if bool2=true then bool2:=false: fi;
        else
            NEG[i]:=0: POS[i]:=0:
        end if;
    od:
    return [POS,NEG,bool1,bool2];
end proc;




## Calcul subs(x=rat, pol) a 2^prec pres (arrondis superieurs et inferieurs) avec pol=pos-neg.
## var est la variable
## On suppose xmin>=0
## pos et neg sont donnes sous la forme de vecteurs de coefficients
MySubsUpDownUnivPolPosNeg:=proc(pol, xmin, xmax, prec)
option inline;
    if METHODE_SHIFT then
        MySubsUpDownAtPosRatShiftSC(pol,xmin,xmax,prec,THRESHOLDEVAL):
    elif METHODE_FLOAT then
        MySubsUpDownAtPosRatShiftSCEvalf(pol,xmin,xmax,prec,THRESHOLDEVAL):
    fi;
end proc;


## On retourne subs(var=xmin, pol)
## pol est un coefficient de vecteurs
## Cette fonction est utilisée dans Newton.
MySubsUpDownAtPositiveRatSingleCoefficientVector:=proc(pol, xmid, var)
local M,dim,numerxmid,denomxmid, i,powdenomxmid,an,resmid:
    M:=0:
    dim:=LinearAlgebra:-RowDimension(pol):
    if dim=0 then return 0:
    elif dim=1 then return pol[dim]: fi;

    numerxmid:=numer(xmid):
    denomxmid:=denom(xmid):

    an:=pol[dim]:
    resmid:=numerxmid*an:
    powdenomxmid:=denomxmid:
    for i from dim-1 to 2 by -1 do
        resmid:=numerxmid*(pol[i]*powdenomxmid+resmid):
        powdenomxmid:=powdenomxmid*denomxmid:
    od;
    resmid:=pol[1]*powdenomxmid+resmid:
    return resmid/powdenomxmid:
end proc;




## ENTRÉE : pol donné sous forme de vecteur de coeff. xmin et xmax
## sont les valeurs (rationnelles) où l'on évalue le polynôme. prec
## est le nombre de bit de précision que l'on veut à la fin de calcul.
## M est la taille du plus gros coeff de pol en valeur
## absolue.

## SORTIE : évaluation de pol sur [xmin,xmax] à p bits de
## précision down pour le coté gauche et up pour le coté droit de
## l'intervalle.

## METHODE : on évalue le polynôme shifté pol(var+xmin) sur
## l'intervalle [0,xmax-xmin].
MySubsUpDownAtPosRatShiftSC:=proc(pol,xmin,xmax,prec,Deg)
local a,_lpos,_lneg,prec_k,prec_pp, ev_lpos_i, ev_lneg_i:
local ev_pos_xmin,ev_pos_xmax,ev_neg_xmin,ev_neg_xmax,k, pol_s, shift_pow;
local ev_xmin_kD,ev_xmax_kD,ev_lpos_xmin_i,ev_lpos_xmax_i,i,ev1,ev2;
local xmin_kD,xmax_kD, numxmin_pow,numxmax_pow,denxmin_pow, denxmax_pow, numxmind, numxmaxd:
local xmind, xmaxd, prec_pp2, denxmin_powkD, denxmax_powkD,ev_lneg_xmin_i,ev_lneg_xmax_i:
local ev_pos_xmin_p, ev_pos_xmax_p, ev_neg_xmax_p,ev_neg_xmin_p,prec_xpow;
local vmin,vmax,Df,test,fd, lpol,st,et,_lpol_s_denom,denomshift_pow,numershift_pow;
local shift,newmin, newmax,numermin, numermax,denommin, denommax, shiftpow;
local tmp,_lll,_lshift,_lpol_s, _lDpol_s, _lval_Dpol_s, _lbool_Dpol;
local name_in, df, ev_lpol_i,_lpol,denxmind,denxmaxd,ev_pol_xmin, ev_pol_xmax,f:
local ev_lpol_i_sorted, ev_Dpol_xmin, ev_Dpol_xmax, xmin_kD_1, xmax_kD_1, _bool_Dpol:
local st0,et0, max_dim:

    #Deg:=THRESHOLDEVAL:
    st:=time():

    shift:=xmin:
    newmin:=0: newmax:=xmax-xmin:
    numermin:=0: denommin:=1:
    numermax:=numer(newmax):
    denommax:=denom(newmax):


    st0:=time():
    ### pol_s est le polynome pol avec shift.
    pol_s:=PolynomialTools:-CoefficientVector(PolynomialTools:-Translate(
        PolynomialTools:-FromCoefficientVector(pol,x),x,shift),x):
    et0:=time()-st:
    ## Tous les vecteurs de coeff de _lpol[-1] sont de taille au plus
    ## Deg.

    ## Le code avec la version CutUnivPolySignCoeff3 ne marche pas car
    ## ne prend pas bien en compte l'impact des changements de
    ## signes.
    ## _lpol_s:=CutUnivPolySignCoeff3(pol_s,Deg): max_dim:=Deg:

    ### _lpol_s contient le découpage de pol_s en fonction des
    ### alternances de signes.
    _lpol_s:=CutUnivPolySignCoeff(pol_s):
    k:=nops(_lpol_s);
    ### max_dim contient la plus grande taille de vecteur de coeff
    ### pour savoir quels puissances précalculer.
    max_dim:=max(seq(LinearAlgebra:-RowDimension(_lpol_s[i]),i=1..k)):

    ### numxmax_pow et denxmax_pow contienne la liste des puissances
    ### du numérateur et du dénominateur de newmax=xmax-xmin.
    numxmax_pow,denxmax_pow:=ListPow(numermax,denommax,max_dim):
    if numermin=0 then
        numxmin_pow:=[1,seq(0,i=1..max_dim-1)]:
        denxmin_pow:=[seq(1,i=1..max_dim)]:
    else
        numxmin_pow,denxmin_pow:=ListPow(numermin,denommin,max_dim):
    fi;

    ##### ev_lpol_i contient l'interval d'évaluation de chaque polynôme de
    ##### _lpol_s sur [0,newxmax].
    ev_lpol_i:=IntervalValuesUnivListPolSignCoeff(_lpol_s,numxmax_pow, denxmax_pow,true);

    if k>1 then
        ##### On calcule les valeurs du polynôme pol_s en 0 et
        ##### newmax.
        ## La valeur min est donnée par l'évaluation minimale de
        ## _lpol_s[1] sur [0,newmax].
        ev_pol_xmin:=ev_lpol_i[1][1]:

        ## La valeur max est donné par la somme des valeurs max
        ## multipliée par la puissance de newmax adéquate, c'est à
        ## dire pour _lpol_s[i],
        ## newmax^(add(RowDimension(_lpol_s[l],l=1..i-1))).
        ev_pol_xmax:=ev_lpol_i[k][2]*newmax^(LinearAlgebra:-RowDimension(_lpol_s[k-1])):
        for i from k-1 to 2 by -1 do
            ev_pol_xmax:=(ev_pol_xmax+ev_lpol_i[i][2])*newmax^LinearAlgebra:-RowDimension(_lpol_s[i-1]):
        od;
        ev_pol_xmax:=ev_pol_xmax+ev_lpol_i[1][2]:
    else
        ev_pol_xmin:=ev_lpol_i[1][1]:
        ev_pol_xmax:=ev_lpol_i[1][2]:
    fi;

    ev_pol_xmin,ev_pol_xmax:=op(sort([ev_pol_xmin, ev_pol_xmax]));


    et:=time()-st:


    ev_pol_xmin, ev_pol_xmax:=BinaryApproximationDown(ev_pol_xmin,prec),
    BinaryApproximationUp(ev_pol_xmax,prec);

    return op(sort([ev_pol_xmin, ev_pol_xmax]));
end proc;


## ENTRÉE : pol donné sous forme de vecteur de coeff. xmin et xmax
## sont les valeurs (rationnelles) où l'on évalue le polynôme. prec
## est le nombre de bit de précision que l'on veut à la fin de calcul.
## M est la taille du plus gros coeff de pol en valeur
## absolue.

## SORTIE : évaluation de pol sur [xmin,xmax] à p bits de
## précision down pour le coté gauche et up pour le coté droit de
## l'intervalle.

## METHODE : on évalue le polynôme shifté pol(var+evalf(xmin)) sur
## l'intervalle [0, xmax-xmin].
MySubsUpDownAtPosRatShiftSCEvalf:=proc(pol,xmin,xmax,prec,Deg)
local test, stm, pol_s_m, etm, _l1,_ll1, stp,pol_s_p, etp,_l2,_ll2:
    Digits:=30:
    test:=true:
    while test do
        Rounding:=-infinity:
        stm:=time():
        pol_s_m:=PolynomialTools:-CoefficientVector(PolynomialTools:-Translate(
            PolynomialTools:-FromCoefficientVector(pol,x),x,evalf(xmin)),x):
        etm:=time()-stm:

        _l1:=MySubsUpDownAtPositiveRatEvalf(pol_s_m, xmin-xmax,prec,Deg):
        _ll1:=BinaryApproximationDown(convert(_l1[1],rational,exact),prec):
        Rounding:=infinity:
        stp:=time():
        pol_s_p:=PolynomialTools:-CoefficientVector(PolynomialTools:-Translate(
            PolynomialTools:-FromCoefficientVector(pol,x),x,evalf(xmin)),x):
        etp:=time()-stp:

        _l2:=MySubsUpDownAtPositiveRatEvalf(pol_s_p, xmin-xmax,prec,Deg):
        _ll2:=BinaryApproximationUp(convert(_l2[2],rational,exact),prec):
        test:=evalb(_ll1<0 and _ll2>0):
        if test then print(evalf([_ll1,_ll2],2),Digits,etm,etp); else print(etm,etp); fi;

        if test then Digits:=Digits*2: fi;
    od;
    return _ll1,_ll2;
end proc;

MySubsUpDownAtPosRatShiftSCEvalf2:=proc(pol,xmin,xmax,prec,Deg,digits)
local test, stm, pol_s_m, etm, _l1,_ll1, stp,pol_s_p, etp,_l2,_ll2, Digits_avant:
    Digits_avant:=Digits:
    Digits:=digits:

    Rounding:=-infinity:
    stm:=time():
    pol_s_m:=PolynomialTools:-CoefficientVector(PolynomialTools:-Translate(
        PolynomialTools:-FromCoefficientVector(pol,x),x,evalf(xmin)),x):
    etm:=time()-stm:

    _l1:=MySubsUpDownAtPositiveRatEvalf(pol_s_m, xmin-xmax,prec,Deg):
    _ll1:=BinaryApproximationDown(convert(_l1[1],rational,exact),prec):
    #_ll11:=BinaryApproximationDown(convert(_l1[1],rational,exact),prec):
    #_ll12:=BinaryApproximationUp(convert(_l1[2],rational,exact),prec):

    Rounding:=infinity:
    stp:=time():
    pol_s_p:=PolynomialTools:-CoefficientVector(PolynomialTools:-Translate(
        PolynomialTools:-FromCoefficientVector(pol,x),x,evalf(xmin)),x):
    etp:=time()-stp:

    _l2:=MySubsUpDownAtPositiveRatEvalf(pol_s_p, xmin-xmax,prec,Deg):
    _ll2:=BinaryApproximationUp(convert(_l2[2],rational,exact),prec):
    #_ll21:=BinaryApproximationDown(convert(_l2[1],rational,exact),prec):
    #_ll22:=BinaryApproximationUp(convert(_l2[2],rational,exact),prec):

    Digits:=Digits_avant:
    #if _ll1>_ll2 then printf("%%%%%%%%%%%"); fi;

    #_ll1:=min(_ll11,_ll12,_ll21,_ll22):
    #_ll2:=max(_ll11,_ll12,_ll21,_ll22):

    return _ll1,_ll2;
end proc;


MySubsUpDownAtPositiveRatEvalf:=proc(pol,val,prec,Deg)
local _lpol_s, k, max_dim, numerval, denomval, numval_pow,denval_pow:
local ev_lpol_i, ev_pol_min, ev_pol_max,i,et:

    _lpol_s:=CutUnivPolySignCoeff(pol):
    k:=nops(_lpol_s);
    ### max_dim contient la plus grande taille de vecteur de coeff
    ### pour savoir quels puissances précalculer.
    max_dim:=max(seq(LinearAlgebra:-RowDimension(_lpol_s[i]),i=1..k)):
    #print("k",k,"max_dim", max_dim, "degree(pol)", LinearAlgebra:-RowDimension(pol_s), "time0", et0);
    numerval:=numer(val):
    denomval:=denom(val):
    ### numxmax_pow et denxmax_pow contienne la liste des puissances
    ### du numérateur et du dénominateur de newmax=xmax-xmin.
    numval_pow,denval_pow:=ListPow(numerval,denomval,max_dim):

    ##### ev_lpol_i contient l'interval d'évaluation de chaque polynôme de
    ##### _lpol_s sur [0,newxmax].
    ev_lpol_i:=IntervalValuesUnivListPolSignCoeff(_lpol_s,numval_pow, denval_pow,true);

    if k>1 then
        ##### On calcule les valeurs du polynôme pol_s en 0 et
        ##### newmax.
        ## La valeur min est donnée par l'évaluation minimale de
        ## _lpol_s[1] sur [0,newmax].
        ev_pol_min:=ev_lpol_i[1][1]:

        ## La valeur max est donné par la somme des valeurs max
        ## multipliée par la puissance de newmax adéquate, c'est à
        ## dire pour _lpol_s[i],
        ## newmax^(add(RowDimension(_lpol_s[l],l=1..i-1))).
        ev_pol_max:=ev_lpol_i[k][2]*val^(LinearAlgebra:-RowDimension(_lpol_s[k-1])):
        for i from k-1 to 2 by -1 do
            ev_pol_max:=(ev_pol_max+ev_lpol_i[i][2])*val^LinearAlgebra:-RowDimension(_lpol_s[i-1]):
        od;
        ev_pol_max:=ev_pol_max+ev_lpol_i[1][2]:
    else
        ev_pol_min:=ev_lpol_i[1][1]:
        ev_pol_max:=ev_lpol_i[1][2]:
    fi;

    ev_pol_min,ev_pol_max:=op(sort([ev_pol_min, ev_pol_max]));


    et:=time()-st:

    return ev_pol_min, ev_pol_max:

end proc;







## Input : a,b des rationnels de la forme int/2^p, int'/2^q.

## Output : triplet [c,d,e] tel que a=c/e et b=d/e.
SameDenom:=proc(a,b)
local ad, an,bd,bn:
    ad:=denom(a): bd:=denom(b):
    an:=numer(a): bn:=numer(b):
    if ad=bd then return an,bn,ad: fi;

    if ad>bd then
        return an, bn*(iquo(ad,bd)), ad:
    else
        return an*(iquo(bd,ad)), bn, bd:
    fi;
end proc:






## xmin, xmax des entiers, sortie : [1,xmin, xmin^2,...,xmin^(d-1)]
## [1,xmax, xmax^2,...,xmin^(d-1)]:
ListPow:=proc(xmin, xmax,d)
local lmin, lmax,i:
    if d=0 or d=1 then return [1],[1]:
    else
        lmin:=[1]: lmax:=[1]:
        if xmin=xmax or xmax=0 then
            for i from 1 to d-1 do
                lmin:=[op(lmin), lmin[-1]*xmin]:
            od;
            if xmax=0 then return lmin,[]: fi:
            lmax:=lmin:
        else
            for i from 1 to d-1 do
                lmin:=[op(lmin), lmin[-1]*xmin]:
                lmax:=[op(lmax), lmax[-1]*xmax]:
            od;
        fi;
        return lmin,lmax:
    fi;
end proc:



## Prend en entree un polynome pol et renvoie _l tq pol=add(_l[i]*X^i,
## 1..nops(_l)) et chaque _l[i] est de degré au plus d.
CutUnivPoly:=proc(pol,d)
local V,dim,k,_l;
#lprint("Cut in", PolynomialTools:-FromCoefficientVector(pol,t));
#print(evalm(pol));
    V:=pol:
    dim:=LinearAlgebra:-RowDimension(V):
    k:=iquo(dim,d,'r'):
    _l:=[seq(V[i*d+1..(i+1)*d], i=0..k-1)]:
    if r=0 then
        return _l,nops(_l);
    else
        return [op(_l), V[k*d+1..-1]],nops(_l)+1:
    fi;
end proc;

## Prend en entree un polynome pol et renvoie _l tq pol=add(_l[i]*X^i,
## 1..nops(_l)) et chaque _l[i] est de degré au plus d.
CutUnivPoly2:=proc(pol,d)
local V,dim,k,_l;
#lprint("Cut in", PolynomialTools:-FromCoefficientVector(pol,t));
#print(evalm(pol));
    V:=pol:
    dim:=LinearAlgebra:-RowDimension(V):
    k:=iquo(dim,d,'r'):
    _l:=[seq(V[i*d+1..(i+1)*d], i=0..k-1)]:
    if r=0 then
        return _l,nops(_l);
    else
        return [op(_l), Vector(d,V[k*d+1..-1])],nops(_l)+1:
    fi;
end proc;

## Prend en entree un polynome pol et renvoie _l tq
## pol=add(_l[i]*X^add(dim(_l[r]),r=1..i-1)), 1..nops(_l)) et chaque
## _l[i] a des coeff de signe constant.
CutUnivPolySignCoeff:=proc(pol)
local V,dim,i,_l,current,pos_bool;
    V:=pol:
    dim:=LinearAlgebra:-RowDimension(V):
    pos_bool:=evalb(V[1]>=0):
    _l:=[]:
    current:=[]:
    i:=1:
    while i<=dim do
        if V[i]=0 then
            current:=[op(current),0]:
        elif pos_bool and V[i]>0 then
            current:=[op(current), V[i]]:
        elif pos_bool and V[i]<0 then
            if current<>[] then
                _l:=[op(_l), Vector(current)]:
            fi;
            current:=[V[i]]:
            pos_bool:=false:
        elif not(pos_bool) and V[i]<0 then
            current:=[op(current),V[i]]:
        elif not(pos_bool) and V[i]>0 then
            if current<>[] then
                _l:=[op(_l),Vector(current)]:
            fi;
            current:=[V[i]]:
            pos_bool:=true;
        else
            lprint(pol,d):
            error "case missing?";
        fi;
        if i=dim and current<>[] then
            _l:=[op(_l),Vector(current)]:
        fi;
        i:=i+1;
    od:
    return _l:
end proc;


## Prend en entree un polynome pol et renvoie _l tq pol=add(_l[i]*X^dim(_l[i]),
## 1..nops(_l)) et chaque _l[i] a des coeff de signe constant et est
## de degré max d.
CutUnivPolySignCoeff3:=proc(pol,d)
local V,dim,i,_l,current,pos_bool;
    V:=pol:
    dim:=LinearAlgebra:-RowDimension(V):
    pos_bool:=evalb(V[1]>=0):
    _l:=[]:
    current:=[]:
    i:=1:
    while i<=dim do
        if V[i]=0 then
            current:=[op(current),0]:
        elif pos_bool and V[i]>0 then
            if nops(current)<d-1 then
                current:=[op(current), V[i]]:
            elif nops(current)=d-1 then
                _l:=[op(_l),Vector([op(current),V[i]])]:
                current:=[];
            fi;
        elif pos_bool and V[i]<0 then
            if current<>[] then
                _l:=[op(_l), Vector(current)]:
            fi;
            current:=[V[i]]:
            pos_bool:=false:
        elif not(pos_bool) and V[i]<0 then
            if nops(current)<d-1 then
                current:=[op(current),V[i]]:
            elif nops(current)=d-1 then
                _l:=[op(_l),Vector([op(current),V[i]])]:
                current:=[]:
            fi;
        elif not(pos_bool) and V[i]>0 then
            if current<>[] then
                _l:=[op(_l),Vector(current)]:
            fi;
            current:=[V[i]]:
            pos_bool:=true;
        else
            lprint(pol,d):
            error "case missing?";
        fi;
        if i=dim and current<>[] then
            _l:=[op(_l),Vector(current)]:
        fi;
        i:=i+1;
    od:
    return _l:
end proc;


## ENTREE : liste de polynomes données sous forme de vecteurs de
## coefficients. liste des puissances du numérateurs, liste des
## puissances du dénominateur. bool un booléen.

## ASSUME : les polynômes dans lpol ont un degré < THRESHOLDEVAL

## SORTIE : liste des évaluation
## Si bool=true alors on
## évalue le polynôme en force brute [pos(0)-neg(num/den),
## pos(num/den)-pos(0)]:
IntervalValuesUnivListPolOLD:=proc(lpol, listpownum, listpowden)
local i, lres, pos,neg,evposmin,evposmax,evnegmin,evnegmax,dim:
    lres:=[];
    for i from 1 to nops(lpol) do
        dim:=LinearAlgebra:-RowDimension(lpol[i]):
        if dim=0 then lres:=[op(lres), [0,0]]:
        else
            pos,neg:=op(DecomposePolynomial(lpol[i])):

            evposmax:=add(pos[i]*listpownum[i]*listpowden[dim-i+1],i=1..dim)/listpowden[dim]:
            evnegmax:=add(neg[i]*listpownum[i]*listpowden[dim-i+1],i=1..dim)/listpowden[dim]:
            if lpol[i][1]>0 then
                evposmin:=lpol[i][1]: evnegmin:=0:
            else
                evposmin:=0: evnegmin:=lpol[i][1]:
            fi;
            lres:=[op(lres), [evposmin-evnegmax, evposmax-evnegmin]]:
        fi;
    od;
    return lres:
end proc;




## ENTREE : liste de polynomes données sous forme de vecteurs de
## coefficients. liste des puissances du numérateurs, liste des
## puissances du dénominateur. bool un booléen.

## ASSUME : les polynômes dans lpol ont un degré < THRESHOLDEVAL

## SORTIE : liste des évaluation
## Si bool=true alors on
## évalue le polynôme en force brute [pos(0)-neg(num/den),
## pos(num/den)-pos(0)]:
IntervalValuesUnivListPol2:=proc(lpol, listpownum, listpowden,bool::boolean:=false)
local i,k, lres, pos,neg,evposmin,evposmax,evnegmin,evnegmax,dim,evpolmax,_ll:
    lres:=[];
    dim:=LinearAlgebra:-RowDimension(lpol[1]):
    _ll:=[seq(listpownum[i]*listpowden[dim-i+1], i=1..dim)]:
    for k from 1 to nops(lpol) do
        if dim=0 then lres:=[op(lres), [0,0]]:
        else
            if bool=false then
                pos,neg:=op(DecomposePolynomial(lpol[k])):
                if not(member(false, map(j-> evalb(pos[j]=0), [seq(1..dim)]))) then
                    evnegmax:=add(neg[i]*_ll[i],i=1..dim)/listpowden[dim]:
                    evnegmin:=abs(lpol[k][1]):
                    #lres:=[op(lres), [-evnegmin, -evnegmax]]:
                    lres:=[op(lres), [-evnegmax, -evnegmin]]:
                elif not(member(false, map(j-> evalb(neg[j]=0), [seq(1..dim)]))) then
                    evposmax:=add(pos[i]*_ll[i],i=1..dim)/listpowden[dim]:
                    evposmin:=abs(lpol[k][1]):
                    lres:=[op(lres), [evposmin, evposmax]]:
                else
                    evposmax:=add(pos[i]*_ll[i],i=1..dim)/listpowden[dim]:
                    evnegmax:=add(neg[i]*_ll[i],i=1..dim)/listpowden[dim]:
                    if lpol[k][1]>0 then
                        evposmin:=abs(lpol[k][1]): evnegmin:=0:
                    else
                        evposmin:=0: evnegmin:=abs(lpol[k][1]):
                    fi;
                    lres:=[op(lres), [evposmin-evnegmax, evposmax-evnegmin]]:

                fi;
            else
                evpolmax:=add(lpol[k][i]*_ll[i],i=1..dim)/listpowden[dim]:
                #lres:=[op(lres), [lpol[k][1],evpolmax]]:
                lres:=[op(lres), sort([lpol[k][1],evpolmax])]:
            fi;
        fi;
    od;
    return lres:
end proc;


IntervalValuesUnivListPol3:=proc(lpol, listpownum, listpowden,
                                 _lbool::list(boolean):=[],
                                 _bool::boolean:=false)
local i,k, lres, pos,neg,evposmin,evposmax,evnegmin,evnegmax,dim,evpolmax,_l:
    lres:=[];
    ## Tous les polynômes ont la même taille.
    dim:=LinearAlgebra:-RowDimension(lpol[1]):
    _l:=[seq(listpownum[i]*listpowden[dim-i+1],i=1..dim)]:
    for k from 1 to nops(lpol) do
        if dim=0 then lres:=[op(lres), [0,0]]:
        else
            if _lbool[k]=false then
                pos,neg:=op(DecomposePolynomial(lpol[k])):
                if not(member(false, map(j-> evalb(pos[j]=0), [seq(1..dim)]))) then
                    evnegmax:=add(neg[i]*_l[i],i=1..dim)/listpowden[dim]:
                    evnegmin:=abs(lpol[k][1]):
                    #lres:=[op(lres), [-evnegmin, -evnegmax]]:
                    lres:=[op(lres), [-evnegmax, -evnegmin]]:
                elif not(member(false, map(j-> evalb(neg[j]=0), [seq(1..dim)]))) then
                    evposmax:=add(pos[i]*_l[i],i=1..dim)/listpowden[dim]:
                    evposmin:=abs(lpol[k][1]):
                    lres:=[op(lres), [evposmin, evposmax]]:
                else
                    evposmax:=add(pos[i]*_l[i],i=1..dim)/listpowden[dim]:
                    evnegmax:=add(neg[i]*_l[i],i=1..dim)/listpowden[dim]:
                    if lpol[k][1]>0 then
                        evposmin:=abs(lpol[k][1]): evnegmin:=0:
                    else
                        evposmin:=0: evnegmin:=abs(lpol[k][1]):
                    fi;
                    lres:=[op(lres), [evposmin-evnegmax, evposmax-evnegmin]]:

                fi;
            else
                evpolmax:=add(lpol[k][i]*_l[i],i=1..dim)/listpowden[dim]:

                if _bool then
                    lres:=[op(lres), [lpol[k][1],evpolmax]]:
                else
                    #printf("(ici)");
                    lres:=[op(lres), sort([lpol[k][1],evpolmax])]:
                fi;
            fi;
        fi;
    od;
    return lres:
end proc;


IntervalValuesUnivListPolSignCoeff:=proc(lpol, listpownum, listpowden, _bool::boolean:=false)
local i,k, lres, pos,neg,evposmin,evposmax,evnegmin,evnegmax,dim,evpolmax,bool1,bool2:
local bool_sort:
    lres:=[];
    ## Tous les polynômes ont la même taille.
    for k from 1 to nops(lpol) do
        dim:=LinearAlgebra:-RowDimension(lpol[k]);

        if dim=0 then lres:=[op(lres), [0,0]];
        else
            #if _bool=false then
            #pos,neg:=op(DecomposePolynomial(lpol[k]));
            ## bool1 indique que pos=0 et bool2 indique si neg=0.
            pos,neg,bool1,bool2:=op(DecomposePolynomial2(lpol[k]));
            if bool1 then
                evnegmax:=add(neg[i]*listpownum[i]*listpowden[dim-i+1],i=1..dim)/listpowden[dim];
                evnegmin:=abs(lpol[k][1]);

                lres:=[op(lres), sort([-evnegmax, -evnegmin])];

            elif bool2 then
                evposmax:=add(pos[i]*listpownum[i]*listpowden[dim-i+1],i=1..dim)/listpowden[dim];
                evposmin:=abs(lpol[k][1]);

                lres:=[op(lres), sort([evposmin, evposmax])];

            else
                print("ici ????");
                evposmax:=add(pos[i]*listpownum[i]*listpowden[dim-i+1],i=1..dim)/listpowden[dim];
                evnegmax:=add(neg[i]*listpownum[i]*listpowden[dim-i+1],i=1..dim)/listpowden[dim];
                if lpol[k][1]>0 then
                    evposmin:=abs(lpol[k][1]); evnegmin:=0;
                else
                    evposmin:=0; evnegmin:=abs(lpol[k][1]);
                fi;

                lres:=[op(lres), sort([evposmin-evnegmax, evposmax-evnegmin])];
            fi;
        fi;
    od;
    return lres;
end proc;



######################################################################
######################################################################
# Approximation binaire
######################################################################
######################################################################


#Calcule une approximation binaire inf de rat (a 2^prec)
BinaryApproximationDown:=proc(rat, prec) option inline; floor((rat*2^prec))/(2^prec):end proc;

#Calcule une approximation binaire sup de rat (a 2^prec)
BinaryApproximationUp:=proc(rat, prec) option inline; ceil((rat*2^prec))/(2^prec);end proc;

BinaryApproximationUpDown:=proc(rat, prec) option inline; floor((rat*2^prec))/(2^prec),ceil((rat*2^prec))/(2^prec); end proc:


##############################################################################################
##############################################################################################
# Evaluation d'un polynome sur un intervalle
##############################################################################################
##############################################################################################

## pol est un polynome en plusieurs variables x1, ..., xn
## _point est un point donne par [xi=[a1,b1], i=1...N] (avec N>=n]
## Cette fonction renvoie une boite contenant toutes les valeurs
## atteintes par pol en la boite definie par _point qui donne
## sous la forme xi=[ai,bi]

## HYPOTHESE: La boite definie par _point n'intersecte transversalement
## aucun axe de coordonnee !
MultivariateIntervalEvaluationOld:=proc(pol, _point)
local _single, _vars, i, pos, neg, newpol, den, _newpoint;

    den:=denom(pol):
    if den>0 then
        newpol:=expand(numer(pol)):
    else
        newpol:=expand(numer(-pol)):
        den:=-den:
    end if;
    _single:=map(_p->sign(rhs(_p)[1]),_point);
    _vars:=map(_p->indets(_p)[1],_point);
    _newpoint:=[]:

    for i from 1 to nops(_single) do
        if _single[i]>0 then
            _newpoint:=[op(_newpoint), _point[i]]:
        else
            _newpoint:=[op(_newpoint), lhs(_point[i])=[-rhs(_point[i])[2], -rhs(_point[i])[1]]]:
            newpol:=expand(subs(_vars[i]=-_vars[i], newpol)):
        end if;
    end do;

    pos, neg:=DecomposeMultivariatePolynomial(expand(newpol));

    if pos - neg <> newpol then error "Bug in decomposition of multivariate polynomials"; fi;

    return map(_e->_e/den, MultivariateIntervalEvaluationAtNonNegativePoint(pos, neg, _newpoint));
end proc:

## pol est un polynome en plusieurs variables x1, ..., xn
## _point est un point donne par [xi=[a1,b1], i=1...N] (avec N>=n]
## Cette fonction renvoie une boite contenant toutes les valeurs
## atteintes par pol en la boite definie par _point qui donne
## sous la forme xi=[ai,bi]

## HYPOTHESE: La boite definie par _point n'intersecte transversalement
## aucun axe de coordonnee !
MultivariateIntervalEvaluation:=proc(pol, _point)
local _single, _vars, i, pos, neg, newpol, den, _newpoint;
local newpol_shift, res, _newpoint_shift:
    den:=denom(pol):
    if den>0 then
        newpol:=expand(numer(pol)):
    else
        newpol:=expand(numer(-pol)):
        den:=-den:
    end if;
    _single:=map(_p->sign(rhs(_p)[1]),_point);
    _vars:=map(_p->indets(_p)[1],_point);
    _newpoint:=[]:

    for i from 1 to nops(_single) do
        if _single[i]>0 then
            _newpoint:=[op(_newpoint), _point[i]]:
        else
            _newpoint:=[op(_newpoint), lhs(_point[i])=[-rhs(_point[i])[2], -rhs(_point[i])[1]]]:
            newpol:=expand(subs(_vars[i]=-_vars[i], newpol)):
        end if;
    end do;

    ## ici, on cherche à évaluer newpol sur un pavé _newpoint inclus
    ## dans R_>0^n.

    newpol_shift:=newpol:
    for i from 1 to nops(_vars) do
        newpol_shift:=PolynomialTools:-Translate(newpol_shift,_vars[i],rhs(_newpoint[i])[1]):
    od;
    newpol_shift:=expand(newpol_shift):

    _newpoint_shift:=map(_p->rhs(_p)[2]-rhs(_p)[1], _newpoint):
    ## _newpoint_shift est le pavé shifté en 0 pour le coin min.
    res:=[MultivariateIntervalEvaluationAtNonNegativePointShift2(newpol_shift,_vars, _newpoint_shift)]:

    return map(_e->_e/den, res);
end:

## pol est un polynome en plusieurs variables x1, ..., xn
## _point est un point donne par [xi=[a1,b1], i=1...N] (avec N>=n]
## Cette fonction renvoie une boite contenant toutes les valeurs
## atteintes par pol en la boite definie par _point qui donne
## sous la forme xi=[ai,bi]

## bool est un booléen et digits un entier

## HYPOTHESE: La boite definie par _point n'intersecte transversalement
## aucun axe de coordonnee !
MultivariateIntervalEvaluationEvalf:=proc(pol, _point,bool, digits::integer:=30)
local den, newpol, _single, _vars, _newpoint, i, Digits_avant;
local Rounding_avant, newpol_shift, _newpoint_shift, res;
    den:=denom(pol):
    if den>0 then
        newpol:=expand(numer(pol)):
    else
        newpol:=expand(numer(-pol)):
        den:=-den:
    end if;
    _single:=map(_p->sign(rhs(_p)[1]),_point);
    _vars:=map(_p->indets(_p)[1],_point);
    _newpoint:=[]:

    for i from 1 to nops(_single) do
        if _single[i]>0 then
            _newpoint:=[op(_newpoint), _point[i]]:
        else
            _newpoint:=[op(_newpoint), lhs(_point[i])=[-rhs(_point[i])[2], -rhs(_point[i])[1]]]:
            newpol:=expand(subs(_vars[i]=-_vars[i], newpol)):
        end if;
    end do;

    ## ici, on cherche à évaluer newpol sur un pavé _newpoint inclus
    ## dans R_>0^n.
    Digits_avant:=Digits:
    Digits:=digits:
    Rounding_avant:=Rounding:
    if bool then
        Rounding:=-infinity:
    else
        Rounding:=+infinity:
    fi;
    newpol_shift:=newpol:
    #lprint("Digits=", Digits);
    for i from 1 to nops(_vars) do
        newpol_shift:=PolynomialTools:-Translate(newpol_shift,_vars[i],evalf(rhs(_newpoint[i])[1])):
    od;
    newpol_shift:=expand(newpol_shift):

    _newpoint_shift:=map(_p->rhs(_p)[2]-rhs(_p)[1], _newpoint):
    ## _newpoint_shift est le pavé shifté en 0 pour le coin min.
    res:=[MultivariateIntervalEvaluationAtNonNegativePointShift2(newpol_shift,_vars, _newpoint_shift)]:
    Digits:=Digits_avant:
    Rounding:=Rounding_avant:
    return map(_e->_e/den, res);
end:


#### ENTREE : pol : polynôme bivarié, _vars les variables de pol,
#### _point : liste de rationnels.

#### SORTIE : intervalle d'approximation de l'évaluation de pol sur le
#### pavé [0,_point[1]]x...x[0,_point[-1]]
BivariateIntervalEvaluationAtNonNegativePointShift:=proc(pol, _vars,_point)
local coeff_x, r, tmp0,tmp, c_i, val_pol_c_i, val0_lpol, valmax_lpol:
local _lpol1, val_lpol1, val0_lpol1, valmax_lpol1, val11,val12:
local _lpol2, val_lpol2, val0_lpol2, valmax_lpol2, val21,val22:
local i,j:
#lprint(_point);
    #printf("{%d}",degree(pol));
    coeff_x:=PolynomialTools:-CoefficientVector(pol,_vars[1]):

    r:=[]:
    for i from 1 to degree(pol)+1 do
        tmp0:=PolynomialTools:-CoefficientVector(coeff_x[i],_vars[2]);
        tmp:=CutUnivPolySignCoeff(tmp0):
        c_i:=map(e->PolynomialTools:-FromCoefficientVector(e,_vars[2]),tmp):

        val_pol_c_i:=map(e-> sort([subs(_vars[2]=0,e),subs(_vars[2]=_point[2],e)]), c_i):

        val0_lpol:=val_pol_c_i[1][1]:

        valmax_lpol:=val_pol_c_i[-1][2];
        for j from nops(c_i)-1 to 1 by -1 do
            valmax_lpol:=valmax_lpol*_point[2]^(degree(c_i[j])+1)+val_pol_c_i[j][2]:
        od;

        r:=[op(r), sort([val0_lpol, valmax_lpol])]:
    od:
    ## r est la liste des valeurs min et max des coefficients en x^i
    ## de pol en [0,_point[2]]


    ## on considère maintenant le polynôme en x avec comme coefficient
    ## les plus petites valeurs des coeff de x^i sur [0,_point[2]]
    _lpol1:=map(e->PolynomialTools:-FromCoefficientVector(e,_vars[1]),
                CutUnivPolySignCoeff(Vector(map(e-> e[1], r)))):
    val_lpol1:=map(e-> sort([subs(_vars[1]=0,e),subs(_vars[1]=_point[1],e)]), _lpol1):

    val0_lpol1:=val_lpol1[1][1]:

    valmax_lpol1:=val_lpol1[-1][2];
    for j from nops(_lpol1)-1 to 1 by -1 do
        valmax_lpol1:=valmax_lpol1*_point[1]^(degree(_lpol1[j])+1)+val_lpol1[j][2]:
    od;

    val11,val12:=op(sort([val0_lpol1, valmax_lpol1])):


    ## on considère maintenant le polynôme en x avec comme coefficient
    ## les plus grandes valeurs des coeff de x^i sur [0,_point[2]]
    _lpol2:=map(e->PolynomialTools:-FromCoefficientVector(e,_vars[1]),
                CutUnivPolySignCoeff(Vector(map(e-> e[2], r)))):
    val_lpol2:=map(e-> sort([subs(_vars[1]=0,e),subs(_vars[1]=_point[1],e)]), _lpol2):
    val0_lpol2:=val_lpol2[1][1]:

    valmax_lpol2:=val_lpol2[-1][2];
    for j from nops(_lpol2)-1 to 1 by -1 do
        valmax_lpol2:=valmax_lpol2*_point[1]^(degree(_lpol2[j])+1)+val_lpol2[j][2]:
    od;

    val21,val22:=op(sort([val0_lpol2, valmax_lpol2])):


    return min(val11,val12,val21,val22), max(val11,val12,val21,val22);
end proc:

#### ENTREE : pol : polynôme multivarié, _vars les variables de pol,
#### _point : liste de rationnels.

#### SORTIE : intervalle d'approximation de l'évaluation de pol sur le
#### pavé [0,_point[1]]x...x[0,_point[-1]]
MultivariateIntervalEvaluationAtNonNegativePointShift2:=proc(pol, _vars,_point)
local monom_x1_xn, r, max_dim, current, signval, i, monom;
local val_min, val_max, val_0_r_i, val_max_r_i, vmin, vmax;

    monom_x1_xn:=[seq(op(i,pol),i=1..nops([coeffs(pol)]))]:

    r:=[]: max_dim:=0:
    current:=monom_x1_xn[1]:
    signval:=sign(coeffs(monom_x1_xn[1])):

    for i from 2 to nops(monom_x1_xn) do
        monom:=monom_x1_xn[i]:
        if sign(coeffs(monom))*signval>0 then
            current:=current+monom:
            max_dim:=max(max_dim, degree(monom)):
        else
            if current<>0 then
                r:=[op(r), current]:
            fi;
            current:=monom_x1_xn[i]:
            signval:=sign(coeffs(current)):
        fi;
        if i=nops(monom_x1_xn) then
            r:=[op(r), current]:
            current:='current':
        fi;
    od;
    if not(type(current,symbol)) then
        r:=[op(r), current]:
    fi;

    val_min:=0:
    val_max:=0:
    #print(nops(r));
    #print(Rounding);
    for i from 1 to nops(r) do
        val_0_r_i:=subs([seq(_vars[j]=0,j=1..nops(_vars))],r[i]):
        val_max_r_i:=subs([seq(_vars[j]=_point[j],j=1..nops(_vars))],r[i]):
        val_max_r_i:=eval(r[i],[seq(_vars[j]=_point[j],j=1..nops(_vars))]):
        vmin,vmax:=op(sort([val_0_r_i,val_max_r_i])):
        val_min:=val_min+vmin:
        val_max:=val_max+vmax:
    od:

    return val_min, val_max:
end proc:

#### ENTREE : pol : polynôme multivarié, _vars les variables de pol,
#### _point : liste de rationnels.

#### SORTIE : intervalle d'approximation de l'évaluation de pol sur le
#### pavé [0,_point[1]]x...x[0,_point[-1]]
MultivariateIntervalEvaluationAtNonNegativePointShift2NEW:=proc(pol, _vars,_point)
local monom_x1_xn, r, max_dim, current, signval, i, monom;
local list_point_pow, val_min, val_max, val_0_r_i, val_max_r_i, vmin, vmax;

    monom_x1_xn:=[seq(op(i,pol),i=1..nops([coeffs(pol)]))]:

    r:=[]: max_dim:=0:
    current:=[monom_x1_xn[1]]:
    signval:=sign(coeffs(monom_x1_xn[1])):

    for i from 2 to nops(monom_x1_xn) do
        monom:=monom_x1_xn[i]:
        if sign(coeffs(monom))*signval>0 then
            #current:=current+monom:
            current:=[op(current),monom]:
            max_dim:=max(max_dim, degree(monom)):
        else
            if current<>[] then
                r:=[op(r), current]:
            fi;
            #current:=monom_x1_xn[i]:
            current:=[monom_x1_xn[i]]:
            signval:=sign(coeffs(current[1])):
        fi;
        if i=nops(monom_x1_xn) then
            r:=[op(r), current]:
            current:='current':
        fi;
    od;
    if not(type(current,symbol)) then
        r:=[op(r), current]:
    fi;

    list_point_pow:=ListPowMultivar(_point, max_dim):

    val_min:=0:
    val_max:=0:
    #print(nops(r));
    for i from 1 to nops(r) do
        val_0_r_i:=add(e, e in subs([seq(_vars[j]=0,j=1..nops(_vars))],r[i])):
        #val_max_r_i:=subs([seq(_vars[j]=_point[j],j=1..nops(_vars))],r[i]):
        val_max_r_i:=EvalMultiPol(r[i], list_point_pow,_vars);
        vmin,vmax:=op(sort([val_0_r_i,val_max_r_i])):
        val_min:=val_min+vmin:
        val_max:=val_max+vmax:
    od:

    return val_min, val_max:
end proc:

## ENTREE : _lmonom : liste de monom de même signes, list_point_pow :
## nops(_points)-uplet : [[1,....,1], [_point[1],...,_point[-1]], ...,
## [_point[1]^deg, ..., _point[-1]^deg]], _vars : liste des variables.

## Sortie : évaluation du polynôme défini par la liste des monomes
## grâce aux précalculs des puissances des valeurs à substituer.
EvalMultiPol:=proc(_lmonom, list_point_pow,_vars)
local res, monom;
    res:=0:
    for monom in _lmonom do
        res:=res+coeffs(monom)*mul(list_point_pow[degree(monom,_vars[i])+1][i],i=1..nops(_vars)):
    od;
    return res:
end proc:


## ENTREE : _point est une liste de rationnels, deg un entier

## SORTIE : liste nops(_points)-uplet : [[1,....,1],
## [_point[1],...,_point[-1]], ..., [_point[1]^deg, ..., _point[-1]^deg]].
ListPowMultivar:=proc(_point, deg)
local nvars, res,j;
    nvars:=nops(_point):
    res:=[[seq(1,j=1..nvars)]]:
    if deg=0 then return res fi:

    for j from 2 to deg+1 do
        res:=[op(res), [seq(res[j-1][i]*_point[i],i=1..nvars)]]:
    od;
    return res:
end proc:



MultivariateIntervalEvaluationAtNonNegativePoint:=proc(pos, neg, _point)
local valmin_pos, valmax_pos, valmin_neg, valmax_neg, valmin, valmax, _lmin, _lmax:
#lprint(_point);

    _lmin:=map(_p->lhs(_p)=rhs(_p)[1], _point);
    _lmax:=map(_p->lhs(_p)=rhs(_p)[2], _point);

    valmin_pos:=subs(_lmin, pos):
    valmax_pos:=subs(_lmax, pos):
    valmin_neg:=subs(_lmin, neg):
    valmax_neg:=subs(_lmax, neg):

    valmin:=valmin_pos-valmax_neg;
    valmax:=valmax_pos-valmin_neg;
    if valmin>valmax then
        lprint(pos, neg, _point);
        error "Bug in MultivariateIntervalEvaluationAtNonNegativePoint";
    fi;
    return [valmin, valmax];
end proc:

# Entree : un polynome pol
# Sortie : deux polynomes a coefficients positifs pos et neg tels que pol = pos-neg;
DecomposeMultivariatePolynomial:=proc(pol)
local deg, neg, pos, lc, x, i, _eps, newpol;

    pos:=0: neg:=0:
    newpol:=pol+_eps:
    for i from 1 to nops(newpol) do
        if coeffs(op(i,newpol))>0 then
            pos:=pos+op(i,newpol):
        else
            neg:=neg-op(i,newpol);
        end if;
    end do;

    return subs(_eps=0, pos), subs(_eps=0, neg);

end proc;
