default(realprecision,100);

myround(p, i) =  round(2^i*p)/2^i;
gpsquares(r, x, k) = 
{
  a = polroots(r);
  p_can = prod(i = 1,poldegree(r)/2,x - a[2*i-1]);
  p_cnj = prod(i = 1,poldegree(r)/2,x - a[2*i]);
  s1 = myround(real((p_can + p_cnj) / 2),k);
  s2 = myround(real((p_can - p_cnj) / (2 * I)),k);
  mf = "out.mm";
  write1(mf,"s1gp := " s1 ";" "s2gp := " s2 ";");
}

\r in.gp
trap(,quit,gpsquares(r,x,k));
\q
