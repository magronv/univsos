default(realprecision,300);

myround(p, i) =  
{
  p = round(2^i*p)/2^i;
  mf = "out.gp";
  write1(mf,"pgp := " p ";");
}

\r in.gp
trap(,quit,myround(eiv,i));
\q
