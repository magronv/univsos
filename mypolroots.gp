default(realprecision,100);

mypolroots(r) = 
{
  a = polroots(r);
  mf = "out.mm";
  write1(mf,"agp:=[");
  for (i = 1,length(a)-1,write1(mf,a[i] ", "));
  write1(mf,a[length(a)] "];");
}


\r in.gp
trap(,quit,mypolroots(r));
\q
