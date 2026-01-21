// This Magma script is trying to use the building blocks from
// ModCrvToECNF.m to find a map from a modular curve to an elliptic curve
// defined over a number field!

SetSeed(31415,0);
AttachSpec("Modular.spec");

// Helper functions

// Given a prime p and an element of Q(zeta_N), apply the field 
// automorphism which sends zeta_N -> zeta_N^k, where k*p = 1 (mod N).
function FieldAut(e,N,p)
  PP := Parent(e);
  zz := PP.1;
  cofs := Eltseq(e);
  pinv := (Integers(N)!p)^(-1);
  pinv := Integers()!pinv;
  return &+[ cofs[i]*zz^(pinv*(i-1)) : i in [1..Degree(PP)]];
end function;

// The Hecke operators on Gamma(N) act by sending sum a(n) q^(n/N) to 
// sum sigma(a(pn)) q^(n/N) + sum b(n) q^(pn/N) for some
// sequence b(n). Here sigma is the field automorphism of Q(zeta_N) that is 
// computed by FieldAut.  We don't attempt to compute the sequence b(n).
// Reference: "p-adic Hodge theory and values of zeta functions of modular forms" 
// by Kazuya Kato, page 148.
function PartialHecke(f,N,p)
  qqq := Parent(f).1;
  newprec := Floor((AbsolutePrecision(f)-1)/p);
  if newprec gt 0 then
    ret := &+[ FieldAut(Coefficient(f,p*n),N,p)*qqq^n : n in [1..newprec]];
  else
    ret := 0;
  end if;
  ret := ret + BigO(qqq^(newprec+1));
  return ret;
end function;


// Try to use the coefficient of index coprime to p to determine the Hecke operator T_p.
// Represent a cusp form as a row vector and see how the Hecke operator acts on it using
// the above formulas. If we cannot identify the image uniquely, we might need more precision.
// In this new version, we use the Fourier expansions at all cusps.
function HeckeMatrix(forms,N,p,preclist,Verbose)
  if Verbose then
    printf "Trying to find Hecke matrix for p = %o.\n",p;
  end if;
  deg := Degree(BaseRing(Parent(forms[1][1])));
  numcusps := #preclist;
  cofslist := [ [ m : m in [1..Floor(preclist[j]/p)-1] | GCD(m,p) eq 1] : j in [1..numcusps]];
  ret := ZeroMatrix(Rationals(),#forms,#forms);
  fouriermat := Matrix(Rationals(),[ &cat [ &cat [ Eltseq(Coefficient(forms[i][j],m)) : m in cofslist[j]] : j in [1..numcusps]] : i in [1..#forms]]);
  rigorous := true;
  for i in [1..#forms] do
    curf := [ PartialHecke(forms[i][j],N,p) : j in [1..numcusps]];
    curvec := Vector(Rationals(), &cat [ &cat [ Eltseq(Coefficient(curf[j],m)) : m in cofslist[j]] : j in [1..numcusps]]);
    chk, sol, ns := IsConsistent(fouriermat,curvec);
    if chk then
      for j in [1..#forms] do
        ret[i][j] := sol[j];
      end for;
      if Dimension(ns) ge 1 then
        rigorous := false;
        if Verbose then
          printf "Representation is not unique for Hecke operator T_%o. Increasing precision may help.\n",p;
        end if;
      end if;
    else
      rigorous := false;
      if Verbose then
        printf "No representation found for Hecke operator T_%o.\n",p;
      end if;
    end if;
  end for;
  return <ret, rigorous>;
end function;

// Period helper functions

// Helper function for LiftToSL
FindNewa := function(a,c,N)
  if GCD(a, c) eq 1 then
    return a;
  end if;
  k := 1;
  while true do
    if GCD(a+N*k, c) eq 1 then
      return a+N*k;
    end if;
    if GCD(a-N*k, c) eq 1 then
      return a-N*k;
    end if;
    k := k + 1;
    assert k le 1000; // Something went wrong
  end while;
end function;

// Lift a matrix from SL_2(Z/NZ) to [a b][c d] in SL_2(Z). Makes c
// as small as possible in absolute value. We mostly follow the algorithm
// given in the proof of Theorem 3.2 from Keith Conrad's notes on SL_2(Z).
function LiftToSL(M)
  N := Characteristic(BaseRing(M));
  a := Integers()!M[1][1];
  b := Integers()!M[1][2];
  c := Integers()!M[2][1];
  d := Integers()!M[2][2];
  if c gt N/2 then
    c := c - N;
  end if;
  if c eq 0 then
    // Check to see if there is a lift with c = 0.
    if a eq 1 then
      return Matrix(Integers(),[[1,b],[0,1]]);
    end if;
    if a eq (N-1) then
      return Matrix(Integers(),[[-1,b],[0,-1]]);
    end if;
    c := N;  // We don't have a lift with c = 0. So we change c to equal N.
  end if;
  // Now we're in the case that c is nonzero
  // Find a' so that a' = a (mod N) and gcd(a',c) = 1.
  newa := FindNewa(a,c,N);
  _, x, y := XGCD(c,newa);
  // We have d = 1 and c*x + newa*y = 1.
  delta := (1 - (newa*d-b*c));
  newb := b - x*delta;
  newd := d + y*delta;
  ret0 := Matrix(Integers(),[[newa,newb],[c,newd]]);
  // ret0 is in SL_2(Z). But let's tweak it so d is smallish.
  absNc := AbsoluteValue(N*c);
  smalld := newd mod absNc;
  if smalld gt absNc/2 then
    smalld := smalld - absNc;
  end if;
  k := Integers()!((smalld - newd)/(N*c));
  return ret0*Matrix(Integers(),[[1,k*N],[0,1]]);
end function;

// Take an element of PSL_2(Z) and write it as a word in S = [0 -1][1 0] and
// T = [1 1][0 1] in the form M = S*T^a*S*T^b*S*T^c*... or T^a*S*T^b*S*....
// The output is two lists: one list of matrices (each of which is S or T)
// and the other of which is the exponents. 
function WordsInST(M)
  curM := M;
  matlist := [];
  exlist := [];
  done := false;
  S := Matrix([[0,-1],[1,0]]);
  T := Matrix([[1,1],[0,1]]);
  while not done do
    a := curM[1][1];
    c := curM[2][1];
    if (c eq 0) then
      // M equals [1 m][0 1] in PSL_2(Z).
      done := true;
      if (curM[1][2] ne 0) then
        Append(~matlist,T);
        Append(~exlist,-curM[1][1]*curM[1][2]);
        curM := T^(-(curM[1][1]*curM[1][2]))*curM;
      end if;  
    end if;
    if (c ne 0) and (AbsoluteValue(c) gt AbsoluteValue(a)) then
      Append(~matlist,S);
      Append(~exlist,1);
      curM := S*curM;
    end if;
    if (c ne 0) and (AbsoluteValue(c) le AbsoluteValue(a)) then
      r := a mod c;
      q := Integers()!((a-r)/c);
      Append(~matlist,T);
      Append(~exlist,-q);
      curM := T^(-q)*curM;
    end if;    
  end while;
  // At this point, we've actually written a formula for the inverse of M.
  // Negate exponents on T. 
  exlist2 := [];
  for j in [1..#matlist] do
    if matlist[j] eq S then
      Append(~exlist2,1);
    else
      Append(~exlist2,-exlist[j]);
    end if;
  end for;
  return <matlist, exlist2>;
end function;

// Given a modular form f and a matrix W in SL_2(Z), compute the Fourier expansion at infinity of f|W.
// David Zywina's ConvertModularFormExpansions basically does this, but our situation
// doesn't actually fit the hypotheses of his function. We return the expansion in terms of q^(1/N).
function TransformAtInfinity(MCR, form, W)
  cuspdata := FindCuspData(MCR,W);
  // cuspdata[1] indicates which cusp.
  ret := form[cuspdata[1]];
  PSring := Parent(ret);
  CF := BaseRing(Parent(ret));
  z0 := CF.1;
  chk, ord := IsRootOfUnity(z0);
  expo := ord/MCR`widths[cuspdata[1]];
  expo := Integers()!expo;
  z := z0^expo;
  expo2 := MCR`gl2level/MCR`widths[cuspdata[1]];
  expo2 := Integers()!expo2;  
  ret := Evaluate(ret,z^cuspdata[2]*PSring.1^expo2);
  return ret;
end function;

// Compute period of a given modular form for a given matrix in SL_2(Z)
// We take the matrix and compute the integral of form from I to mat(I).
// We break this up into a pieces based on representing mat as a word in S and T.
// We use Fourier expansions at all cusps to make this happen.
function ComputePeriodAlongWord(ModEC, form, wrd)
  mats := wrd[1]; exs := wrd[2];
  matlist := [ mats[j]^exs[j] : j in [1..#mats]];
  C := ModEC`C;
  ret := C!0;
  N := ModEC`N;
  GG := GL(2,Integers(N));
  //"Word length:", #matlist;
  for j in [1..#matlist] do
    if (j lt #matlist) then
      W := &*[ matlist[k] : k in [1..#matlist-j]];
    else
      W := Matrix([[1,0],[0,1]]);
    end if;  
    W2 := matlist[#matlist-j+1];
    // We want to compute the integral of form | W
    // and evaluate this at W2(i) and at i.
    formfourier := TransformAtInfinity(ModEC`MCR, form, GG!W);
    val2 := (W2[1][1]*C.1+W2[1][2])/(W2[2][1]*C.1+W2[2][2]);
    coflist := [ Evaluate(Coefficient(formfourier,j), ModEC`psiCF) : j in [1..ModEC`prec-1]];
    formval1 := &+[ (N*coflist[n]/n)*ModEC`EXP[n] : n in [1..ModEC`prec-1]];
    formval2 := &+[ (N*coflist[n]/n)*Exp(2*Pi(C)*C.1*(n/N)*val2) : n in [1..ModEC`prec-1]];
    ret := ret + (formval2 - formval1);    
  end for;
  return ret;
end function;

// Computes int_{a/b}^{i*infinity} f(z) dz for cusp a/b as follows:
// int_{a/b}^{i*infinity} f(z) dz = int_{M(i*infinity)}^{M(i)} f(z) dz + int_{M(i)}^i f(z) dz + int_{i}^{i*infinity} f(z) dz
PeriodIntegralFromCusp := function(ModEC, form, cusp)
    a := cusp[1]; b := cusp[2];
    prec := ModEC`prec;
    N := ModEC`MCR`gl2level;
    _, y, x := XGCD(a, -b);
    M := Matrix([[a, x], [b, y]]); // might need to coerce into GL2
    formfourier := TransformAtInfinity(ModEC`MCR,form,M);
    coflist := [ Evaluate(Coefficient(formfourier,j), ModEC`psiCF) : j in [1..prec-1]];
    formval1 := &+[ (N*coflist[n]/n)*ModEC`EXP[n] : n in [1..prec-1]];
    formval2 := -ComputePeriodAlongWord(ModEC, form, WordsInST(M));
    formfourier2 := TransformAtInfinity(ModEC`MCR,form,Matrix([[1,0],[0,1]]));
    coflist2 := [ Evaluate(Coefficient(formfourier2,j), ModEC`psiCF) : j in [1..prec-1]];
    formval3 := - &+[ (N*coflist2[n]/n)*ModEC`EXP[n] : n in [1..prec-1]];
    return formval1 + formval2 + formval3;
end function;

// Generate a collection of matrices for period computations. We start by including generators
// of the group, and then choose random matrices = I (mod N) that have word length <= MaxLen.
RandWords := function(N, genlist, Verbose : NumMats := 20, MaxLen := 50)
  if Verbose then
    printf "Computing periods of %o matrices (max length %o).\n", NumMats, MaxLen;
  end if;
  SL2inter := sub<GL(2,Integers(N)) | genlist> meet SL(2,Integers(N));
  Gam := CongruenceSubgroup(N);
  Sl := SL(2,Integers());
  matlist := [LiftToSL(mat) : mat in Generators(SL2inter)];
  wrdlist := [wrd : wrd in [WordsInST(M) : M in matlist] | #wrd[1] ge 1];
  while #matlist lt NumMats do
    M := Sl!Matrix(Random(Gam, 100*N));
    if not M in matlist then
      wrd := WordsInST(M);
      if #wrd[1] ge 1 and #wrd[1] le MaxLen then
        Append(~matlist, M);
        Append(~wrdlist, wrd);
      end if;
    end if;
  end while;
  return wrdlist;
end function;

// Given elements in the period lattice (scaled by a constant) of an elliptic 
// curve, try to determine whether the discriminant of the curve is positive 
// or negative, and the approximate periods of the lattice.
FindLatType := function(C, perlist)
  rmin := Minimum({AbsoluteValue(Real(z)) : z in perlist | AbsoluteValue(Real(z)) ge 0.01});
  imin := Minimum({AbsoluteValue(Imaginary(z)) : z in perlist | AbsoluteValue(Imaginary(z)) ge 0.01});
  M := Matrix([ Vector(Rationals(),[BestApproximation(Real(z)/rmin,100),BestApproximation(Imaginary(z)/imin,100)]) : z in perlist]);
  L := Lattice(M);
  Lx := Lattice(Submatrix(M,1,1,NumberOfRows(M),1));
  Ly := Lattice(Submatrix(M,1,2,NumberOfRows(M),1));
  // Lx and Ly are the projections of L onto the 1st and 2nd coordinate.
  a := Vector(Lx.1)[1];
  b := Vector(Ly.1)[1];
  prmin := a*rmin;
  pimin := b*imin;
  L2 := Lattice(Matrix([[a,0],[0,b]]));
  if L eq L2 then
    return 1, [prmin, pimin*C.1];
  end if;
  if Index(L2,L) eq 2 then
    return -1, [2*prmin, (prmin + pimin*C.1) ];
  end if;
  print "Error: Failed to find lattice type.";
  assert false;
end function;

// Determine an exact point on EK, given an approximate point. This requires
// factoring division polynomials over Q(zeta_N).
MatchPtOnEC := function(EK, E, psiCF, a2, b2, decprec, RtsCache, k, Verbose)
  ord := LCM([ Denominator(a2), Denominator(b2)]);
  if Verbose then
    printf "Image of cusp %o has order %o on elliptic curve.\n",k,ord;
  end if;
  if ord eq 1 then
    ECpt2 := EK![0,1,0];
    if Verbose then
      printf "Point is %o.\n",ECpt2;
    end if;
  else
    if IsDefined(RtsCache,<EK, ord>) then
      rts := RtsCache[<EK, ord>];
    else
      divpoly := PrimitiveDivisionPolynomial(EK,ord);
      rts := Roots(divpoly);
      RtsCache[<EK,ord>] := rts;
    end if;
    Eper := Periods(E);
    ECpt := EllipticExponential(E,(a2*Eper[1]+b2*Eper[2]));
    rtsC := [ Evaluate(rts[j][1],psiCF) : j in [1..#rts]];
    goodind := [ j : j in [1..#rts] | AbsoluteValue(ECpt[1]-rtsC[j]) lt 10^(-(decprec-2)) ];
    assert (#goodind eq 1);
    xcoord := rts[goodind[1]][1];
    _, ECpt2 := IsPoint(EK,xcoord);
    if AbsoluteValue(Evaluate(ECpt2[2],psiCF)-ECpt[2]) ge 10^(-(decprec-2)) then
      ECpt2 := -ECpt2;
    end if;
    err := AbsoluteValue(Evaluate(ECpt2[2],psiCF)-ECpt[2]);
    assert (err le 10^(-20));
    if Verbose then
      printf "Point is %o.\n",ECpt2;
    end if;
  end if;
  return ECpt2, RtsCache;
end function;

// We use a formula from Wikipedia for the Fourier expansion of the Weierstrass p-function:
// p(z) = (1/z^2) + z^2 * sum (d_k * z^(2*k))/k!.
// Here d_0 = 3G_4, d_1 = 5G_6 and there's a recurrence relation given there. First, let's calculate the d's
WeierstrassP := function(a, b, prec, zz)
  dlist := [-a/5,-b/7];
  for n in [0..Floor(prec/2)] do
    // Compute d_(n+2) using recursion on Eisenstein series Wikipedia page. See also https://dlmf.nist.gov/23.9.
    newterm := ((3*n+6)/(2*n+9))*&+[ Binomial(n,k)*dlist[k+1]*dlist[n-k+1] : k in [0..n]];
    Append(~dlist,newterm);
  end for;
  wp := 1/zz^2 + &+[ zz^(2*k+2)*dlist[k+1]/Factorial(k) : k in [0..Floor(prec/2)]] + BigO(zz^prec);
  wpderiv := Derivative(wp);
  return wp, wpderiv;
end function;

// Compute the degree of the map to the elliptic curve, using Theorem 3 of
// John Cremona's "Computing the degree of the modular parametrization of
// a modular elliptic curve", Math. Comp. 64 (1995). The inputs are the ModEC record, the modular form f
// (given as a tuple of Fourier expansions), and generators of its period lattice
// as output by FindLatType.

// A helper function for AnalyticDegree. This takes as input a matrix gamma, a group GSL,
// a set of coset representatives, and the coset map mp. It outputs the matrix
// t(gamma) so that gamma*T = t(gamma)*mp(gamma).
tfunc := function(gamma,GSL,bigSL,coreps,mp)
  ind := Index([ (bigSL!coreps[i])*((bigSL!gamma)*(bigSL!Matrix([[1,1],[0,1]])))^(-1) in GSL : i in [1..#coreps]],true);
  tau := coreps[ind];
  ret := gamma*Matrix([[1,1],[0,1]])*tau^(-1);
  return ret, tau;
end function;

// Compute the analytic modular degree of the map associated with modf.
AnalyticDegree := function(ModEC,modf,pergens)
  if ModEC`Verbose then
    printf "Starting modular degree computation.\n";
  end if;
  lev := ModEC`MCR`gl2level;
  bigSL := SL(2,Integers(lev));
  bigGL := GL(2,Integers(lev));
  GSL := sub<GL(2,Integers(ModEC`MCR`gl2level)) | [ bigGL!t : t in ModEC`gens]> meet SL(2,Integers(lev));
  cosetreps, mp := RightTransversal(bigSL,GSL);

  // Now, build a set of representatives of the right cosets so that if gamma is in
  // the set, so is gamma*(TS).
  coreps := [];
  // Ignore a coset if it is fixed by TS.
  todo := [ cosetreps[i] : i in [1..#cosetreps]];
  donealready := [];
  done := false;
  T := Matrix(Integers(),[[1,1],[0,1]]);
  S := Matrix(Integers(),[[0,-1],[1,0]]);
  while done eq false do
    newind := Min([ i : i in [1..#todo] | not (todo[i] in donealready)]);
    newmat1 := LiftToSL(cosetreps[newind]);
    Append(~coreps,newmat1);
    Append(~donealready,mp(bigSL!newmat1));
    if not (mp(bigSL!(newmat1*T*S))) eq mp(bigSL!newmat1) then
      newmat2 := newmat1*T*S;
      newmat3 := newmat2*T*S;
      Append(~coreps,newmat2);
      Append(~coreps,newmat3);
      Append(~donealready,mp(bigSL!newmat2));
      Append(~donealready,mp(bigSL!newmat3));
    end if;  
    if #coreps eq #todo then
      done := true;
    end if;
  end while;  
  
  // For each cosetrep, compute the t, and the corresponding period.

  npairlist := [];
  if ModEC`Verbose then
    printf "Computing %o periods.\n",#coreps;
  end if;
  for i in [1..#coreps] do
    tt := tfunc(coreps[i],GSL,bigSL,coreps,mp);
    rawper := ComputePeriodAlongWord(ModEC,modf,WordsInST(tt));
    lst := [ <a,b,a*pergens[1]+b*pergens[2]> : a in [-50..50], b in [-50..50]];
    minval, ind := Min([ AbsoluteValue(lst[k][3]-rawper) : k in [1..#lst]]);
    n2 := lst[ind][2];
    n1 := lst[ind][1];
    //printf "Raw period %o. Got <%o,%o> with error of %o.\n",rawper,n1,n2,minval;
    Append(~npairlist,<n1,n2>);
  end for;

  // Now divide the coset reps into orbits.

  orbs := [];
  sorted := [];
  done := false;
  while done eq false do
    // Do one orbit per iteration
    startind := Min([ k : k in [1..#coreps] | not (coreps[k] in sorted)]);
    neworb := [ coreps[startind]];
    Append(~sorted,coreps[startind]);
    done2 := false;
    while (done2 eq false) do
      tt, tau := tfunc(neworb[#neworb],GSL,bigSL,coreps,mp);
      next := tau;
      if next ne neworb[1] then
        Append(~neworb,next);
        Append(~sorted,next);
      else
        done2 := true;
      end if;
    end while;
    Append(~orbs,neworb);
    if #sorted eq #coreps then
      done := true;
    end if;
  end while;

  // Compute the answer
  ret := 0;
  percount := 0;
  for k in [1..#orbs] do
    orbcont := 0;
    for l in [1..#orbs[k]-1] do
      mat1 := orbs[k][l];
      ind := Index(coreps,mat1);
      npair1 := npairlist[ind];
      for m in [l+1..#orbs[k]] do
        mat2 := orbs[k][m];
        ind2 := Index(coreps,mat2);
        npair2 := npairlist[ind2];
        orbcont := orbcont + (1/2)*(npair1[1]*npair2[2]-npair1[2]*npair2[1]);    
      end for;
    end for;
    ret := ret + orbcont;    
  end for;
  if ModEC`Verbose then
    printf "Analytic modular degree is %o.\n",ret;
  end if;
  return ret;
end function;

/*
// Select the "optimal" E in the isogeny class. The period lattice of this optimal E will be a rational scalar multiple
// of the period lattice for the modular form.
PickBestECs := function(ModEC)
  moddeglist := [];
  pers := [];
  Elist := [];
  manin := [];
  for r in [1..#ModEC`ainvlist] do
    pers0 := [];
    Elist0 := [];
    manin0 := [];
    iso := IsogenousCurves(EllipticCurve(ModEC`ainvlist[r]));
    for i in [1..ModEC`nummaps] do
      // This code won't quite work properly if nummaps > 1.
      sgn, per := FindLatType(ModEC`C, ModEC`perlist[r][i]); 
      E, rr := IdentifyEC(iso, sgn, per);
      Append(~pers0,per);
      Append(~Elist0, E);
      Append(~manin0, 1/rr);
      if ModEC`Verbose then
        printf "Best elliptic curve %o is %o. The Manin constant is %o.\n",i,aInvariants(E),1/rr;
      end if;
      ad := AnalyticDegree(ModEC,ModEC`goodforms[r][i],per);
      if (#moddeglist eq 0) or (ad lt Min(moddeglist)) then
        pers := pers0;
        Elist := Elist0;
        manin := manin0;
      end if;
      Append(~moddeglist,ad);
    end for;  
  end for;
  minmoddeg, ind := Min(moddeglist);
  if ModEC`Verbose then
    printf "Minimal modular degree is %o. Choosing elliptic curve %o.\n",minmoddeg,aInvariants(Elist[1]);
  end if;
  Egiven := Elist[1];
  goodforms := ModEC`goodforms[ind];
  goodforms := goodforms;
  return pers, Elist, manin, Egiven, goodforms, minmoddeg;
end function;
*/

// Decrease power series precision as appropriate. Sometimes this is still a bit too aggressive, and the
// actual precision we need will depend on the analytic degree.
TweakPrec := function(ModEC)
  g := ModEC`MCR`genus;
  maxr := Floor((3*ModEC`ECdegmap+g-1)/ModEC`MCR`model_degree)+1;
  // The maximum degree in the canonical ring needed to get the map.
  // Now we use the Sturm bound to know how much precision we need.
  if ModEC`Verbose then
    printf "Tweaking precision.\n";
    printf "Guaranteed to find map in degree %o.\n",maxr;
  end if; 
  if ModEC`Verbose then
    printf "Old preclist = %o.\n",ModEC`preclist;
  end if;
  numcusps := #ModEC`MCR`cusps;
  precsum := ((3*maxr*ModEC`MCR`k)/12)*ModEC`MCR`index;
  multiplier := &+[ ModEC`MCR`widths[r]/ModEC`MCR`sl2level : r in [1..numcusps]];
  powerprec := Ceiling(precsum/multiplier);
  if (powerprec gt ModEC`prec) then
    printf "The precision currently available is %o, but the needed precision is %o.\n",ModEC`prec,powerprec;
    printf "Try rerunning this case with precmult = %o.\n",RealField(5)!(0.1+powerprec/ModEC`prec);
    assert false;  
  end if;
  preclist := [Max(Ceiling(Min(powerprec*ModEC`precmult,ModEC`prec)*ModEC`MCR`widths[i]/ModEC`MCR`sl2level),2) : i in [1..numcusps]];
  if ModEC`Verbose then
    printf "Setting powerprec = %o.\n",Min(powerprec*ModEC`precmult,ModEC`prec);
    printf "New preclist = %o.\n",preclist;
  end if;
  return preclist, maxr;
end function;

RatLatApx := function(bas, z, decprec, i, k)
  Mat := Matrix([[Real(bas[1]),Imaginary(bas[1])],[Real(bas[2]),Imaginary(bas[2])]]);
  vc := Matrix([[Real(z),Imaginary(z)]]);
  //printf "Mat = %o. Base ring is %o.\n",Mat,BaseRing(Mat);
  //printf "vc = %o. Base ring is %o.\n",vc,BaseRing(vc);
  sols := vc*Mat^(-1);
  //printf "sols = %o.\n",sols;
  a := sols[1][1];
  b := sols[1][2];
  //printf "z = %o. We get a = %o, b = %o.\n",z,a,b;
  a2 := BestApproximation(a,100);
  b2 := BestApproximation(b,100);
  chk := z - a2*bas[1] - b2*bas[2];
  if AbsoluteValue(chk) gt 10^(-(decprec-3)) then
    printf "Rational identification error with map = %o, cusp = %o.\n",i,k;
    assert false;
  end if;
  return a2, b2;
end function;

// Compute exact points on EK coming from the period integrals.
PerIntImages := function(ModEC)
  aval := 1+ModEC`K.1^7;
  numcusps := #ModEC`MCR`cusps;
  translist := <>;
  RtsCache := AssociativeArray();
  for i in [1..ModEC`nummaps] do
    mapilist := [];
    EK := BaseChange(ModEC`Elist[i], ModEC`K);
    for k in [1..numcusps] do
      curper := PeriodIntegralFromCusp(ModEC, ModEC`goodforms[i],[ModEC`MCR`cusps[k][1][1], ModEC`MCR`cusps[k][2][1]]);
      // Now write curper = a*pers[i][1] + b*pers[i][2]
      a2, b2 := RatLatApx(ModEC`pers, curper, ModEC`decprec, i, k);
      //printf "We found that the point is %o*omega_1 + %o*omega_2.\n",a2,b2;
      // phiK := InfinitePlaces(K)[1];
      // Now we have a complex approximation for the point we seek. We need the coordinates
      // of this in Q(zeta_N)
      //ECpt2, RtsCache := MatchPtOnEC(EK, ModEC`Elist[i], ModEC`psiCF, a2, b2, ModEC`decprec, RtsCache, k, ModEC`Verbose);
      // Unfortunately, Magma's EllipticExponential function doesn't work
      // for elliptic curves defined over C, so we need to use Sage to do this part manually.
      // The results are recorded below.
      if (k eq 1) then
        ECpt2 := EK![0,1,0];
      end if;
      if (k in [2,3,4]) then
        ECpt2 := EK![1,aval-1,1];
      end if;
      Append(~mapilist,ECpt2);  
    end for;
    Append(~translist,mapilist);
  end for;
  return translist;
end function;

// Compute Fourier expansions of the modular functions x(z), y(z) that define X_G --> E.
// This is similar to PARI/GP's function "elltaniyama".
FourierExpOfMaps := function(ModEC)
  numcusps := #ModEC`MCR`cusps;
  xfourierlist := [];
  yfourierlist := [];
  newprec := [];
  RR<zz> := LaurentSeriesRing(ModEC`K);
  ModEC`RR := RR;
  for i in [1..ModEC`nummaps] do
    if ModEC`Verbose then
      printf "Finding elliptic curve map %o.\n",i;
    end if;

    // Should we use Fourier expansion at all cusps, or just one?
    pullback := [ ModEC`manin[i]*ModEC`goodforms[i][j] : j in [1..numcusps]];

    E2, weiermap := WeierstrassModel(ModEC`Elist[i]);
    a := aInvariants(E2)[4];
    b := aInvariants(E2)[5];
    ainvi := aInvariants(ModEC`Elist[i]);

    wp, wpderiv := WeierstrassP(a, b, ModEC`prec, zz);

    des := DefiningEquations(Inverse(weiermap));
    PP := Parent(des[2]);
    _, scal := IsPower(Rationals()!MonomialCoefficient(des[2],PP.2),3);

    // The short Weierstrass model is parametrized by x = wp, and y = wpderiv/2.
    x0 := Evaluate(des[1],[wp,wpderiv/2,1]);
    y0 := Evaluate(des[2],[wp,wpderiv/2,1]);

    xf := [];
    yf := [];
    np := [];
    for j in [1..numcusps] do
      intgoodcusp := &+[ (ModEC`MCR`widths[j]/n)*Coefficient(pullback[j],n)*ModEC`PS.1^n : n in [1..ModEC`preclist[j]-1]] + BigO(ModEC`PS.1^ModEC`preclist[j]);
      if ModEC`Verbose then
        printf "Computing Fourier expansions of x and y modular functions at cusp %o of %o.\n",j,numcusps;
      end if;

      xfourier := Evaluate(x0,intgoodcusp*scal);
      yfourier := Evaluate(y0,intgoodcusp*scal);

      // We need to do some messing with this based on weiermap.

      dxfourier := &+[ (n/ModEC`MCR`widths[j])*Coefficient(xfourier,n)*zz^n : n in [Valuation(xfourier)..AbsolutePrecision(xfourier)-1]] + BigO(zz^AbsolutePrecision(xfourier));
      invdiff := dxfourier/(2*yfourier+ainvi[1]*xfourier+ainvi[3]);
      assert IsWeaklyZero(pullback[j]-invdiff);

      // Finally, we need to translate this by the EC points in translist.

      // TranslateBy ...
      transpt := -ModEC`translist[i][j];
      if Order(transpt) eq 1 then
        newxfourier := xfourier;
        newyfourier := yfourier;
      else
        lam := (yfourier-transpt[2])/(xfourier-transpt[1]);
        nu := (transpt[2]*xfourier-yfourier*transpt[1])/(xfourier-transpt[1]);
        newxfourier := lam^2 + ainvi[1]*lam - ainvi[2] - transpt[1]-xfourier;
        newyfourier := -(lam + ainvi[1])*newxfourier - nu - ainvi[3];
      end if;
      Append(~np,Min(RelativePrecision(newxfourier),RelativePrecision(newyfourier)));      
      // ... TranslateBy
      Append(~xf,newxfourier);
      Append(~yf,newyfourier);
      // IsOnCurve ...
      chkchk := yf[#yf]^2 + ainvi[1]*xf[#xf]*yf[#yf] + ainvi[3]*yf[#yf]
      - (xf[#xf]^3 + ainvi[2]*xf[#xf]^2 + ainvi[4]*xf[#xf] + ainvi[5]);
      assert IsWeaklyZero(chkchk);
      // ... IsOnCurve
    end for;
    Append(~xfourierlist,xf);
    Append(~yfourierlist,yf);
    Append(~newprec,np);
  end for;
  return xfourierlist, yfourierlist, newprec, RR;
end function;

// Realize the modular functions in the function field of X_G. Here we do the computation over Q(zeta_N).
// The ultimate goal here is just to compute the image under X_G -> E of the rational basepoint on X_G.
// So we make sure to pick a rational map from X_G -> E that doesn't have the basepoint in the base locus.
RealizeInFF := function(ModEC)
  numcusps := #ModEC`MCR`cusps;
  polyring := PolynomialRing(ModEC`K,#ModEC`genforms,"grevlex");
  vars := [ polyring.i : i in [1..#ModEC`genforms]];
  gens := [ Evaluate(ModEC`MCR`psi[j],vars) : j in [1..#ModEC`MCR`psi]];
  ttemp := Cputime();
  if ModEC`Verbose then
    printf "Computing Grobner basis for ideal.\n";
  end if;
  I := ideal<polyring | gens>;
  G := GroebnerBasis(I);
  gbtime := Cputime(ttemp);
  if ModEC`Verbose then
    printf "Grobner basis time was %o.\n",gbtime;
  end if;
  LMs := [ LeadingMonomial(G[i]) : i in [1..#G]];
  initideal := ideal<polyring | LMs>;

  // canring is a list of pairs.
  // The first thing in a pair is list of lists of Fourier expansions
  // of the degree d generators of the canonical ring.
  // The second thing in a pair is list of degree d monomials representing the
  // elements.

  canring := <>;

  // Let's choose monomials that will *always* work!

  if ModEC`Verbose then
    printf "Generating cyclotomic canonical ring.\n";
  end if;

  donelist := [ false : i in [1..ModEC`nummaps]];
  // Tweak to check d = 1 case.
  d := 0;
  ecmaps := [ [polyring!0,polyring!0,polyring!0] : i in [1..ModEC`nummaps]];
  while not (&and donelist) do
    d := d + 1;
    if ModEC`Verbose then
      printf "Generating degree %o piece of canonical ring.\n",d;
    end if;
    mons := MonomialsOfDegree(polyring,d);
    bas := [ m : m in mons | not (m in initideal)];
    newfourier := <>;
    newvars := [];
    if (d eq 1) then
      for ind in [1..#vars] do
        newprd := [ ModEC`RR!ModEC`genforms[ind][r] + BigO(ModEC`RR.1^(ModEC`preclist[r]+1)): r in [1..numcusps]];
        Append(~newfourier,newprd);
      end for;
      newvars := vars;
    else
      for j in [1..#bas] do
        curmon := bas[j];
        // We have to be able to write curmon as a product of a degree (d-1)
        // monomial not in initideal, and a degree 1 element.
        // If we couldn't, then curmon would be in initideal
        ind := Index([ IsDivisibleBy(curmon,canring[d-1][2][k]) : k in [1..#canring[d-1][2]]],true);
        chk, q := IsDivisibleBy(curmon,canring[d-1][2][ind]);
        ind2 := Index(vars,q);
        newprd := [ModEC`RR!(ModEC`genforms[ind2][r]*canring[d-1][1][ind][r]) : r in [1..numcusps]];
        Append(~newfourier,newprd);
        Append(~newvars,curmon);
      end for;  
    end if;
    Append(~canring,<newfourier,newvars>);

    for ii in [1..ModEC`nummaps] do
      if not donelist[ii] and (d ge ModEC`maxdegree - 1) then
        // We only build the matrix if we might find the map.
        if ModEC`Verbose then
          printf "Searching for map %o of %o.\n",ii,ModEC`nummaps;
        end if;
        multtime := 0;
        jointime := 0;
        mat := ZeroMatrix(ModEC`K,0,2*&+[ ModEC`newprec[ii][r] : r in [1..numcusps]]);
        for i in [1..#canring[d][1]] do
          pre := Cputime();
          pp := [ ModEC`xfourierlist[ii][r]*canring[d][1][i][r] : r in [1..numcusps]];
          pp2 := [ ModEC`yfourierlist[ii][r]*canring[d][1][i][r] : r in [1..numcusps]];
          post := Cputime(pre);
          multtime := multtime + post;      
          vecseq := &cat [ [ Coefficient(pp[r],m) : m in [Valuation(ModEC`xfourierlist[ii][r])..Valuation(ModEC`xfourierlist[ii][r])+ModEC`newprec[ii][r]-1]] : r in [1..numcusps]];
          vecseq2 := &cat [ [ Coefficient(pp2[r],m) : m in [Valuation(ModEC`yfourierlist[ii][r])..Valuation(ModEC`yfourierlist[ii][r])+ModEC`newprec[ii][r]-1]] : r in [1..numcusps]];
          pre := Cputime();
          mat := VerticalJoin(mat,Matrix(ModEC`K,1,#vecseq+#vecseq2,vecseq cat vecseq2));
          post := Cputime(pre);
          jointime := jointime + post;
        end for;
        for i in [1..#canring[d][1]] do
          vecseq := &cat [ [ Coefficient(canring[d][1][i][r],m) : m in [Valuation(ModEC`xfourierlist[ii][r])..Valuation(ModEC`xfourierlist[ii][r])+ModEC`newprec[ii][r]-1]] : r in [1..numcusps]];
          vecseq2 := &cat [ [ ModEC`K!0 : m in [Valuation(ModEC`yfourierlist[ii][r])..Valuation(ModEC`yfourierlist[ii][r])+ModEC`newprec[ii][r]-1]] : r in [1..numcusps]];
          pre := Cputime();
          mat := VerticalJoin(mat,Matrix(ModEC`K,1,#vecseq+#vecseq2,vecseq cat vecseq2));
          post := Cputime(pre);
          jointime := jointime + post;
        end for;
        for i in [1..#canring[d][1]] do
          vecseq := &cat [ [ ModEC`K!0 : m in [Valuation(ModEC`xfourierlist[ii][r])..Valuation(ModEC`xfourierlist[ii][r])+ModEC`newprec[ii][r]-1]] : r in [1..numcusps]];
          vecseq2 := &cat [ [ Coefficient(canring[d][1][i][r],m) : m in [Valuation(ModEC`yfourierlist[ii][r])..Valuation(ModEC`yfourierlist[ii][r])+ModEC`newprec[ii][r]-1]] : r in [1..numcusps]];
          pre := Cputime();
          mat := VerticalJoin(mat,Matrix(ModEC`K,1,#vecseq+#vecseq2,vecseq cat vecseq2));
          post := Cputime(pre);
          jointime := jointime + post;
        end for;
        if (ModEC`Verbose eq true) then
          printf "Matrix dimensions are %o x %o.\n",NumberOfRows(mat),NumberOfColumns(mat);
          printf "Multiplication time was %o sec.\n",multtime;
          printf "Join time was %o sec.\n",jointime;
        end if;
        pre := Cputime();
        NN2 := NullSpace(mat);
        nulltime := Cputime(pre);
        dimdim2 := Dimension(NN2);
        if ModEC`Verbose then
          printf "For d = %o, dimension of null space is %o.\n",d,dimdim2;
          printf "Null space time was %o sec.\n",nulltime;
        end if;
        if (dimdim2 eq 0) and (d ge ModEC`maxdegree) then
          printf "We didn't find a map in a degree where it is guaranteed to exist!\n";
          assert false;
        end if;
        if dimdim2 ge 1 then
          if not (assigned ModEC`cyclodegree) then
            ModEC`cyclodegree := d;
          end if;
          // If the assertion above fails, we are finding the map in a degree where it is
          // guaranteed not to exist.

          // Make sure to get a map where our chosen base point on X_G
          // is not in the base locus! Magma can be really slow 
          // to evaluate our map in Step 10 otherwise.
          B := Basis(NN2);
          chknull := false;
          it := 0;
          ptseq := Eltseq(ModEC`BasePt);
          while (chknull eq false) do
            it := it + 1;
            v2 := B[it];
            ZZ := &+[ v2[i]*bas[i] : i in [1..#bas]];
            XX := -&+[ v2[i+#bas]*bas[i] : i in [1..#bas]];
            YY := -&+[ v2[i+2*#bas]*bas[i] : i in [1..#bas]];
            if (Evaluate(ZZ,ptseq) ne 0) or (Evaluate(XX,ptseq) ne 0) or (Evaluate(YY,ptseq) ne 0) then
              if ModEC`Verbose then
                printf "Null space vector %o of %o is good.\n",it,dimdim2;
              end if;
              chknull := true;
              donelist[ii] := true;
              ecmaps[ii][3] := ZZ;
              ecmaps[ii][1] := XX;
              ecmaps[ii][2] := YY;
            end if;
            if (it eq #B) then
              chknull := true;
            end if;
          end while;
        end if;
      end if;  
    end for;
  end while;

  return ecmaps, LMs, canring, ModEC`cyclodegree;
end function;

N := 21;
gens := [[7,4,4,14],[14,5,8,7],[14,6,3,7],[14,10,20,14]];

decprec := 50;
precmult := 1;
Verbose := true;

RecModEC := recformat<
    N, gens, ainvlist, multlist, nummaps, CheckLocal, LocalExp, decprec, precmult, Verbose, IgnoreBase,
    C, EXP, prec, MCR, preclist, genforms, XG,
    BasePt,
    PS, K, B, goodforms, psiCF,
    perlist,
    pers, Elist, manin, Egiven, ECdegmap,
    translist,
    xfourierlist, yfourierlist, newprec, RR, maxdegree, cyclodegree,
    ecmaps, LMs, canring,
    newxfourierlist, newyfourierlist, newprec2
  >;
  transposegens := [ [a[1],a[3],a[2],a[4]] : a in gens ];
  // David Zywina's code has an "opposite" modular intepretation to that of the LMFDB.
  // For consistency with the LMFDB we take a transpose here.
  ModEC := rec<RecModEC | N := N, gens := transposegens, decprec := decprec, precmult := precmult, Verbose := Verbose>;

  SetKantPrecision(2 * decprec);
  CC<I> := ComplexField(2*decprec);
  ModEC`C := CC;


maxtest := 4*ModEC`N^2;
EXP := [Exp(-2*Pi(ModEC`C)*n/ModEC`N) : n in [1..maxtest]];
termest := [ 1.5*ModEC`N*NumberOfDivisors(n)*Sqrt(ModEC`C!n)*EXP[n] : n in [1..maxtest]];
// At some point, change this to depend on sl2level.
prec := 1;
done := false;
while not done do
  if Real(&+[ termest[i] : i in [prec+1..maxtest]]) lt 10^(-(ModEC`decprec+1)) then
    done := true;
  else
    prec := prec + 1;
    if (prec gt maxtest) then
      printf "Error! Need to increase maxtest.\n";
      assert false;
    end if;
  end if;
end while;
prec := Round(prec*precmult);
// This is the precision in q^(1/N) that we need at the cusp at infinity.

G := GL(2,Integers(ModEC`N));
genlist := [ G!s : s in ModEC`gens];
MCR := CreateModularCurveRec(ModEC`N, genlist);
MCR := FindModelOfXG(MCR);
MCR := IncreaseModularFormPrecision(MCR, prec);

ModEC`EXP := EXP; 
ModEC`prec := prec; 
ModEC`MCR := MCR;
gl2lev := MCR`gl2level;
sl2lev := MCR`sl2level;
numcusps := #MCR`cusps;
cuspwidths := MCR`widths;
ModEC`preclist := [Ceiling(prec*cuspwidths[i]/sl2lev) : i in [1..numcusps]];
ModEC`genforms := [ [ MCR`F0[i][j] : j in [1..numcusps]] : i in [1..#MCR`F0]];
ModEC`XG := Curve(ProjectiveSpace(Rationals(),#ModEC`genforms-1),MCR`psi : Nonsingular := true);
if (MCR`k gt 2) then
  MCR := FindModularForms(2,MCR);
  MCR := IncreaseModularFormPrecision(MCR,prec);
end if;  
MCR := FindCuspForms(MCR);
ModEC`MCR := MCR;
ModEC`PS := Parent(MCR`F0[1][1]);
K := BaseRing(ModEC`PS);
ModEC`K := K;
ModEC`psiCF := InfinitePlaces(ModEC`K)[1];

ModEC`BasePt := ModEC`XG![1,0,0];
IgnoreBase := false;

Hp := HeckeMatrix(ModEC`MCR`F0,21,2,ModEC`preclist,Verbose);
I := IdentityMatrix(Rationals(),3);
// We see that Hp has [0 3 2] in its null space
// and the subspace spanned by F0[1] and F0[3] is
// Hp invariant.
form1 := MCR`F0[1];
form2 := MCR`F0[3];

wrdlist := RandWords(ModEC`N,ModEC`gens,ModEC`Verbose : NumMats := 30, MaxLen := 50);
perlist1 := [ ComputePeriodAlongWord(ModEC,form1,wrdlist[j]) : j in [1..#wrdlist]];
perlist2 := [ ComputePeriodAlongWord(ModEC,form2,wrdlist[j]) : j in [1..#wrdlist]];

mat := ZeroMatrix(RealField(50),#wrdlist,4);
for i in [1..#wrdlist] do
  mat[i][1] := Real(perlist1[i]);
  mat[i][2] := Imaginary(perlist1[i]);
  mat[i][3] := Real(perlist2[i]);
  mat[i][4] := Imaginary(perlist2[i]);
end for;

/* x1 = 11.9480803409898, x2 = 11.3098839568836.
   y1 = 6.89822740116975, y2 = 6.52976454701022
y1 = x1*sqrt(3)/3, x2/x1=y2/y1.

If 
K<a> := NumberField(x^2-x+1) and
E1 := EllipticCurve([1,-1,a,-26*a+12,161*a-50]),
with periods Omega_1 and Omega_2, then
42*Omega_1 = x2 + (3*y1+3*y2)*I = sqrt(-3)*x1 + (1+sqrt(-3))*x2
21*Omega_2 = -x1 + (3*y1+2*y2)*I = (-1+sqrt(-3))*x1 + (2*sqrt(-3)/3)*x2

basis1 = x1 + (1+sqrt(-3)/3)*x2 = (x1+x2)+(sqrt(-3)/3)*x2
basis2 = sqrt(-3)*x1 + (1+sqrt(-3))*x2 = x2+(x1+x2)*sqrt(-3)

general vector = c1*x1 + c1*x2 + c1*(sqrt(-3)/3)*x2
+ c2*x2 + c2*(x1+x2)*sqrt(-3)
= c1*x1 + (c1+c2)*x2 + c2*x1*sqrt(-3) + (c1/3+c2)*x2*sqrt(-3)

equivalently

a*x1 + b*x2 + c*x1*sqrt(-3) + d*x2*sqrt(-3)
must satisfy a + 3*c - 3*d = 0 and b + 2*c - 3*d = 0.

Matrix is
1.  [ 0 0 0 0 ]
2.  [ 0 0 0 0 ]
3.  [ 0 0 0 0 ]
4.  [ x1+x2 y1+y2 x2 -y2 ]
5.  [ x1 -y1 -3*x1-2*x2 -3*y1-2*y2 ]
6.  [ 0 0 0 0 ]
7.  [ 0 0 0 0 ]
8.  [ 0 0 0 0 ]
9.  [ -x1-x2 y1+y2 -x2 -y2 ]
10. [ -x1-2*x2 -3*y1 -3*x1-4*x2 -9*y1-6*y2 ]
11. [ -x1-x2 y1+y2 -x2 -y2 ]
12. [ -x1 y1 3*x1+2*x2 3*y1+2*y2 ]
13. [ x1+2*x2 3*y1+2*y2 3*x1+4*x2 3*y1 ]
14. [ -x1 y1 3*x1+2*x2 3*y1+2*y2 ]
15. [ x1 3*y1+2*y2 -3*x1-2*x2 3*y1 ]
16. [ -x1-x2 -3*y1-3*y2 -x2 3*y2 ]
17. [ -x1 -y1-2*y2 3*x1+2*x2 3*y1+4*y2 ]
18. [ 3*x1+3*x2 -y1-y2 3*x2 y2 ]
19. [ -x1 y1 3*x1+2*x2 3*y1+2*y2 ]
20. [ x1 -y1 -3*x1-2*x2 -3*y1-2*y2 ]
21. [ -x1 -y1 3*x1+2*x2 -3*y1-2*y2 ]
22. [ -x1 -y1-2*y2 3*x1+2*x2 3*y1+4*y2 ]
23. [ x2 2*y1+y2 3*x1+3*x2 3*y1+y2 ]
24. [ -2*x1-x2 2*y1+3*y2 3*x1+x2 -3*y1-5*y2 ]
25. [ 0 0 0 0 ]
26. [ -2*x1-x2 2*y1+3*y2 3*x1+x2 -3*y1-5*y2 ]
27. [ x1+x2 -y1-y2 x2 y2 ]
28. [ -x1 -y1 3*x1+2*x2 -3*y1-2*y2 ]
29. [ 0 0 0 0 ]
30. [ 0 -2*y1 0 -6*y1-4*y2 ]

*/

// Can we find alpha1 and alpha2 in K so that
// alpha1*form1 + alpha2*form2 has periods in the vector space whose
// general vector = c1*x1 + c1*x2 + c1*(sqrt(-3)/3)*x2 + c2*x2 + c2*(x1+x2)*sqrt(-3)
// = c1*x1 + (c1+c2)*x2 + c2*x1*sqrt(-3) + (c1/3+c2)*x2*sqrt(-3)

// A basis is [1,1,0,1/3] and [0,1,1,1]

// equivalently

// a*x1 + b*x2 + c*x1*sqrt(-3) + d*x2*sqrt(-3)
// must satisfy a + 3*c - 3*d = 0 and b + 2*c - 3*d = 0.

// periods for matrix4: 
// f1: [1,1,1/3,1/3]
// f1*sqrt(-3): [-1,-1,1,1]
// f2: [0,1,0,-1/3]
// f2*sqrt(-3): [0,1,0,1]

// 3*f1-f1*sqrt(-3)-f2+f2*sqrt(-3) works
// 3*f1+3*f1*sqrt(-3)+3*f2+f2*sqrt(-3) works too.

// periods for matrix5:
// f1: [1,0,-1/3,0]
// f1*sqrt(-3): [1,0,1,0]
// f2: [-3,-2,-1,-2/3]
// f2*sqrt(-3): [3,2,-3,-2]

// Again 3*f1-f1*sqrt(-3)-f2+f2*sqrt(-3) works.
// Again 3*f1+3*f1*sqrt(-3)+3*f2+f2*sqrt(-3) works.
// We could look at f1*sqrt(-3) + f2
// and 3*f1 + f2*sqrt(-3).

// Let's take f1*sqrt(-3) + f2

simplepers := [ perlist1[i]*Sqrt(CC!(-3)) + perlist2[i] : i in [1..#perlist1]];
pergens := [-simplepers[4],-simplepers[5]];
// x1 period and 2*x2 period.

xxx := jInvariant(pergens[2]/pergens[1]);
pol := PowerRelation(xxx,2);

// Roots are 1/343*(988929*a+1141344) and 1/343*(-988929*a+2130273)
// These match with elliptic curves with LMFDB label 441.2-a3 and 441.2-a4 over Q(omega).
// The match is with 441.2-a3.

// We have pergens = 21*Periods()[1].

// This checks out!
// Periods appear to be:
// 2*x1+2*x2+(2/3)*x2*sqrt(-3)
// -x1 + (2/3)*x2*Sqrt(-3)
// 5*x1+4*x2 - x1*Sqrt(-3) + (2/3)*x2*Sqrt(-3)
// 4*x1+2*x2 + ...
// All coefficients of x2 look to be even.

// Take the right square root of -3:
sqneg3 := 1 + 2*(K.1)^7;
ModEC`goodforms := [[form1[r]*sqneg3 + form2[r] : r in [1..numcusps]]];
ModEC`ECdegmap := AnalyticDegree(ModEC,ModEC`goodforms[1],pergens);
// Degree of map to EC is 6!
ModEC`nummaps := 1;

ModEC`pers := pergens;
ModEC`manin := [1/21];
aval := 1+(K.1)^7;

ModEC`Elist := [EllipticCurve([1,-1,aval,4*aval-3,-4*aval+1])];

// Step 6 - For each cusp and map, compute period integral from that cusp to the cusp at
// infinity. Take the image of this under the isomorphism C/Lambda -> E(C) and compute
// the image exactly as a point in E(Q(zeta_N)). We subtract by these points
// when making the map to the elliptic curve.

ModEC`translist := PerIntImages(ModEC);

// Step 7 - Tweak precision

ModEC`preclist, ModEC`maxdegree := TweakPrec(ModEC);

// Step 8 - Fourier expansions of maps to elliptic curve. Use the result of step 5. 
  
xfourierlist, yfourierlist, newprec, RR := FourierExpOfMaps(ModEC);
ModEC`xfourierlist := xfourierlist;
ModEC`yfourierlist := yfourierlist;
ModEC`newprec := newprec;
ModEC`RR := RR;

// Step 9 - Realize x and y modular functions in function field of modular curve over Q(zeta_N)
if not IgnoreBase then
  ecmaps, LMs, canring, cyclodegree := RealizeInFF(ModEC);
  ModEC`ecmaps := ecmaps;
  ModEC`LMs := LMs;
  ModEC`canring := canring;
  ModEC`cyclodegree := cyclodegree;
end if;

// Now that we have the map, coerce it into a subfield.

L := sub<Parent(aval) | aval>;
RRR<a,b,c> := PolynomialRing(L,3);
Lmaps := [];
for j in [1..3] do
  cofs, mons := CoefficientsAndMonomials(ecmaps[1][j]);
  Append(~Lmaps, &+[ L!cofs[i]*Evaluate(mons[i],[a,b,c]) : i in [1..#cofs]]);
end for;
EL := EllipticCurve([1,-1,L.1,4*L.1-3,-4*L.1+1]);
finalmap := map<BaseChange(ModEC`XG,L) -> EL | Lmaps>;
rnk, rnkchk := Rank(EL);
assert (rnk eq 0);
assert rnkchk;

T, tmap := TorsionSubgroup(EL);
torspoints := [tmap(t) : t in T];
for j in [1..#torspoints] do
  preim := torspoints[j]@@finalmap;
  printf "Points that are preimages of point %o of %o is %o.\n",j,#torspoints,RationalPoints(preim);
end for;

// There are precisely three rational points on X_G: (0 : 0 : 1), (-1 : 1 : 0) and (1 : 0 : 0).
// One of these is a rational cusp and the other two are CM points of discriminants
// -3 and -19.