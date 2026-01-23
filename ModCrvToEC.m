// Magma code to find maps from a modular curve to elliptic curves
// This version includes the algorithm by Ivan Novak to count CM points.

/* Helper function zone */

intrinsic PointsViaLifting(psi,p,m) -> SeqEnum
    { From David Zywina's OpenImage repository under the MIT License.
      Input:
            psi: a sequence of homogeneous polynomials in Z[x_1,...,x_r]
            p  : a prime
            m  : an integer at least one    
        Output:
            The set of points C(Z/p^m), where C is the subscheme of P^(r-1)_Q defined by psi.
    }    
    r:=Rank(Parent(psi[1]));
    PolZ<[x]>:=PolynomialRing(Integers(),r);
    psi:=[PolZ!f: f in psi];

    PP:=ProjectiveSpace(GF(p),r-1);
    C:=Scheme(PP,psi);
    S:={Eltseq(P): P in Points(C)};   // points mod p
    S:={[Integers()!a: a in P]: P in S};

    e:=1;
    while e lt m do
        PP:=ProjectiveSpace(Integers(p^(e+1)),r-1);
        Snew:={};        
        for P in S do
            // For each point in C(Z/p^e), we find all possible lifts to C(Z/p^(e+1)).
            A:=[]; b:=[];
            Pol<[a]>:=PolynomialRing(Integers(),r);
            for f in psi do
                pol:=Evaluate(f,[P[i]+p^e*a[i]: i in [1..r]]);
                A:=A cat [[MonomialCoefficient(pol,a[i]) div p^e : i in [1..r]]];
                b:=b cat [ -MonomialCoefficient(pol,1) div p^e ];
            end for;
            A:=ChangeRing(Matrix(A),GF(p));
            b:=ChangeRing(Vector(b),GF(p));
            flag,v,W:=IsConsistent(Transpose(A),b);
            if flag then 
                T:={Eltseq(v+w): w in W};
                T:={[Integers()!a: a in w] : w in T};
                T:={ [P[i]+p^e*w[i]: i in [1..r]] : w in T};
                T:={PP!w: w in T}; 
                Snew:=Snew join T;
            end if;
        end for;
        S:={Eltseq(P): P in Snew};
        S:={[Integers()!a: a in P]: P in S};
        e:=e+1;
    end while;

    S:={[Integers(p^m)!a: a in P] : P in S};
    return S;
end intrinsic;

/* Deprecated - This code was moved to the parser file and running script
// Selects a rational point on X_G; used to rationalize maps.
ChooseBasePt := function(ModEC)
  if ModEC`CheckLocal then
    if ModEC`Verbose then
      print "Checking for local obstructions";
    end if;
    if ModEC`MCR`genus ge 10 then
      print "Checking for local obstructions. This step may take a while since the genus is large.";
      print "Consider setting CheckLocal to false to skip this step.";
    end if;
    for p in PrimeDivisors(ModEC`N) do
      if #PointsViaLifting(ModEC`MCR`psi, p, ModEC`LocalExp) eq 0 then
        printf "The given modular curve has no %o-adic points.\n", p;
        return -1;
      end if;
    end for;
    if ModEC`Verbose then
      print "No local obstructions found";
    end if;
  end if;
  pts := PointSearch(ModEC`XG,1000);
  if #pts eq 0 then
    printf "No rational points found. This case not yet implemented.\n";
    assert false;
  else
    if ModEC`Verbose then
      print "Base point chosen.";
    end if;
  end if;
  // We choose the rational point with lowest height to be the base point.
  _, ind := Min([ Max([ Height(pts[i][j]) : j in [1..#Eltseq(pts[i])]]) : i in [1..#pts]]);
  return pts[ind];
end function; */

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

// Simplify a Q-vector space. This script takes a matrix M
// and finds the lattice of elements L where all the coordinates are integers.
// Then it finds an LLL-reduced basis for that lattice. It returns
// a square matrix that indicates which linear combinations of the rows of M
// are the LLL-reduced basis
function NicefyRat(ModEC, M)
  M0, T := EchelonForm(M);
  // Rows of T give current basis.
  ee := Eltseq(M0);
  denom := LCM([ Denominator(ee[i]) : i in [1..#ee]]);
  if ModEC`Verbose then
    printf "Nicefying %ox%o matrix.\n",NumberOfRows(M),NumberOfColumns(M);
  end if;
  M2 := Matrix(Integers(),NumberOfRows(M),NumberOfColumns(M),[ denom*ee[i] : i in [1..#ee]]);
  AA := Saturation(M2);
  chk, mult := IsConsistent(ChangeRing(M2,Rationals()),ChangeRing(AA,Rationals()));
  curbat := denom*mult*T;
  newlatbasismat, change := LLL(AA : Proof := false);
  finalbat := ChangeRing(change,Rationals())*curbat;
  return finalbat;
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

// Given an isogeny class, sign of discriminant, and approximate periods of an 
// elliptic curve, try to determine the elliptic curve and the Manin constant.
// In this function we assume that the numerator of the Manin constant is 1.
IdentifyEC := function(iso, sgn, per)
    for E in iso do
        if Sign(Discriminant(E)) eq sgn then
            Ratios := [per[i] / Periods(E)[i] : i in [1,2]];
            if Maximum([AbsoluteValue(Imaginary(z)) : z in Ratios]) le 0.01 then
                r := [Round(Real(Ratios[i])) : i in [1,2]];
                // r := [BestApproximation(Real(Ratios[i]),1000) : i in [1,2]];
                    if r[1] eq r[2] then
                        return E, r[1];
                    end if;
            end if;
        end if;
    end for;
    "Failed to identify the curve";
    assert false;
end function;

// The function below takes an elliptic curve E and a positive integer n
// and returns a polynomial whose roots are the x-coordinates of points of exact order n
// on E.
PrimitiveDivisionPolynomial := function(E,n)
  FF := FunctionField(BaseRing(E));
  ret := &*[ (FF!DivisionPolynomial(E,r))^(MoebiusMu(n div r)) : r in Divisors(n) | (r gt 1) ];
  return Numerator(ret);
end function;

// Build the modular curve record MCR (and related fields) at a precision
// sufficient for later analytic estimates, scaling by precmult. These parameters scale the default power series precision.
CreateModCrvWithPrec := function(ModEC,precmult)
  // Choose power series precision fairly carefully.
  // What if we assume that the coefficient of q^(n/sl2level) of
  // the eigenform is bounded by 3*N*d(n)*sqrt(n)?
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
  if ModEC`Verbose then
    printf "Choosing power series precision = %o.\n",prec;
  end if;
  // This is the precision in q^(1/N) that we need at the cusp at infinity.

  G := GL(2,Integers(ModEC`N));
  genlist := [ G!s : s in ModEC`gens];

  if ModEC`Verbose then
    printf "Creating model with power series precision %o.\n", prec;
  end if;

  MCR := CreateModularCurveRec(ModEC`N, genlist);
  MCR := FindModelOfXG(MCR);
  if ModEC`Verbose then
    printf "Model found. Now increasing precision.\n";
  end if;

  MCR := IncreaseModularFormPrecision(MCR, prec);
  if ModEC`Verbose then
    printf "Precision increase done.\n";
  end if;
  // Fourier expansion at cusps is given in terms of qw, which is q^(1/w).
  // The absolute precision is q^(prec/sl2level).
  return EXP, prec, MCR;
end function;

// Find a basis of the Hecke eigen subspace
FindEigenformBasis := function(ModEC)

  MCR := ModEC`MCR;
  ret := <>;

  curp := 0;
  I := IdentityMatrix(Rationals(), MCR`genus);
  for r in [1..#ModEC`ainvlist] do
    sub := RSpace(Rationals(), MCR`genus);
    while Dimension(sub) gt ModEC`multlist[r] do
      repeat
          curp := NextPrime(curp);
      until GCD(curp, ModEC`N) eq 1;

      HM := HeckeMatrix(MCR`F0, ModEC`N, curp, ModEC`preclist, ModEC`Verbose)[1];
      tr := TraceOfFrobenius(EllipticCurve(ModEC`ainvlist[r]), curp);
      sub := sub meet NullSpace(HM - tr*I);
    end while;
    Append(~ret,Basis(sub));  
  end for;

  return ret;
end function;


// Identify weight 2 cusp forms with correct Hecke eigenvalues
GoodForms := function(ModEC)
  cuspforms := ModEC`MCR`F0;
  genus := ModEC`MCR`genus;
  numcusps := #ModEC`MCR`cusps;
  ret := [];
  for r in [1..#ModEC`B] do
    Bmat := Matrix(ModEC`B[r]);
    for i in [1..#ModEC`B[r]] do
      formfourier := [ &+[ Bmat[i][j]*cuspforms[j][k] : j in [1..genus]] : k in [1..numcusps]];
      vec := &cat [ &cat [ Eltseq(Coefficient(formfourier[k],j)) : j in [1..ModEC`preclist[k]-1]] : k in [1..numcusps]];
      if (i eq 1) then
        FM := Matrix(Rationals(),1,#vec,vec);
      else
        FM := VerticalJoin(FM,Matrix(Rationals(),1,#vec,vec));
      end if;    
    end for;
    nf := NicefyRat(ModEC,FM);
    if NumberOfColumns(nf) ne NumberOfRows(Bmat) then
      printf "Failed to correctly identify Hecke eigenforms.\n";
      printf "Rerun with a larger value of precmult.\n";
      assert false;
    end if;
    formmat := nf*Bmat;
    // nf*FM is the matrix whose rows are the good Fourier expansions.
    goodforms := [];
    for i in [1..ModEC`nummaps] do
      fe := [ &+[ formmat[i][j]*cuspforms[j][k] : j in [1..genus]] : k in [1..numcusps]];
      Append(~goodforms,fe);
    end for;
    Append(~ret,goodforms);
  end for;    
  return ret;
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

// Diagnostic to check the size of the Fourier coefficients.
CheckFourierCoeffSizes := function(ModEC);
  if ModEC`Verbose then
    printf "Fourier coefficient size diagnostic.\n";
  end if;
  mx := 0;
  NN := ModEC`MCR`gl2level;
  for r in [1..#ModEC`ainvlist] do
    for i in [1..#ModEC`goodforms[r]] do
      for j in [1..#ModEC`MCR`cusps] do
        wid := ModEC`MCR`widths[j];
        sizes := [ AbsoluteValue(Conjugates(Coefficient(ModEC`goodforms[r][i][j],t))[1])/(NumberOfDivisors(Integers()!(t*NN/wid))*(t*NN/wid)^(1/2)) : t in [1..ModEC`preclist[j]-1]];      
      end for;
      mx := Max(mx,Max(sizes));
    end for;
  end for;   
  return mx;
end function;

// Write a complex number z in the form a*omega_1 + b*omega_2
// where the coefficients are rational of small height.
RatLatApx := function(bas, z, decprec, i, k)
  b := Imaginary(z)/Imaginary(bas[2]);
  a := Real(z-b*bas[2])/Real(bas[1]);
  a2 := BestApproximation(a,100);
  b2 := BestApproximation(b,100);
  chk := z - a2*bas[1] - b2*bas[2];
  if AbsoluteValue(chk) gt 10^(-(decprec-3)) then
    printf "Rational identification error with map = %o, cusp = %o.\n",i,k;
    assert false;
  end if;
  return a2, b2;
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

// We use a formula from https://dlmf.nist.gov/23.9 for the Fourier expansion of the Weierstrass p-function:
// p(z) = (1/z^2) + z^2 * sum (d_k * z^(2*k))/k!.
// Here d_0 = 3G_4, d_1 = 5G_6 and there's a recurrence relation given there. First, let's calculate the d's
WeierstrassP := function(a, b, prec, zz)
  dlist := [-a/5,-b/7];
  for n in [0..Floor(prec/2)] do
    // Compute d_(n+2) using a formula from https://dlmf.nist.gov/23.9.
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
    tm := Realtime();
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
    n2 := Round(Imaginary(rawper)/Imaginary(pergens[2]));
    n1 := Round(Real((rawper-pergens[2]*n2)/pergens[1]));
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
    print "Time to compute analytic modular degree:", Realtime(tm);
  end if;
  return ret;
end function;

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
      // This part will need to be updated to support nummaps > 1.
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

// Decrease power series precision as appropriate, but only enough to ensure
// we have enough precision to certify the map to the elliptic curve.
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
  precsum := ((3*maxr*ModEC`MCR`k)/12)*ModEC`MCR`index+2;
  multiplier := &+[ ModEC`MCR`widths[r]/ModEC`MCR`sl2level : r in [1..numcusps]];
  powerprec := Ceiling(precsum/multiplier)+9;
  if ModEC`Verbose then
    printf "precsum = %o, multiplier = %o, powerprec = %o.\n",precsum,multiplier,powerprec;
  end if;
  if (powerprec gt ModEC`prec) then
    printf "The precision currently available is %o, but the needed precision is %o.\n",ModEC`prec,powerprec;
    printf "Try rerunning this case with precmult = %o.\n",RealField(5)!(0.1+powerprec/ModEC`prec);
    assert false;  
  end if;
  preclist := [Max(Ceiling(Min(powerprec,ModEC`prec)*ModEC`MCR`widths[i]/ModEC`MCR`sl2level),2) : i in [1..numcusps]];
  if ModEC`Verbose then
    printf "Setting powerprec = %o.\n",Min(powerprec,ModEC`prec);
    printf "New preclist = %o.\n",preclist;
  end if;
  return preclist, maxr;
end function;

// Compute exact points on EK coming from the period integrals.
PerIntImages := function(ModEC)
  numcusps := #ModEC`MCR`cusps;
    translist := <>;
    RtsCache := AssociativeArray();
    for i in [1..ModEC`nummaps] do
      mapilist := [];
      EK := BaseChange(ModEC`Elist[i], ModEC`K);
      for k in [1..numcusps] do
        curper := PeriodIntegralFromCusp(ModEC, ModEC`goodforms[i],[ModEC`MCR`cusps[k][1][1], ModEC`MCR`cusps[k][2][1]]);
        // Now write curper = a*pers[i][1] + b*pers[i][2]
        a2, b2 := RatLatApx(ModEC`pers[i], curper, ModEC`decprec, i, k);
        //printf "We found that the point is %o*omega_1 + %o*omega_2.\n",a2,b2;
        // phiK := InfinitePlaces(K)[1];
        // Now we have a complex approximation for the point we seek. We need the coordinates
        // of this in Q(zeta_N)
        ECpt2, RtsCache := MatchPtOnEC(EK, ModEC`Elist[i], ModEC`psiCF, a2, b2, ModEC`decprec, RtsCache, k, ModEC`Verbose);
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
    _, scal := IsPower(MonomialCoefficient(des[2],PP.2),3);

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
  if ModEC`Verbose then
    printf "Realizing x,y over cyclotomic field.\n";
    tm := Realtime();
  end if;
  numcusps := #ModEC`MCR`cusps;
  polyring := PolynomialRing(ModEC`K,#ModEC`genforms,"grevlex");
  vars := [ polyring.i : i in [1..#ModEC`genforms]];
  gens := [ Evaluate(ModEC`MCR`psi[j],vars) : j in [1..#ModEC`MCR`psi]];
  ttemp := Realtime();
  if ModEC`Verbose then
    printf "Computing Grobner basis for ideal.\n";
  end if;
  I := ideal<polyring | gens>;
  G := GroebnerBasis(I);
  gbtime := Realtime(ttemp);
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
        mat := ZeroMatrix(ModEC`K,0,2*&+[ ModEC`newprec[ii][r] : r in [1..numcusps]]);
        for i in [1..#canring[d][1]] do
          pre := Realtime();
          pp := [ ModEC`xfourierlist[ii][r]*canring[d][1][i][r] : r in [1..numcusps]];
          pp2 := [ ModEC`yfourierlist[ii][r]*canring[d][1][i][r] : r in [1..numcusps]];
          post := Realtime(pre);
          vecseq := &cat [ [ Coefficient(pp[r],m) : m in [Valuation(ModEC`xfourierlist[ii][r])..Valuation(ModEC`xfourierlist[ii][r])+ModEC`newprec[ii][r]-1]] : r in [1..numcusps]];
          vecseq2 := &cat [ [ Coefficient(pp2[r],m) : m in [Valuation(ModEC`yfourierlist[ii][r])..Valuation(ModEC`yfourierlist[ii][r])+ModEC`newprec[ii][r]-1]] : r in [1..numcusps]];
          pre := Realtime();
          mat := VerticalJoin(mat,Matrix(ModEC`K,1,#vecseq+#vecseq2,vecseq cat vecseq2));
          post := Realtime(pre);
        end for;
        for i in [1..#canring[d][1]] do
          vecseq := &cat [ [ Coefficient(canring[d][1][i][r],m) : m in [Valuation(ModEC`xfourierlist[ii][r])..Valuation(ModEC`xfourierlist[ii][r])+ModEC`newprec[ii][r]-1]] : r in [1..numcusps]];
          vecseq2 := &cat [ [ ModEC`K!0 : m in [Valuation(ModEC`yfourierlist[ii][r])..Valuation(ModEC`yfourierlist[ii][r])+ModEC`newprec[ii][r]-1]] : r in [1..numcusps]];
          pre := Realtime();
          mat := VerticalJoin(mat,Matrix(ModEC`K,1,#vecseq+#vecseq2,vecseq cat vecseq2));
          post := Realtime(pre);
        end for;
        for i in [1..#canring[d][1]] do
          vecseq := &cat [ [ ModEC`K!0 : m in [Valuation(ModEC`xfourierlist[ii][r])..Valuation(ModEC`xfourierlist[ii][r])+ModEC`newprec[ii][r]-1]] : r in [1..numcusps]];
          vecseq2 := &cat [ [ Coefficient(canring[d][1][i][r],m) : m in [Valuation(ModEC`yfourierlist[ii][r])..Valuation(ModEC`yfourierlist[ii][r])+ModEC`newprec[ii][r]-1]] : r in [1..numcusps]];
          pre := Realtime();
          mat := VerticalJoin(mat,Matrix(ModEC`K,1,#vecseq+#vecseq2,vecseq cat vecseq2));
          post := Realtime(pre);
        end for;
        pre := Realtime();
        NN2 := NullSpace(mat);
        nulltime := Realtime(pre);
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

  if ModEC`Verbose then
    print "Time to realize x,y over cyclotomic field:", Realtime(tm);
  end if;

  return ecmaps, LMs, canring, ModEC`cyclodegree;
end function;

// Translate the Fourier expansions of x,y so that the chosen base 
// point maps to the point at infinity on E.
TransByBasePt := function(ModEC)
  numcusps := #ModEC`MCR`cusps;
  newxfourierlist := [];
  newyfourierlist := [];
  newprec2 := [];
  for ii in [1..ModEC`nummaps] do
    if ModEC`Verbose then
      printf "Starting cyclotomic map evaluation.\n";
    end if;
    mapcyclo := map<BaseChange(ModEC`XG,ModEC`K) -> ModEC`Elist[ii] | ModEC`ecmaps[ii] : Check := false>;
    // We assume this map works. We'll check it, and get a prettier equation for it later.
    baseim := mapcyclo(Domain(mapcyclo)!Eltseq(ModEC`BasePt));
    chk := IsCoercible(ModEC`Elist[ii](ModEC`K),Eltseq(baseim));
    assert chk;
    if ModEC`Verbose then
      printf "Map %o goes from XG to curve %o. Base point %o maps to %o.\n",ii,aInvariants(ModEC`Elist[ii]),ModEC`BasePt,baseim;
    end if;

    transpt := -baseim;
    xf := [];
    yf := [];
    np := [];
    for r in [1..numcusps] do
      xfourier := ModEC`xfourierlist[ii][r];
      yfourier := ModEC`yfourierlist[ii][r];      
      if Order(transpt) eq 1 then
        newxfourier := xfourier;
        newyfourier := yfourier;
      else
        //printf "xfourier = %o.\n",xfourier;
        //printf "yfourier = %o.\n",yfourier;
        //printf "transpt = %o.\n",transpt;
        if IsWeaklyZero(xfourier-transpt[1]) then
          PS := Parent(xfourier);
          newxfourier := O(PS.1^0);
          newyfourier := O(PS.1^0);
        else
          lam := (yfourier-transpt[2])/(xfourier-transpt[1]);
          nu := (transpt[2]*xfourier-yfourier*transpt[1])/(xfourier-transpt[1]);
          ainvi := aInvariants(ModEC`Elist[ii]);
          newxfourier := lam^2 + ainvi[1]*lam - ainvi[2] - transpt[1]- xfourier;
          newyfourier := -(lam + ainvi[1])*newxfourier - nu - ainvi[3];
        end if;  
      end if;
      Append(~np,Min(RelativePrecision(newxfourier),RelativePrecision(newyfourier)));      
      Append(~xf,newxfourier);
      Append(~yf,newyfourier);
    end for;
    Append(~newxfourierlist,xf);
    Append(~newyfourierlist,yf);
    Append(~newprec2,np);
  end for;
  return newxfourierlist, newyfourierlist, newprec2;
end function;

// A function to check if a modular form with given Fourier expansions is zero or not
CheckFourier := procedure(fourierlist,weight,index)
  numcusps := #fourierlist;
  precsum := 0;
  for r in [1..numcusps] do
    if not IsWeaklyZero(fourierlist[r]) then
      printf "Error in FourierCheck. The map doesn't work or compatibility fails.\n";
      assert false;
    end if;
    precsum := precsum + AbsolutePrecision(fourierlist[r]);            
  end for;
  precneeded := (weight/12)*index;
  if precsum le precneeded then 
    printf "Error in FourierCheck. Not enough power series precision to prove form vanishes.\n";
    assert false;
  end if;
end procedure;

// Re-run the linear algebra of RealizeInFF over Q (instead of K)
// to produce a rational map X_G --> E.
MapOverQ := function(ModEC)
  if ModEC`Verbose then
    print "Realizing x,y over rationals.";
    tm := Realtime();
  end if;
  numcusps := #ModEC`MCR`cusps;
  polyring := PolynomialRing(Rationals(),#ModEC`genforms,"grevlex");
  if ModEC`IgnoreBase then
    canring := <>;
    ModEC`newxfourierlist := ModEC`xfourierlist;
    ModEC`newyfourierlist := ModEC`yfourierlist;
    ModEC`newprec2 := ModEC`newprec;    
    vars := [ polyring.i : i in [1..#ModEC`genforms]];
    gens := [ Evaluate(ModEC`MCR`psi[j],vars) : j in [1..#ModEC`MCR`psi]];
    ttemp := Realtime();
    if ModEC`Verbose then
      printf "Computing Grobner basis for ideal.\n";
    end if;
    I := ideal<polyring | gens>;
    G := GroebnerBasis(I);
    gbtime := Realtime(ttemp);
    if ModEC`Verbose then
      printf "Grobner basis time was %o.\n",gbtime;
    end if;
    LMs := [ LeadingMonomial(G[i]) : i in [1..#G]];
    initideal := ideal<polyring | LMs>;
  else
    canring := ModEC`canring;
    vars := [ polyring.i : i in [1..#ModEC`genforms]];
    initideal := ideal<polyring | [polyring!mm : mm in ModEC`LMs]>;
  end if;

  if ModEC`Verbose then
    printf "Generating rational canonical ring.\n";
  end if;

  donelist := [ false : i in [1..ModEC`nummaps]];
  // Tweak to check d = 1 case.
  d := 0;
  ecmaps := [ [] : i in [1..ModEC`nummaps]];
  while not (&and donelist) do
    d := d + 1;
    if #canring lt d then
      if ModEC`Verbose then
        printf "Generating degree %o piece of canonical ring.\n",d;
      end if;
      if (d gt ModEC`maxdegree) then
        printf "If the map exists, it should have been found by this point.\n";
        assert false;
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
          ind := Index([ IsDivisibleBy(curmon,polyring!canring[d-1][2][k]) : k in [1..#canring[d-1][2]]],true);
          chk, q := IsDivisibleBy(curmon,polyring!canring[d-1][2][ind]);
          ind2 := Index(vars,q);
          newprd := [ModEC`RR!(ModEC`genforms[ind2][r]*(canring[d-1][1][ind][r])) : r in [1..numcusps]];
          Append(~newfourier,newprd);
          Append(~newvars,curmon);
        end for;  
      end if;
      Append(~canring,<newfourier,newvars>);
    else
      bas := canring[d][2];
    end if;  

    for ii in [1..ModEC`nummaps] do
      if (not donelist[ii] and (d ge ModEC`maxdegree - 1) and ((not assigned ModEC`cyclodegree) or (d ge ModEC`cyclodegree))) then
        if ModEC`Verbose then
          printf "Searching for map %o of %o in degree %o.\n",ii,ModEC`nummaps,d;
        end if;
        mat := ZeroMatrix(Rationals(),0,(2*&+[ ModEC`newprec2[ii][r] : r in [1..numcusps]])*Degree(ModEC`K));
        for i in [1..#canring[d][1]] do
          pp := [ ModEC`newxfourierlist[ii][r]*canring[d][1][i][r] : r in [1..numcusps]];
          pp2 := [ ModEC`newyfourierlist[ii][r]*canring[d][1][i][r] : r in [1..numcusps]];      
          vecseq := &cat [ &cat [ Eltseq(Coefficient(pp[r],m)) : m in [Valuation(ModEC`newxfourierlist[ii][r])..Valuation(ModEC`newxfourierlist[ii][r])+ModEC`newprec2[ii][r]-1]] : r in [1..numcusps]];
          vecseq2 := &cat [ &cat [ Eltseq(Coefficient(pp2[r],m)) : m in [Valuation(ModEC`newyfourierlist[ii][r])..Valuation(ModEC`newyfourierlist[ii][r])+ModEC`newprec2[ii][r]-1]] : r in [1..numcusps]];
          mat := VerticalJoin(mat,Matrix(Rationals(),1,#vecseq+#vecseq2,vecseq cat vecseq2));
        end for;
        for i in [1..#canring[d][1]] do
          vecseq := &cat [ &cat [ Eltseq(Coefficient(canring[d][1][i][r],m)) : m in [Valuation(ModEC`newxfourierlist[ii][r])..Valuation(ModEC`newxfourierlist[ii][r])+ModEC`newprec2[ii][r]-1]] : r in [1..numcusps]];
          vecseq2 := &cat [ &cat [ Eltseq(ModEC`K!0) : m in [Valuation(ModEC`newyfourierlist[ii][r])..Valuation(ModEC`newyfourierlist[ii][r])+ModEC`newprec2[ii][r]-1]] : r in [1..numcusps]];
          mat := VerticalJoin(mat,Matrix(Rationals(),1,#vecseq+#vecseq2,vecseq cat vecseq2));
        end for;
        for i in [1..#canring[d][1]] do
          vecseq := &cat [ &cat [ Eltseq(ModEC`K!0) : m in [Valuation(ModEC`newxfourierlist[ii][r])..Valuation(ModEC`newxfourierlist[ii][r])+ModEC`newprec2[ii][r]-1]] : r in [1..numcusps]];
          vecseq2 := &cat [ &cat [ Eltseq(Coefficient(canring[d][1][i][r],m)) : m in [Valuation(ModEC`newyfourierlist[ii][r])..Valuation(ModEC`newyfourierlist[ii][r])+ModEC`newprec2[ii][r]-1]] : r in [1..numcusps]];
          mat := VerticalJoin(mat,Matrix(Rationals(),1,#vecseq+#vecseq2,vecseq cat vecseq2));
        end for;
        if ModEC`Verbose then
            printf "Matrix size is %o x %o.\n",NumberOfRows(mat),NumberOfColumns(mat);
        end if;
        NN2 := NullSpace(mat);
        dimdim2 := Dimension(NN2);
        if ModEC`Verbose then
          printf "For d = %o, dimension of null space is %o.\n",d,dimdim2;
        end if;
        if (dimdim2 eq 0) and (d ge ModEC`maxdegree) then
          printf "If the map exists, it should have been found by now!\n";
          assert false;
        end if;
        if dimdim2 ge 1 then
          donelist[ii] := true;
          nullmat2 := Matrix(Basis(NN2));
          change2 := NicefyRat(ModEC,nullmat2);
          ecmapii := [];
          fouriermaps := [];
          precchecking := [];
          ecpoly := DefiningPolynomial(ModEC`Egiven);
          for j in [1..Min(dimdim2,5)] do
            v2 := (change2*nullmat2)[j];
            curmap3 := &+[ v2[i]*bas[i] : i in [1..#bas]];
            curmap1 := -&+[ v2[i+#bas]*bas[i] : i in [1..#bas]];
            curmap2 := -&+[ v2[i+2*#bas]*bas[i] : i in [1..#bas]];
            Append(~ecmapii,[curmap1,curmap2,curmap3]);            
            zfouriermap := [&+[ v2[i]*canring[d][1][i][r] : i in [1..#bas]] : r in [1..numcusps]];
            xfouriermap := [-&+[ v2[i+#bas]*canring[d][1][i][r] : i in [1..#bas]] : r in [1..numcusps]];
            yfouriermap := [-&+[ v2[i+2*#bas]*canring[d][1][i][r] : i in [1..#bas]] : r in [1..numcusps]];
            mapstoec := [ Evaluate(ecpoly,[xfouriermap[r],yfouriermap[r],zfouriermap[r]]) : r in [1..numcusps]];
            if ModEC`Verbose then
              printf "Checking map equation %o of %o.\n",j,Min(dimdim2,5);
            end if;
            CheckFourier(mapstoec,3*d*ModEC`MCR`k,ModEC`MCR`index);
            Append(~fouriermaps,[xfouriermap,yfouriermap,zfouriermap]);
            for l in [1..j-1] do
              if ModEC`Verbose then
                printf "Checking compatability of map equation %o and %o.\n",l,j;
              end if;
              xcheck := [fouriermaps[l][1][r]*zfouriermap[r] - fouriermaps[l][3][r]*xfouriermap[r] : r in [1..numcusps]];
              CheckFourier(mapstoec,2*d*ModEC`MCR`k,ModEC`MCR`index);
              ycheck := [fouriermaps[l][2][r]*zfouriermap[r] - fouriermaps[l][3][r]*yfouriermap[r] : r in [1..numcusps]];
              CheckFourier(mapstoec,2*d*ModEC`MCR`k,ModEC`MCR`index);
            end for;
          end for;
          ecmaps[ii] := ecmapii;  
        end if;
      end if;  
    end for;  
  end while;
  if ModEC`Verbose then
    print "Time to realize x,y over rationals:", Realtime(tm);
  end if;
  return ecmapii;
end function;

// Builds Magma maps X_G --> E, which verifies the maps are non-constant.
// This function is no longer used. It is an alternative to the code 
// that is actually used in MapOverQ.
CheckMaps := function(ModEC)
  maplst := <>;
  for ii in [1..ModEC`nummaps] do
    if ModEC`Verbose then
      printf "Checking the map is non-constant.\n";
    end if;
    mapchk := map<ModEC`XG -> ModEC`Elist[ii] | ModEC`ecmaps[ii] : Check := false>;
    preiminf := (Codomain(mapchk)![0,1,0])@@mapchk;
    if ModEC`Verbose then
      print "Dimension of preimage: ", Dimension(preiminf);
    end if;
    assert Dimension(preiminf) eq 0;
  end for;  
  return <mapchk>;
end function;

/* Main functions */

// Our new, mostly custom function for pulling back rational points. The input is the level N,
// and a map from X_G -> E where E(Q) has rank zero. The function computes all rational preimages on X_G
// of torsion points on E.

// The optional parameter Verbose provides information about what is going on.

// Step A - Reduce zero-dimensional scheme X mod primes that don't divide the level and count points mod p
// and count singular points.

// Step B - If we find a prime with no singular points, then every point in X(Q_p) is a lift of
// a point in X(F_p). We lift the points mod p to points mod p^k for some k with p^k around 10^20. Then see if we get
// a rational point on the scheme. This should find all the rational points.

// Step C - Keep testing primes to see if we can find one for which we get equality
// in the number of mod p points and the rational points we have found. If we do, we're done.

// Step D - In the event that we can't find a prime with no singular points, or
// we can't get equality in step 3, then fall back to Magma's built-in "RationalPoints" function, which
// can involve expensive Groebner basis computations for ridiculous zero-dimensional schemes.

// Step 13 - Determine the rational points on X_G
// In our main run, this is called in the parser file.
intrinsic RatPtsFromMaps(N::RngIntElt, mps::Tup : Verbose := false) -> SeqEnum
  {Pulls back points on a rank 0 elliptic curve to provably determine all rational points on the modular curve (the domain of the maps). This custom method uses reduction mod p, Hensel lifting, and rational reconstruction; for low genus curves, naive point-pullback also works.}

  if Verbose then
    print "Pulling back points";
    tm := Realtime();
  end if;
  allXpoints := [];
  for phi in mps do
    E := Codomain(phi);
    assert Rank(E) eq 0;
    if Verbose then
      print "The codomain of the map is a rank 0 elliptic curve:", aInvariants(E);
    end if;
    T, psi := TorsionSubgroup(E);
    ptsE := {psi(P) : P in T};
    if Verbose then
      print "The set of rational points of this elliptic curve is:";
    end if;
    X := Domain(phi);
    for P in ptsE do
      if Verbose then
        printf "Pulling back point %o.\n",P;
      end if;
      X2 := P@@phi;
      sing := true;
      maxpts := -1;
      polylist := Generators(Ideal(X2));
      polylist2 := [];
      numvars := Rank(Parent(polylist[1]));
      foundall := false;
      foundpoints := [];
      for q in polylist do
        denom := LCM([ Denominator(c) : c in Coefficients(q)]);
        Append(~polylist2,denom*q);
      end for;
      curp := 1;
      step2done := false;
      while (step2done eq false) do
        curp := NextPrime(curp);
        if (GCD(curp,N) eq 1) then
          X2p := ChangeRing(Scheme(Ambient(X2),polylist2),GF(curp));
          if Dimension(X2p) eq 0 then
            pts := Points(X2p);
            singpts := [ i : i in [1..#pts] | IsSingular(pts[i])];
            //printf "Testing p = %o. There are %o points, of which %o are singular.\n",curp,#pts,#singpts;
            if #singpts eq 0 then
              sing := false;
              step2done := true;
              if (maxpts eq -1) then
                maxpts := #pts;
              else
                maxpts := Min(maxpts,#pts);
              end if;
              // Do Hensel lifting to search for rational points with height <= 10^6 or so.
              Qp := pAdicField(curp : Precision := 50);
              RR := PolynomialRing(Qp,numvars);
              vars := [RR.i : i in [1..numvars]];
              neweq := [ Evaluate(polylist2[i],vars) : i in [1..#polylist2]];
              for pp in pts do
                if Verbose then
                  printf "Lifting mod p point %o.\n",pp;
                end if;
                modppoint := [ elt<Qp | Integers()!Eltseq(pp)[j], 1> : j in [1..#Eltseq(pp)]];
                liftexp := Ceiling(12*Log(10)/Log(curp))+1;
                padicpoint := LiftPoint(neweq,1,modppoint,liftexp);
                //printf "p-adic point is %o.\n",padicpoint;
                chk := true;
                ratpt := [];
                for l in [1..#padicpoint] do
                  chk2, recon := RationalReconstruction(Integers(curp^liftexp)!(Integers()!padicpoint[l]));
                  chk := chk and chk2;
                  if chk2 then
                    Append(~ratpt,recon);
                  end if;
                end for;
                if chk then
                  //printf "Rational reconstruction is %o.\n",ratpt;
                  chk, Xpoint := IsCoercible(X,ratpt);
                  if chk then
                    if Verbose then
                      printf "We found a rational point %o.\n",Xpoint;
                    end if;
                    Append(~foundpoints,Xpoint);
                  else
                    if Verbose then
                      printf "We didn't find a rational point.\n";
                    end if;
                  end if;
                else
                  if Verbose then
                    printf "We didn't find a rational point.\n";
                  end if;
                end if;
              end for;
            end if;  
          end if;  
        end if;
        if (curp gt 101) then
          step2done := true;
        end if;
      end while;
      // Step 3 - Search for a prime for which #X(F_p) equals the number of points we
      // have found so far.
      if (sing eq false) then
        step3done := false;
        while (step3done eq false) do
          if (GCD(curp,N) eq 1) then
            X2p := ChangeRing(Scheme(Ambient(X2),polylist2),GF(curp));
            if Dimension(X2p) eq 0 then
              pts := Points(X2p);
              singpts := [ i : i in [1..#pts] | IsSingular(pts[i])];
              if #singpts eq 0 then
                if Verbose then
                  printf "Mod %o there are %o points, all of which are non-singular.\n",curp,#pts;
                end if;
                maxpts := Min(maxpts,#pts);
                if maxpts eq #foundpoints then
                  foundall := true;
                  step3done := true;  
                  if Verbose then
                    printf "The reduction mod p map from X(Q) -> X(F_%o) is bijective. We're done!\n",curp;
                  end if;

                end if;
              end if;  
            end if;  
          end if;
          curp := NextPrime(curp);
          if (curp gt 400) then
            step3done := true;
          end if;
        end while;  
      end if;
      // Step 4
      if (foundall eq false) then
        if (sing eq true) then
          if Verbose then
            printf "Fall back to built-in function - no non-singular reduction found.\n";
          end if;
        end if;
        if (sing eq false) then
          if Verbose then
            printf "Fall back to built-in function - no p for which #X(F_p) matches number of known rational points found.\n";
          end if;
        end if;
        pts := RationalPoints(X2);
        for P in pts do
          Append(~foundpoints,X!Eltseq(P));
          if Verbose then
            printf "Found rational point %o.\n",P;
          end if;
        end for;
      end if;
      for P in foundpoints do
        Append(~allXpoints,X!Eltseq(P));
      end for;
    end for;   
  end for;
  if #allXpoints gt 0 then
    allXpoints := SetToSequence(SequenceToSet(allXpoints));
  end if;
  if Verbose then
    if #allXpoints eq 0 then
      printf "There are no rational points on the given modular curve.\n";
      else
        if #allXpoints eq 1 then
            printf "There is %o rational point on the given modular curve.\n",#allXpoints;
            printf "It is %o.\n",allXpoints;
          else
            printf "There are %o rational points on the given modular curve.\n",#allXpoints;
            printf "They are %o.\n",allXpoints;
        end if;
    end if;
  end if;
  if Verbose then
    print "Time to pull back points:", Realtime(tm);
  end if;
  return allXpoints;
end intrinsic;

// Build and populate the ModEC record as needed for FindMapsToEC and EllipticCurveQuoCandidates.
// This calls David Zywina's code for computing models of modular curves and modular forms.
// There are three optional parameters:
// 1. decprec - The decimal precision desired for period computations. By default this is set to 10, and the function
// tries to pick enough power series precision to ensure the comptuations are roughly accurate to that many decimal places.
// 2. precmult - This parameter (which defaults to 1) allows the user to increase the power series precision by a given
// factor. Sometimes the script will inform the user more precision is needed.
// 3. Verbose - This defaults to false, but when set to true it provides a lot of information about what is going on in
// each step of the computation. 

// Step 1. Compute modular forms and a model of X_G
// In our main run, this is called in the parser file.
// After this function is called, we do Step 2: Test 
// local solvability and find a rational base point.
intrinsic InitializeModEC(N::RngIntElt, gens::SeqEnum : decprec := 5, precmult := 1, Verbose := false) -> Rec
  {Prepares a ModEC record that is used for FindMapsToEC and EllipticCurveQuoCandidates.}
  // This is the main record format we'll use.
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
    newxfourierlist, newyfourierlist, newprec2,
    ModelMCR, jmap
  >;
  transposegens := [ [a[1],a[3],a[2],a[4]] : a in gens ];
  // David Zywina's code has an "opposite" modular intepretation to that of the LMFDB.
  // For consistency with the LMFDB we take a transpose here.
  ModEC := rec<RecModEC | N := N, gens := transposegens, decprec := decprec, precmult := precmult, Verbose := Verbose>;

  SetKantPrecision(2 * decprec);
  ModEC`C := ComplexField(2 * decprec);
  EXP, prec, MCR := CreateModCrvWithPrec(ModEC,precmult);
  ModEC`EXP := EXP; 
  ModEC`prec := prec;
  ModEC`MCR := MCR; 
  ModEC`ModelMCR := MCR;
  ModEC`ModelMCR`prec := MCR`prec;
  ModEC`ModelMCR`F0 := MCR`F0;  
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
  return ModEC;
end intrinsic;

// This function determines a list of candidates for elliptic curves that X_G could map to by considering
// the action of Hecke operators. The input is a ModEC record, and the output is a list of a-invariants
// of elliptic curves, and a list of multiplicities. 

// When the optional parameter OnlyRankZero is set to true, the function only returns elliptic curves that have rank zero.

// The Jacobian of X_G factors as a product of modular abelian varieties of level dividing N^2. For this reason, 
// elliptic curves with conductor dividing N^2 are checked to see if their a_p(E) values match eigenvalues of Hecke opeartors.
// This relies on the Cremona database, and so this function won't be helpful if N^2 >= 500000. 

intrinsic EllipticCurveQuoCandidates(ModEC::Rec : OnlyRankZero := false) -> SetEnum, RngIntElt
  {Screens for possible elliptic curve factors of the Jacobian of the modular curve by matching traces.}
  N := ModEC`N;
  B := Max(ModEC`preclist);
  MaxECQuos := ModEC`MCR`genus;
  TR := AssociativeArray();
  for p in PrimesUpTo(B) do
    if N mod p ne 0 then
      Tp := HeckeMatrix(ModEC`MCR`F0, N, p, ModEC`preclist, ModEC`Verbose);
      if Tp[2] then
          f := CharacteristicPolynomial(Tp[1]);
          TR[p] := {* r[1]^^r[2] : r in Roots(f) *};
          MaxECQuos := Minimum(MaxECQuos, &+[fac[2] : fac in Factorization(f) | Degree(fac[1]) eq 1]);
      end if;
    end if;
  end for;

  D := EllipticCurveDatabase();
  Candidates := [];
  Mults := [];
  for d in Divisors(N^2) do
    for i in [1..NumberOfIsogenyClasses(D,d)] do
        E := EllipticCurve(D,d,i,1);
        MinE := ModEC`MCR`genus;
        TracesE := TracesOfFrobenius(E,B);
        Flg := true;
        for i in [1..#PrimesUpTo(B)] do
          p := NthPrime(i);
          if p in Keys(TR) then
            MinE := Minimum(MinE, Multiplicity(TR[p], TracesE[i]));
            if MinE eq 0 then
                Flg := false;
                break;
            end if;
          end if;
        end for;
        if Flg then
          if ModEC`Verbose then
            "Candidate found:", aInvariants(E);
            "Multiplicity:", MinE;
          end if;
          Append(~Candidates, aInvariants(E));
          Append(~Mults, MinE);
        end if;
    end for;
  end for;

  if &+ Mults gt MaxECQuos then
    print "More candidates (counted with max possible multiplicity) found than max number of EC quotients.";
    print "Increasing precmult may help.";
  end if;

  if not OnlyRankZero then
    return Candidates, Mults;
  end if;

  RankZeroIso := [];
  RankZeroMults := [];
  for i in [1..#Candidates] do
    E := EllipticCurve(Candidates[i]);
    r := Rank(E);
    if ModEC`Verbose then
      printf "The elliptic curve %o has rank %o.\n", Candidates[i], r;
    end if;
    if r eq 0 then
        Append(~RankZeroIso, Candidates[i]);
        Append(~RankZeroMults, Mults[i]);
    end if;
  end for;
  return RankZeroIso, RankZeroMults;

end intrinsic;

// Wrapper function for the main `EllipticCurveQuoCandidates` function.
intrinsic EllipticCurveQuoCandidates(N::RngIntElt, gens::SeqEnum : B := 1000) -> SetEnum, RngIntElt
  {Wrapper function for InitializeModEC and EllipticCurveQuoCandidates}
  ModEC := InitializeModEC(N, gens);
  return EllipticCurveQuoCandidates(ModEC : B := B);
end intrinsic;

// The main function for this repo. 

// It takes as input a ModEC record created by InitializeModEC,
// a list of a-invariants of elliptic curves, and a list of multiplicities. It returns a map from X_G -> E
// where E is an elliptic curve isogenous to one of those specified in ainvlist. Currently, the function
// requires X_G to have a rational point.

// There is a second version that takes as input a level, list of generators, elliptic curves, and multiplicities and calls 
// InitializeModEC first.

// The optional parameter IgnoreBase when set to true assumes that the basepoint can
// be chosen to be the cusp at infinity. This allows several steps in the algorithm to
// be skipped. 

// The additional optional parameters decprec, precmult, and Verbose can be set by InitializeModEC.

// The optional parameter nummaps is currently unused (the function always returns one map). 

intrinsic FindMapsToEC(ModEC::Rec, ainvlist, multlist : nummaps := 1, IgnoreBase := false) -> Tup
  {Constructs rational maps X_G --> E where E lives in the supplied isogeny class}

  ModEC`nummaps := nummaps;
  ModEC`IgnoreBase := IgnoreBase;

  if Type(ainvlist[1]) eq RngIntElt then
    ainvlist := [ainvlist];
  end if;
  ModEC`ainvlist := ainvlist;

  if Type(multlist) eq RngIntElt then
    multlist := [multlist];
  end if;
  ModEC`multlist := multlist;

  // Step 3 - Determine a weight 2 cusp form(s) that are eigenforms of Hecke operators 
  // with the desired Hecke eigenvalues. Then, compute the Fourier expansions of the 
  //cusp forms and pick the first nummaps of these that are best.
  ModEC`B := FindEigenformBasis(ModEC);
  ModEC`goodforms := GoodForms(ModEC);
  ModEC`psiCF := InfinitePlaces(ModEC`K)[1];
  // For diagnostic purposes - see how big Fourier coefficients of goodforms are.
  mx := CheckFourierCoeffSizes(ModEC);
  if ModEC`Verbose then
    printf "True max = %o.\n",mx;
    printf "Bound is = %o.\n",3*ModEC`N;
  end if;

  // Step 4 - Compute periods of each form

  wrdlist := RandWords(ModEC`N, ModEC`gens, ModEC`Verbose);
  ModEC`perlist := [[[ComputePeriodAlongWord(ModEC,ModEC`goodforms[r][i],wrd) : wrd in wrdlist] : i in [1..nummaps]] : r in [1..#ainvlist]];

  // Steps 5, 6, and 7:
  // - Identify the period lattice for each form.
  // - For each form, determine the optimal elliptic curve in each isogeny class.
  // - Compute degrees of the maps to the elliptic curves and pick the one with smallest degree.

  pers, Elist, manin, Egiven, goodforms, ECdegmap := PickBestECs(ModEC);
  ModEC`pers := pers;
  ModEC`Elist := Elist;
  ModEC`manin := manin;
  ModEC`Egiven := Egiven;
  ModEC`goodforms := goodforms;
  ModEC`ECdegmap := ECdegmap;

  // Step 8 - For each cusp and map, compute period integral from that cusp to the cusp at
  // infinity. Take the image of this under the isomorphism C/Lambda -> E(C) and compute
  // the image exactly as a point in E(Q(zeta_N)). We subtract by these points
  // when making the map to the elliptic curve.

  ModEC`translist := PerIntImages(ModEC);

  // This part completes Step 7

  ModEC`preclist, ModEC`maxdegree := TweakPrec(ModEC);

  // Step 9 - Fourier expansions of maps to elliptic curve. Use the result of Step 8. 
  
  xfourierlist, yfourierlist, newprec, RR := FourierExpOfMaps(ModEC);
  ModEC`xfourierlist := xfourierlist;
  ModEC`yfourierlist := yfourierlist;
  ModEC`newprec := newprec;
  ModEC`RR := RR;

  // Step 10 - Realize x and y modular functions in function field of modular curve over Q(zeta_N)
  if not IgnoreBase then
    ecmaps, LMs, canring, cyclodegree := RealizeInFF(ModEC);
    ModEC`ecmaps := ecmaps;
    ModEC`LMs := LMs;
    ModEC`canring := canring;
    ModEC`cyclodegree := cyclodegree;
  end if;

  // Note: canring is a list of pairs. The first thing in a pair is list of 
  // lists of Fourier expansions of the degree d generators of the canonical 
  // ring. The second thing in a pair is list of degree d monomials 
  // representing the elements.

  // Compute images of basepoint and translate by that.
  
  if not IgnoreBase then
    newxfourierlist, newyfourierlist, newprec2 := TransByBasePt(ModEC);
    ModEC`newxfourierlist := newxfourierlist;
    ModEC`newyfourierlist := newyfourierlist;
    ModEC`newprec2 := newprec2;
  end if;  

  // Steps 11 and 12
  // - Do the linear algebra again, but this time do it over Q and not Q(zeta_n).
  // - Check that the maps we get actually work and return.

  ModEC`ecmaps := MapOverQ(ModEC);
  Map := map<ModEC`XG -> ModEC`Elist[1] | ModEC`ecmaps[1] : Check := false>;

  return <Map>;
end intrinsic;

// Wrapper function for the main `FindMapsToEC` function.
intrinsic FindMapsToEC(N::RngIntElt, gens::SeqEnum, ainvlist, multlist : nummaps := 1, CheckLocal := true, LocalExp := 3, decprec := 5, precmult := 1, Verbose := false, IgnoreBase := false) -> Tup
  {Wrapper function for InitializeModEC and FindMapsToEC}

  ModEC := InitializeModEC(N, gens : decprec := decprec, precmult := precmult, Verbose := Verbose);

  return FindMapsToEC(ModEC, ainvlist, multlist : nummaps := nummaps, CheckLocal := CheckLocal, LocalExp := LocalExp);

end intrinsic;

// This function takes an already existing ModEC record and computes the map the j-map
// j : X_G -> P^1. The result is stored in the ModEC field jmap.

intrinsic ComputeJ(ModEC::Rec) -> Rec
  {Computes equations (from 1 to 5) from X_G to j-line}
  // Step A - Check precision. If insufficient, ask for more.
  if ModEC`Verbose then
    printf "Computing j map.\n";
    tm := Realtime();
  end if;
  N := ModEC`N;
  numcusps := #ModEC`ModelMCR`cusps;
  maxjdeg := Floor((ModEC`ModelMCR`index + ModEC`ModelMCR`genus - 1)/ModEC`ModelMCR`model_degree) + 1;
  minjdeg := maxjdeg - 1;
  absprec := Max([ (ModEC`ModelMCR`prec[i]/ModEC`ModelMCR`widths[i])*N : i in [1..numcusps]]);
  // The numbers in the list above should all be about the same.
  precsum := ((2*maxjdeg*(ModEC`ModelMCR`k+12))/12)*ModEC`ModelMCR`index+2;
  multiplier := &+[ ModEC`ModelMCR`widths[r]/ModEC`ModelMCR`sl2level : r in [1..numcusps]];
  neededprec := Ceiling(precsum/multiplier)+7;
  if neededprec gt absprec then
    if ModEC`Verbose then
      printf "Increasing modular form precision to %o to compute j-map.\n",neededprec;
    end if;
    ModEC`ModelMCR := IncreaseModularFormPrecision(ModEC`ModelMCR,[Ceiling(neededprec*ModEC`ModelMCR`widths[i]/N) : i in [1..numcusps]]);
    delete ModEC`canring;
    ModEC`genforms := [ [ ModEC`ModelMCR`F0[i][j] : j in [1..numcusps]] : i in [1..#ModEC`ModelMCR`F0]];
  end if;
  preclist := ModEC`ModelMCR`prec;
  jpolys := [];
  // Step B - Check to see what if any of the canonical ring has been built.
  polyring := PolynomialRing(Rationals(),#ModEC`genforms,"grevlex");
  if not (assigned ModEC`canring) then
    canring := <>;
    vars := [ polyring.i : i in [1..#ModEC`genforms]];
    gens := [ Evaluate(ModEC`ModelMCR`psi[j],vars) : j in [1..#ModEC`ModelMCR`psi]];
    ttemp := Realtime();
    if ModEC`Verbose then
      printf "Computing Grobner basis for ideal.\n";
    end if;
    I := ideal<polyring | gens>;
    G := GroebnerBasis(I);
    gbtime := Realtime(ttemp);
    if ModEC`Verbose then
      printf "Grobner basis time was %o.\n",gbtime;
    end if;
    LMs := [ LeadingMonomial(G[i]) : i in [1..#G]];
    initideal := ideal<polyring | LMs>;
  else
    canring := ModEC`canring;
    vars := [ polyring.i : i in [1..#ModEC`genforms]];
    initideal := ideal<polyring | [polyring!mm : mm in ModEC`LMs]>;
  end if;
  done := false;
  d := 0;
  // Make E4^3 and Delta.
  R<qqq> := PowerSeriesRing(BaseRing(Parent(ModEC`ModelMCR`F0[1][1])) : Precision := neededprec);
  E4cube := Eisenstein(4,qqq)^3;
  del := Delta(qqq);
  q := ModEC`PS.1;
  jnum := [ Evaluate(E4cube,q^ModEC`ModelMCR`widths[i])+BigO(q^preclist[i]) : i in [1..numcusps]];
  jdenom := [ Evaluate(del,q^ModEC`ModelMCR`widths[i])+BigO(q^preclist[i]) : i in [1..numcusps]];
  while not done do
    d := d + 1;
    if #canring lt d then
      // Step C - Build degree d piece of canonical ring
      if ModEC`Verbose then
        printf "Generating degree %o piece of canonical ring.\n",d;
      end if;
      if (d gt maxjdeg) then
        printf "If the map exists, it should have been found by this point.\n";
        assert false;
      end if;
      mons := MonomialsOfDegree(polyring,d);
      bas := [ m : m in mons | not (m in initideal)];
      newfourier := <>;
      newvars := [];
      if not assigned ModEC`RR then
       RR<zz> := LaurentSeriesRing(ModEC`K);
       ModEC`RR := RR;
      end if;
      if (d eq 1) then
        for ind in [1..#vars] do
          newprd := [ ModEC`RR!ModEC`genforms[ind][r] + BigO(ModEC`RR.1^(preclist[r]+1)): r in [1..numcusps]];
          Append(~newfourier,newprd);
        end for;
        newvars := vars;
      else
        for j in [1..#bas] do
          curmon := bas[j];
          // We have to be able to write curmon as a product of a degree (d-1)
          // monomial not in initideal, and a degree 1 element.
          // If we couldn't, then curmon would be in initideal
          ind := Index([ IsDivisibleBy(curmon,polyring!canring[d-1][2][k]) : k in [1..#canring[d-1][2]]],true);
          chk, q := IsDivisibleBy(curmon,polyring!canring[d-1][2][ind]);
          ind2 := Index(vars,q);
          newprd := [ModEC`RR!(ModEC`genforms[ind2][r]*(canring[d-1][1][ind][r])) : r in [1..numcusps]];
          Append(~newfourier,newprd);
          Append(~newvars,curmon);
        end for;  
      end if;
      Append(~canring,<newfourier,newvars>);
    else
      bas := canring[d][2];
    end if;  

    // Step D - linear algebra
    if (d ge minjdeg) then
      if ModEC`Verbose then
        printf "Searching for jmap in degree %o.\n",d;
        printf "preclist = %o.\n",preclist;
      end if;
      mat := ZeroMatrix(Rationals(),0,(&+[ preclist[r] : r in [1..numcusps]])*Degree(ModEC`K));
      for i in [1..#canring[d][1]] do
        pp := [ jnum[r]*canring[d][1][i][r] : r in [1..numcusps]];
        vecseq := &cat [ &cat [ Eltseq(Coefficient(pp[r],m)) : m in [0..preclist[r]-1]] : r in [1..numcusps]];
        mat := VerticalJoin(mat,Matrix(Rationals(),1,#vecseq,vecseq));
      end for;
      for i in [1..#canring[d][1]] do
        pp2 := [ jdenom[r]*canring[d][1][i][r] : r in [1..numcusps]];      
        vecseq2 := &cat [ &cat [ Eltseq(Coefficient(pp2[r],m)) : m in [0..preclist[r]-1]] : r in [1..numcusps]];
        mat := VerticalJoin(mat,Matrix(Rationals(),1,#vecseq2,vecseq2));
      end for;
      if ModEC`Verbose then
        printf "Matrix size is %o x %o.\n",NumberOfRows(mat),NumberOfColumns(mat);
      end if;
      NN2 := NullSpace(mat);
      dimdim2 := Dimension(NN2);
      if ModEC`Verbose then
        printf "For d = %o, dimension of null space is %o.\n",d,dimdim2;
      end if;
      if (dimdim2 eq 0) and (d ge maxjdeg) then
        printf "If the map exists, it should have been found by now!\n";
        assert false;
      end if;
      if dimdim2 ge 1 then
        done := true;
        nullmat2 := Matrix(Basis(NN2));
        change2 := NicefyRat(ModEC,nullmat2);
        for j in [1..Min(dimdim2,5)] do
          v2 := (change2*nullmat2)[j];
          denomfouriermap := [ &+[ v2[i]*canring[d][1][i][r]*jnum[r] : i in [1..#bas]] : r in [1..numcusps]];
          numfouriermap := [-&+[ v2[i+#bas]*canring[d][1][i][r]*jdenom[r] : i in [1..#bas]] : r in [1..numcusps]];
          chk := [ numfouriermap[r] - denomfouriermap[r] : r in [1..numcusps]];
          if ModEC`Verbose then
            printf "Checking map equation %o of %o.\n",j,Min(dimdim2,5);
          end if;
          CheckFourier(chk,12+d*ModEC`ModelMCR`k,ModEC`ModelMCR`index);
          jdenompoly := &+[ v2[i]*bas[i] : i in [1..#bas]];
          jnumpoly := -&+[ v2[i+#bas]*bas[i] : i in [1..#bas]];
          Append(~jpolys,[jnumpoly,jdenompoly]);
        end for;
      end if;
    end if;  
  end while;
  ModEC`jmap := map< ModEC`XG -> ProjectiveSpace(Rationals(),1) | jpolys >;
  if ModEC`Verbose then
    print "Time to compute j map:", Realtime(tm);
  end if;
  return ModEC;
end intrinsic;

intrinsic RatPtsJInvs(ModEC, RatPts) -> SeqEnum
  {Determines the images of the rational points}
  jInvs := {* *};
  jmap := ModEC`jmap;
  for P in RatPts do
    j := jmap(P);
    if ModEC`Verbose eq true then
      printf "Image of point %o is %o.\n",P,j;
    end if;
    Include(~jInvs, j);
  end for;
  return jInvs;
end intrinsic;