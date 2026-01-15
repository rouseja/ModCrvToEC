/* This is the Magma script that calls everything to determine X_G(Q) and the images on the j-line
for modular curves X_G with level <= 70 and a map to a rank zero elliptic curve.

Here are the files needed:
ModCrvToEC.m - the main script
modcurvedata.txt - Data from the LMFDB about the 1034 X_G's
nfdata.m - A list pairing a LMFDB newform label with an elliptic curve.
Modular.m - David Zywina's code for working with modular curves (available on Github at http://github.com/davidzywina/Modular/main)
          - The files in the folders "main" and "earlier_code" are needed too.
Modular.spec - This file loads all the needed material from David Zywina's repo.
cmpointcount/newcmpointcount.m - An optimized version of Ivan Novak's code for counting rational CM points on modular curve (available on Github at https://github.com/inova3c/number-of-cm-points-on-modular-curves)
cmpointcount/cmdata.txt - Pairing CM discriminants with j-invariants
ModCrvFiles/ - Download the file "LMFDBmodels.zip" and unzip the contests into a directory
called ModCrvFiles
*/

SetLogFile("mainoutput.out");

D := GetCurrentDirectory();
AttachSpec("Modular.spec");
ChangeDirectory(D);
ChangeDirectory("cmpointcount");
load "newcmpointcount.m";
ChangeDirectory(D);
Attach("ModCrvToEC.m");

str := Read("modcurvedata.txt");
lines := Split(str,"\n");

load "nfdata.m";

LD := recformat< generators : SeqEnum, genus : Integers(), 
has_obstruction : Integers(), index : Integers(), level : Integers(), mults : SeqEnum, 
newforms : SeqEnum, ellipticcurves : SeqEnum, obstructions : SeqEnum, parents : SeqEnum, pointless : MonStgElt, 
rational_cusps : Integers(), reductions : SeqEnum, primepowchk : BoolElt, lemoschk : BoolElt, needtorun : BoolElt, 
ModelType : MonStgElt, Model : Crv, jmap : MapSch, NumRatPts : RngIntElt, jInvs : SetMulti, NumCMRatPts : RngIntElt>;

// Helper function for parsing the model files from the LMFDB.
FixedVers := function(ln, P, vars)
  i1 := Index(ln, ":=") + 3;
  i2 := Index(ln, ";") - 1;
  orig := ln[i1..i2];
  fixed := "";
  for i in [1..#orig] do
    c := orig[i];
    if c in vars then
      j := IntegerToString(Index("xyzwtuvrsabcdefghiklmnopq", c));
      fixed cat:= "P." cat j;
    else
      fixed cat:= c;
    end if;
  end for;
  return eval fixed;
end function;

// Read the j-map from a model file from the LMFDB.
ExtractCrvJ := function(label)
  file := "ModCrvFiles/" cat label cat ".m";
  fstr := Read(file);
  flines := Split(fstr,"\n");
  for ln in flines do
    if #ln ge 4 and ln[1..4] eq "Pol<" then
      i1 := Index(ln, "<") + 1;
      i2 := Index(ln, ">") - 1;
      vars := Split(ln[i1..i2], ",");
      P := ProjectiveSpace(Rationals(), #vars - 1);
    end if;
    if #ln ge 7 and ln[1..7] eq "model_0" then
      i := Index(flines, ln);
      ModelType := flines[i-1];
      ModelType := ModelType[4..#ModelType];
      ModelTypeL := ToLower(ModelType);
      // print ModelType;
      model_0 := FixedVers(ln, P, vars);
    end if;
    if #ln ge 13 and ln[1..13] eq "map_0_coord_0" then
      i := Index(flines, ln);
      NeededMap := "// j-invariant map from the " cat ModelType;
      NeededMapL := "// j-invariant map from the " cat ModelTypeL;
      if flines[i-2] eq NeededMap or flines[i-2] eq NeededMapL then
        map_0_coord_0 := FixedVers(ln, P, vars);
      end if;
    end if;
    if #ln ge 13 and ln[1..13] eq "map_0_coord_1" then
      map_0_coord_1 := FixedVers(ln, P, vars);
    end if;
  end for;
  if assigned map_0_coord_0 then
    Model := Curve(P, model_0);
    jmap := map< Model -> ProjectiveSpace(Rationals(),1) | [map_0_coord_0, map_0_coord_1] >;
    return true, ModelType, Model, jmap;
  end if;
  return false, false, false, false;
end function;

// Parse data from the file "modcurvedata.txt" which was extracted from the LMFDB.
// Along the way, we will record information about whether a curve can be ruled out based on known results.

// A list of modular curves of prime power level <= 31 whose rational points have not been handled.
// For p = 5 we have X_ns^+(25): 25.250.14.a.1
// For p = 7 we have X_ns#(49) and X_sp#(49): 49.147.9.a.1, 49.196.9.a.1
// For p = 11 we have X_ns^+(121): 121.6655.511.a.1
// For p = 19, 23, 29, 31 we have X_ns^+(p): 19.171.8.a.1, 23.253.13.a.1, 29.406.24.a.1, 31.465.28.a.1

badprimepowerlabels := [ "25.250.14.a.1", "49.147.9.a.1", "49.196.9.a.1", "121.6655.511.a.1", "19.171.8.a.1",
  "23.253.13.a.1", "29.406.24.a.1", "31.465.28.a.1"];

// Results of Lemos say that the image of the mod p Galois representation cannot be contained
// in C_ns^+(p) for p > 3 and also the Borel mod q or the split Cartan mod q if q is a prime
// different than p.

nonsplitcartanlabels := [ "5.10.0.a.1", "7.21.0.a.1", "11.55.1.b.1", "13.78.3.a.1", "17.136.6.a.1",
"19.171.8.a.1", "23.253.13.a.1", "29.406.24.a.1", "31.465.28.a.1" ];
splitandborellabels := [ "2.3.0.a.1", "3.4.0.a.1", "3.6.0.b.1", "3.12.0.a.1", "5.6.0.a.1", "5.15.0.a.1", "5.30.0.a.1", "5.30.0.b.1", "7.8.0.a.1",
"7.24.0.a.1", "7.24.0.b.1", "7.28.0.a.1", "13.14.0.a.1", "13.28.0.a.1", "13.28.0.a.2", "13.42.0.a.1",
"13.42.0.a.2", "13.42.0.b.1"];

labelstodo := [];
RecAr := AssociativeArray();
for i in [1..#lines] do
  r := rec<LD | >;

  curstr := Split(lines[i],":,")[2];
  curstr2 := Split(curstr,"'")[2];
  label := curstr2;

  labsplit := Split(curstr2,".");
  r`level := StringToInteger(labsplit[1]);
  r`index := StringToInteger(labsplit[2]);
  r`genus := StringToInteger(labsplit[3]);

  curstr := Split(lines[i],":")[3];
  curstr2 := Split(curstr,"'")[1];
  curstr3 := Substring(curstr2,1,#curstr2-2);
  r`generators := eval curstr3;

  curstr := Split(lines[i],":")[4];
  curstr2 := Split(curstr,",")[1];
  r`has_obstruction := StringToInteger(curstr2);

  curstr := Split(lines[i],":")[5];
  curstr2 := Split(curstr,"'")[1];
  curstr3 := Substring(curstr2,1,#curstr2-2);
  r`mults := eval curstr3;

  curstr := Split(lines[i],":")[6];
  curstr2 := Split(curstr,"]")[1];
  curstr3 := curstr2 cat "]";
  curstr4 := [ curstr3[j] : j in [1..#curstr3]];
  for j in [1..#curstr4] do
    if curstr4[j] eq "'" then
      curstr4[j] := "\"";
    end if;
  end for;
  r`newforms := eval (&cat curstr4);

  NFsWithECs := [];
  for j in [1..#r`newforms] do
    for c in nfdata do
      nf := r`newforms[j];
      if nf eq c[1] then
        Append(~NFsWithECs,<c,r`mults[j]>);
      end if;
    end for;
  end for;
  r`newforms := NFsWithECs;

  curstr := Split(lines[i],":")[7];
  curstr2 := Split(curstr,"'")[1];
  curstr3 := Substring(curstr2,1,#curstr2-2);
  r`obstructions := eval curstr3;

  curstr := Split(lines[i],":")[8];
  curstr2 := Split(curstr,"]")[1];
  curstr3 := curstr2 cat "]";
  curstr4 := [ curstr3[j] : j in [1..#curstr3]];
  for j in [1..#curstr4] do
    if curstr4[j] eq "'" then
      curstr4[j] := "\"";
    end if;
  end for;
  r`parents := eval (&cat curstr4);

  curstr := Split(lines[i],":")[9];
  curstr2 := Split(curstr,",")[1];
  r`pointless := curstr2[2..#curstr2];

  curstr := Split(lines[i],":")[10];
  curstr2 := Split(curstr,",")[1];
  r`rational_cusps := StringToInteger(curstr2);

  curstr := Split(lines[i],":")[11];
  curstr2 := Split(curstr,"]")[1];
  curstr3 := curstr2 cat "]";
  curstr4 := [ curstr3[j] : j in [1..#curstr3]];
  for j in [1..#curstr4] do
    if curstr4[j] eq "'" then
      curstr4[j] := "\"";
    end if;
  end for;
  r`reductions := eval (&cat curstr4);

  chk := false;
  if IsPrimePower(r`level) then
    chk := true;
  end if;
  for j in [1..#r`reductions] do
    curred := r`reductions[j];
    splitlab := Split(curred,".");
    redlev := StringToInteger(splitlab[1]);
    redgen := StringToInteger(splitlab[3]);
    if (redlev ge 2) then
      if IsPrimePower(redlev) and (redgen ge 2) then 
        if not (curred in badprimepowerlabels) then
          chk := true;
        end if;
      end if;
    end if;  
  end for;
  r`primepowchk := chk;
  // r`primepowchk will be true if the modular curve reduces to a prime power level 
  // modular curve that has already been handled.

  nonsplitred := false;
  borelorsplitred := false;
  for j in [1..#r`reductions] do
    curred := r`reductions[j];
    if curred in nonsplitcartanlabels then
      nonsplitred := true;
    end if;
    if curred in splitandborellabels then
      borelorsplitred := true;
    end if;
  end for;
  r`lemoschk := (nonsplitred and borelorsplitred);
  // r`lemoschk will be true if the modular curve simultanouesly has a reduction
  // that is a mod p non-split Cartan for some p >= 5 and a mod q reduction
  // that is a split Cartan or Borel.

  // We will do all cases of genus <= 10, and cases with genus > 10 that don't have a local obstructions, haven't been ruled out
  // by a prime power level modular curve that has already been handled, or Lemos's results.
  // We don't try to run cases where genus >= 60.
  RecAr[label] := r;
  if (r`genus le 10) then 
    if (r`has_obstruction in {-1,0}) then
      r`needtorun := true;
    else
      r`needtorun := false;
    end if;
  end if;
  if (r`genus gt 10) then
    if (r`genus le 60) and (r`has_obstruction in {-1,0}) and (not r`primepowchk) and (not r`lemoschk) then
      r`needtorun := true;
    else
      r`needtorun := false;
    end if;
  end if;
  if (r`needtorun eq true) then
    Append(~labelstodo,label);
  end if;

  Bool, ModelType, Model, jmap := ExtractCrvJ(label);

  if Bool then
    r`ModelType := ModelType;
    r`Model := Model;
    r`jmap := jmap;
  end if;

  RecAr[label] := r;

end for;

PowByPrime := function(p)
    if p eq 2 then
        return 8;
    end if;
    if p eq 3 then
        return 4;
    end if;
    if p le 10 then
        return 3;
    end if;
    return 2;
end function;

SmartpAdic := function(psi, lvl) 
    for p in PrimeDivisors(lvl) do
        PP:=ProjectiveSpace(GF(p), Rank(Parent(psi[1]))-1);
        C:=Scheme(PP, psi); 
        Pointsp := Points(C);
        if Dimension(C) ne 1 or {IsSingular(P) : P in Pointsp} eq {true} then
            "Need to look into", p;
            // p, #PointsViaLifting(psi, p, PowByPrime(p));
            if #PointsViaLifting(psi, p, PowByPrime(p)) eq 0 then
                "There are no points mod p^k", p, PowByPrime(p);
                return p;
            else
                "Found points mod p^k", p, PowByPrime(p);
            end if;
        end if;
    end for;
    return 0;
end function;

for i in [1..#labelstodo] do
  label := labelstodo[i];
  ModCrv := RecAr[label];
  printf "Starting curve %o with label %o.\n",i,label;
  starttim := Cputime();
  // Create the modular curve record, compute the model and increase precision.
  ModEC := InitializeModEC(ModCrv`level, ModCrv`generators : Verbose := true);
  IgnoreBase := true;
  ModCrv`pointless := "False";
  Iso := [E[1][2] : E in ModCrv`newforms];
  Mults := [m[2] : m in ModCrv`newforms];
  // When the genus <= 29, do local testing.
  if ModCrv`genus le 29 then
    pts := PointSearch(ModEC`XG,100 : OnlyOne := true);
    if #pts eq 0 then
      PolZ<[x]>:=PolynomialRing(Integers(),Rank(Parent(ModEC`MCR`psi[1])));
      psi:=[PolZ!f: f in ModEC`MCR`psi];
      s := SmartpAdic(psi, ModCrv`level);
      if (s gt 0) then
        printf "There are no local points at p = %o.\n",s;
        ModCrv`pointless := "True";
        ModCrv`NumRatPts := 0;
        ModCrv`jInvs := {**};
      else
        printf "Possible local-global failure at %o.\n",label;
        printf "Proceeding with IgnoreBase = true.\n";
      end if;
    else
      IgnoreBase := false;
      ModEC`BasePt := pts[1];
    end if;  
  end if;
  try 
  if ModCrv`pointless eq "False" then
    // Run the main function - Find a map to an elliptic curve.
    Map := FindMapsToEC(ModEC, Iso, Mults : IgnoreBase := IgnoreBase);
    // Pull back the rational points to determine X_G(Q).
    allratpts := RatPtsFromMaps(ModCrv`level, Map : Verbose := true);
    ModCrv`NumRatPts := #allratpts;
  end if;  
  // Count rational cusps and CM points.
  CMjMultiSet := NewCMPointCount(ModCrv`level, sub<GL(2, Integers(ModCrv`level)) | ModCrv`generators>);
  ModCrv`NumCMRatPts := #CMjMultiSet;
  if ModCrv`NumRatPts eq ModCrv`rational_cusps + ModCrv`NumCMRatPts then
    NonCMjInvs := {* *};
  else
    // printf "The curve %o has %o rational points, of which %o are cusps and %o are CM. \n", label, ModCrv`NumRatPts, ModCrv`rational_cusps, ModCrv`NumCMRatPts;
    if assigned ModCrv`jmap then
      Pts := PointSearch(ModCrv`Model, 10000);
      if #Pts eq ModCrv`NumRatPts then
        j := ModCrv`jmap;
        ModCrv`jInvs := {* j(P) : P in Pts*};
        // print "The multiset of j-invariants is:", ModCrv`jInvs;
        NonCMjInvs := {* p[1] : p in  ModCrv`jInvs | p[2] ne 0 *} diff CMjMultiSet;
      else
        print "Error with", label;
        print "There is a discrepancy between points via point search and the output";
        printf "We found %o points in a point search and %o via RatPtsFromMaps.\n",#Pts,ModCrv`NumRatPts;
        assert false;
      end if;
    else
      // Compute the j-invariant map.
      ModEC := ComputeJ(ModEC);
      // Compute the images of all the rational points.
      ModCrv`jInvs := RatPtsJInvs(ModEC,allratpts);
      NonCMjInvs := {* p[1] : p in  ModCrv`jInvs | p[2] ne 0 *} diff CMjMultiSet;
    end if;
  end if;
  print "Label:", label;
  endtim := Cputime(starttim);
  print "Number of rational cusps:", ModCrv`rational_cusps;
  print "Number of CM points:", ModCrv`NumCMRatPts;
  print "Multiset of CM j-invariants:", CMjMultiSet;
  print "Number of non-CM points:", ModCrv`NumRatPts - (ModCrv`rational_cusps + ModCrv`NumCMRatPts);
  print "Multiset of non-CM j-invariants:", NonCMjInvs;
  printf "Total time needed was %o sec.\n",endtim;
  if #NonCMjInvs gt 0 then
    print "Non-CM j-invariants were found for label:",label;
  end if;
  print "";
  RecAr[label] := ModCrv;
  catch e
    printf "ISSUE WITH LABEL %o.\n",label;
    printf "ERROR IS %o.\n",e;
    endtim := Cputime(starttim);
    printf "Time before error was %o sec.\n",endtim;
  end try;
end for;

