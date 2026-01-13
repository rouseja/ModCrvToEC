// This script is a modification of the file "cm point count.txt"
// from Ivan Novak's Github https://github.com/inova3c/number-of-cm-points-on-modular-curves


load "cmdata.txt";

// Add -Id to H
AttachMinusIdentity := function(N, H)
    R := Integers(N);
    minusId := -Identity(GL(2,R));
    return sub< GL(2,R) | Generators(H) join { minusId } >;
end function;

// This is Ivan Novak's function. It's fairly slow so we don't use it.
function AllDoubleCosets(G, H, A)
    G_set := Set(G);
    H_set := Set(H);
    A_set := Set(A);
   
    double_cosets := [];
    remaining := G_set;
   
    while #remaining gt 0 do
        g := Random(remaining);
       
        // Manually compute H * {g} * A = {h * g * a : h in H, a in A}
        double_coset := {h * g * a : h in H_set, a in A_set};
       
        Append(~double_cosets, <g, double_coset>);
        remaining diff:= double_coset;
    end while;
   
    return double_cosets;
end function;

// We use the function below to find representatives for the double cosets H\G/A, 
// assuming that A is cyclic and of small order.
function DoubleCosetReps(G,H,A)
  a := A.1;
  assert Order(a) eq #A;
  cosetreps, transmap := RightTransversal(G,H);
  ret := [];
  for c in cosetreps do
    good := true;
    done := false;
    i := 0;
    while (done eq false) do
      if transmap(c*a^i) in ret then
        good := false;
        done := true;
      else
        i := i + 1;
      end if;
      if (i ge Order(a)) then
        done := true;
      end if;
    end while;
    if good then
      Append(~ret,c);
    end if;
  end for;
  return ret;
end function;

// We do not use the next two functions. Drew Sutherland's
// GL2Cartan and GL2CartanNormalizer are much faster and give fewer generators.
// Build C_{delta,phi}(N)
BuildCdeltaPhi := function(N, delta, phi)
    R := Integers(N);
    G := GL(2,R);
    mats := [ ];
    for a in [0..N-1] do
        for b in [0..N-1] do
            M := Matrix(R,2,2,[a+b*phi,b,delta*b,a]);
            if IsInvertible(M) then
                Append(~mats,M);
            end if;
        end for;
    end for;
    return sub< G | mats >;
end function;

// Build N_{delta,phi}(N)
BuildNdeltaPhi := function(N, delta, phi)
    R := Integers(N);
    G := GL(2,R);
    mats := [ ];
    for a in [0..N-1] do
        for b in [0..N-1] do
            M := Matrix(R,2,2,[a+b*phi,b,delta*b,a]);
            if IsInvertible(M) then
                Append(~mats,M);
            end if;
        end for;
    end for;
    extra := Matrix(R,2,2,[-1,0,phi,1]);
    Append(~mats,extra);
    return sub< G | mats >;
end function;

// NewCMPointCount function

NewCMPointCount := function(N,H)
    retset := {* *};
    RZ := Integers(N);
    G := GL(2,RZ);

    H := AttachMinusIdentity(N,H);
    total_count := 0;

    for triple in cmlist do
        d := triple[1];
        f := triple[2];
        j := triple[3];

        R := GL2CartanNormalizer(d*f^2,N);

        count := 0;

        if j ne 0 and j ne 1728 then
            // generic case: right cosets Hg with gRg^-1 <= H
            reps := RightTransversal(G, H);

            for g in reps do
    		  ok := true;
              for r in Generators(R) do
        	    if not (g*r*g^-1 in H) then
                  ok := false;
            	  break;
        	    end if;
    		  end for;
    		  if ok then
        	    count +:= 1;
    		  end if;
            end for;
        else
          // special cases: define A
          if j eq 1728 then
            A := sub< G | [ Matrix(RZ,2,2,[0,-1,1,0]) ] >;
          elif j eq 0 then
            A := sub< G | [ Matrix(RZ,2,2,[1,1,-1,0]) ] >;
          end if;
          dcreps := DoubleCosetReps(G,H,A);
          // For each double coset representative g,
          // test whether gRg^(-1) is contained in H*(gAg^(-1)).
          cosetrep, transmap := RightTransversal(G,H);
          //printf "Found %o double coset reps.\n",#dcreps;
          for i in [1..#dcreps] do
            g := dcreps[i];
            Rconj := Conjugate(R,g^(-1)); // This is gRg^(-1).
            goodims := [ transmap(g*(A.1)^i*g^(-1)) : i in [1..#A]];
            // Now, we test if each coset representative for (H intersecxt gRg^(-1))
            // inside gRg^(-1) is in one of the few cosets in H*(gAg^(-1)).
            cosetrep2 := RightTransversal(Rconj,H meet Rconj);
            //printf "For rep %o, the index of gRg^(-1) intersect H in gRg^(-1) is %o.\n",i,#cosetrep2;
            if &and [ transmap(corep) in goodims : corep in cosetrep2] then
              count+:=1;
              //printf "This one is good!\n";
            end if;
          end for;
        end if;
        Include(~retset,j^^count);
    end for;
    return retset;
end function;

//Example: the modular curve X_1(3)

/*
G:=GL(2, Integers(3));
H:=sub<G | [1, 0, 0, 2], [1, 1, 0, 2]>;
#H;
time NewCMPointCount(3, H);
*/

//Example: X_0(88) - no CM points.
/*
G:=GL(2, Integers(88));
H:=sub<G | [1, 0, 0, 3], [1, 1, 0, 1], [3,0,0,1], [5,0,0,1], [1,0,0,5], [7,0,0,1], [1,0,0,7] >;
time NewCMPointCount(88,H);
*/

//Example: X_0(163) - only one CM point.
/*
G := GL(2,Integers(163));
H:=sub<G|[104,157,0,45],[112,111,0,157]>;
time NewCMPointCount(163,H);
*/

// X_ns^+(27) - 8 rational CM points all with different discriminants.
/*
G := GL(2,Integers(27));
H:=sub<G|[22,20,18,5],[24,20,16,3]>;
time NewCMPointCount(27,H);
*/

// 32.96.3.bj.1 - 6 rational points above j = 1728.
/*
G := GL(2,Integers(32));
H := sub<G | [15,20,22,17], [21,18,12,9], [25,29,12,23], [31,30,28,27]>;
time NewCMPointCount(32,H);
*/