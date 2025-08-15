// First load files from David Zywina's "Modular" repo.
// Available at: https://github.com/davidzywina/Modular
// It is necessary to first navigate to the directory containing this file or to // use the ChangeDirectory command.
AttachSpec("Modular.spec");

// Now load this repository. It is necessary to first navigate to the directory
// containing this file or to use the ChangeDirectory command.
Attach("ModCrvToEC.m");

// Example: 6.6.1.a.1 - Simplest genus >= 1 modular curve.
// Run time is under 1 second.
N := 6;
gens := [[1,3,3,2],[1,5,5,2]];
tim0 := Cputime();
ModEC := InitializeModEC(N, gens);
Maps := FindMapsToEC(ModEC, [0,0,0,0,-27], 1);
ratpoints := RatPtsFromMaps(N,Maps);
tim1 := Cputime(tim0);
printf "There are %o rational points on 6.6.1.a.1. Total time taken was %o sec.\n",#ratpoints,tim1;


// Example: 14.48.2.g.1
// From the LMFDB, we know that the Jacobian of this modular curve is isogenous to
// 196.a1^2. Note that elliptic curves in 196.a have rank 1.
// Run time is about 10 seconds.
tim0 := Cputime();
N := 14;
gens := [ [ 7, 9, 2, 7 ], [ 10, 3, 11, 9 ] ];
ModEC := InitializeModEC(N, gens);
Iso, Mx := EllipticCurveQuoCandidates(ModEC);
Iso; // The elliptic curve [ 0, -1, 0, -2, 1 ] is the only elliptic curve that could occur in the Jacobian decomposition (up to isogeny).
Mx; // The multiplicity of [ 0, -1, 0, -2, 1 ] in the Jacobian decomposition is at most 2.
Maps := FindMapsToEC(ModEC, Iso, Mx);
// We found a rational map to an elliptic curve [0,-1,0,-142,701], which is isogenous to [0,-1,0,-2,1].
printf "We found the map from X_G to the elliptic curve %o. The total time taken was %o sec.\n",aInvariants(Codomain(Maps[1])),Cputime(tim0);

// Example: 37.38.2.a.1 - X_0(37), a genus 2 modular curve with 4 rational points.
// Run time is about 60 seconds.
N := 37;
gens := [[10,19,0,13],[32,2,0,25]];
tim0 := Cputime();
ModEC := InitializeModEC(N, gens);
Maps := FindMapsToEC(ModEC, [0,1,1,-3,1], 1 : CheckLocal := false); // Choose the rank zero factor.
ratpoints := RatPtsFromMaps(N,Maps);
tim1 := Cputime(tim0);
printf "There are %o rational points on 37.38.2.a.1. Total time taken was %o sec.\n",#ratpoints,tim1;

// Example: 64.96.3.b.1 - Rational points on the Fermat quartic
// Run time is about 80 seconds.
N := 64;
gens := [[3,39,0,17],[11,7,0,39],[17,39,0,57],[23,31,0,37],[43,58,0,21]];
tim0 := Cputime();
ModEC := InitializeModEC(N, gens : Verbose := true);
P2<x,y,z> := ProjectiveSpace(Rationals(), 2);
fq := Curve(P2, x^4+y^4-z^4);
assert IsIsomorphic(fq,ModEC`XG);
Iso, Mx := EllipticCurveQuoCandidates(ModEC : OnlyRankZero := true);
Maps := FindMapsToEC(ModEC, Iso, Mx : CheckLocal := false); 
ratpoints := RatPtsFromMaps(N,Maps);
tim1 := Cputime(tim0);
printf "There are %o rational points on 64.96.3.b.1. Total time taken was %o sec.\n",#ratpoints,tim1;

// Example: 39.84.5.b.1 - Genus 5 curve that is bielliptic
// Run time is about 219 seconds.
N := 39;
gens := [[15,13,19,12],[29,21,27,25],[31,27,12,1],[32,9,3,29]];
tim0 := Cputime();
ModEC := InitializeModEC(N, gens : precmult := 1.01, Verbose := true);
Maps := FindMapsToEC(ModEC, [[1,1,0,1,0]], [1] : CheckLocal := false); 
ratpoints := RatPtsFromMaps(N,Maps);
tim1 := Cputime(tim0);
printf "There are %o rational points on 39.84.5.b.1. Total time taken was %o sec.\n",#ratpoints,tim1;

// Example: 36.108.6.g.1 - This is a genus 6 rank 5 curve whose rational points are
// left open in the paper "Serre's constant of elliptic curves over the rationals" by
// Harris Daniels and Enrique González-Jiménez.
// Run time is about 71 seconds.
N := 36;
gens := [[8,17,25,12],[12,23,5,15],[14,15,25,5]];
tim0 := Cputime();
ModEC := InitializeModEC(N, gens : Verbose := true);
Maps := FindMapsToEC(ModEC, [[0,0,0,-27,-918]], [1] : CheckLocal := false); 
ratpoints := RatPtsFromMaps(N,Maps);
tim1 := Cputime(tim0);
printf "There are %o rational points on 36.108.6.g.1. Total time taken was %o sec.\n",#ratpoints,tim1;

// Example: 18.216.11.c.1 - This genus 11 curve maps to 6 different rank 0 elliptic curves.
// We let the function choose the elliptic curve with the lowest degree map. 
// It finds a degree 6 map to [1, -1, 0, 3, -1].
// Run time is about 420 seconds.
N := 18;
gens := [[5,8,12,5],[14,9,9,4],[17,3,0,1]];
tim0 := Cputime();
// We need some extra precision to compute Hecke operators T_5 through T_47.
ModEC := InitializeModEC(N, gens : precmult := 2, Verbose := true);  // Setting precmult to 2 doubles the default precision.
Iso, Mx := EllipticCurveQuoCandidates(ModEC : OnlyRankZero := true);
Maps := FindMapsToEC(ModEC, Iso, Mx : CheckLocal := false); 
ratpoints := RatPtsFromMaps(N,Maps);
tim1 := Cputime(tim0);
printf "There are %o rational points on 18.216.11.c.1. Total time taken was %o sec.\n",#ratpoints,tim1;
