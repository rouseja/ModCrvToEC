This repository contains Magma code (by Jacob Mayle and Jeremy Rouse) for computing rational maps from a modular curve $X_{G}$ to an elliptic curve $E/\mathbb{Q}$. In addition, there are auxiliary functions for determining which elliptic curves $E$ a given $X_{G}$ maps to, and for using a map from $X_{G}$ to $E$ (when $E$ has rank zero) to determine the rational points on $X_{G}$, and for determining the $j$-invariants of the corresponding points. These functions rely on code in David Zywina's [Modular](https://github.com/davidzywina/Modular) repository for computing modular forms and equations of modular curves and also on Ivan Novak's algorithm [number-of-cm-points-on-modular-curves](https://github.com/inova3c/number-of-cm-points-on-modular-curves). This code is used to determine $X_{G}(\mathbb{Q})$ for all but $11$ modular curves $X_{G}$ with level $\leq 70$, surjective determinant that contain $-I$, and that admit a map over $\mathbb{Q}$ to a rank zero elliptic curve.

## Installation instructions

1. If necessary, update [Magma](https://magma.maths.usyd.edu.au/magma/). (We believe that V2.28-21 or newer is needed.)
2. Download David Zywina's [Modular](https://github.com/davidzywina/Modular) repository. 
3. Move the folders `main` and `earlier_code` to Magma's directory folder (use the <code>GetCurrentDirectory()</code> command in Magma to see the current directory).
4. Download the file [ModCrvToEC.m](https://github.com/rouseja/ModCrvToEC/blob/main/ModCrvToEC.m) from this repository and move it to Magma's directory folder.
5. Open Magma and run the commands <code>AttachSpec("Modular.spec");</code> and <code>Attach("ModCrvToEC.m");</code>. 

## Primary functions

- The function <code>InitializeModEC</code> takes as input a level $N$
and generators for a subgroup of $GL(2,\mathbb{Z}/N\mathbb{Z})$ and returns a <code>ModEC</code> record used by later functions.

- The function <code>EllipticCurveQuoCandidates</code> takes as input a <code>ModEC</code> record and uses the action of Hecke operators to list all potential elliptic curve factors of $X_{G}$. It returns two lists: a list of elliptic curves that *could* occur in the Jacobian decomposition of $X_G$, and a corresponding list of *upper bounds* on their multiplicities in the Jacobian decomposition. (If the optional parameter <code>OnlyRankZero</code> is set to true, only rank zero elliptic curves are returned.)

- The function <code>FindMapsToEC</code> takes as input a <code>ModEC</code> record, an elliptic curve (or a list of elliptic curves), and a multiplicity (or a list of multiplicities) and returns a map from $X_{G}$ to an elliptic curve isogenous to one of those in the list. The function automatically chooses which elliptic curve in the isogeny class to map to. Also, in the event that multiple elliptic curves are specified, the function picks an elliptic curve so that the map from $X_{G}$ to $E$ has minimal degree.

- The function <code>RatPtsFromMaps</code> takes as input a level $N$
and a list of maps to elliptic curves of rank zero and determines the rational points on $X_{G}$ by pulling back all the rational points on $E$ to $X_{G}$. This function uses Hensel lifting and rational reconstruction to handle the zero-dimensional schemes that arise. In complicated cases it is likely to be faster than Magma's built-in functionality.

- The function <code>ComputeJ</code> takes as input a <code>ModEC</code> record and computes the $j$-map $j \colon X_{G} \to \mathbb{P}^{1}$.

- The function <code>RatPtsJInvs</code> takes as input a <code>ModEC</code> record and a list of points on $X_{G}$ and computes their images under the $j$-map.

### Worked example

The commands
```
AttachSpec("Modular.spec");
Attach("ModCrvToEC.m");
```
make available the needed functions.

Running the commands
``` 
N := 15;
gens := [[3,8,4,12],[8,3,9,2],[9,11,8,6],[11,12,6,4]];
ModEC := InitializeModEC(N,gens : Verbose := true);
```
creates the <code>ModEC</code> record associated with the modular curve [15.60.3.d.1](https://beta.lmfdb.org/ModularCurve/Q/15.60.3.d.1/). If we now run
```
Iso, Mults := EllipticCurveQuoCandidates(ModEC : OnlyRankZero := true);
```
we see three elliptic curves that potentially occur as factors of the Jacobian, each with multiplicity at most one. Further, two of these elliptic curves have rank zero. This matches with the decomposition of the Jacobian given on the modular curve's LMFDB page.

Now, running the commands
```
pts := PointSearch(ModEC`XG,100);
ModEC`BasePt := pts[1];
Map := FindMapsToEC(ModEC, Iso, Mults);
```
determines that the degree of the map from $X_{G}$ to [1,0,1,-126,523] is 3, while
the degree of the map from $X_{G}$ to [0,1,1,2,4] is 6. The map from $X_{G}$ to [1,0,1,-126,523] is then computed and returned.

```
ratpts := RatPtsFromMaps(N, Map);
ModEC := ComputeJ(ModEC);
RatPtsJInvs(ModEC,ratpts);
```
shows that $X_{G}(\mathbb{Q})$ contains exactly four points, two of which map to $j = 0$ and two of which map to $j = 8000$.

For additional examples, look at the file [Examples.m](https://github.com/rouseja/ModCrvToEC/blob/main/Examples.m) in this repo.

### Overview of the algorithm

The main function <code>FindMapsToEC</code> works by finding a weight 2 cusp form $f$ for $G$ whose Hecke eigenvalues match those of each specified elliptic curve $E$. By computing period integrals of this weight 2 cusp form numerically, we determine its lattice $L$ of periods. We identify a rational scalar $c$ so that $cL = \Lambda(E')$ for some elliptic curve $E'$ isogenous to $E$. The map $P \mapsto \int_{\infty}^{P} cf(z) dz$ is a map $X_{G} \to \mathbb{C}/\Lambda(E)$ and composing this with the isomorphism $\mathbb{C}/\Lambda(E') \simeq E'(\mathbb{C})$, we obtain Fourier expansions for the $x$ and $y$ modular functions for $G$ that give the map to the elliptic curve. Linear algebra is used to express $x$ and $y$ as ratios of modular forms for $X_{G}$ and therefore to obtain the map from $X_{G}$ to $E'$. The cusp at infinity on $X_{G}$ need not be rational, and so the map we have just obtained need not be defined over $\mathbb{Q}$. We translate this map by the image of a rational point on $X_{G}$ to obtain the final map defined over $\mathbb{Q}$ (which entails doing the linear algebra a second time). Because many of the steps in the algorithm are heuristic, as the last step we have Magma verify that the map obtained really does map the domain $X_{G}$ to the codomain $E'$.

## Additional files for computations of $X_{G}(\mathbb{Q})$

- The file `modcurvedata.txt` contains data extracted from the LMFDB about the 1034 minimal $X_{G}$ of level $\leq 70$ that admit a map to a rank zero elliptic curve.

- The file `nfdata.m` contains a list of all rank zero elliptic curves $E$ whose conductor divides $N^{2}$ for some $N \leq 70$, together with the LMFDB label of the corresponding newform.

- The file `LMFDBmodels.zip` contains Magma scripts that include models and $j$-maps downloaded from the LMFDB.

- The directory `cmpointcount` contains a data file and an optimized version of Ivan Novak's algorithm for counting rational CM points in $X_{G}(\mathbb{Q})$.

- The file `parser.m` contains a script that parses the data files `modcurvedata.txt` and `nfdata.m`, makes a list of labels of modular curves for which `FindMapsToEC` should be run, calls this function, and writes the output to a file.

- The directory `logs` contains several log files documenting the computations determining $X_{G}(\mathbb{Q})$. 

- The file `labels_method_does_not_apply.m` contains a list of the labels of the 6859 level $\leq 70$ modular curves $X_{G}$ that do not admit a map to a rank zero elliptic curve over $\mathbb{Q}$.

- The file `level21genus3map.m` contains a Magma script that computes a map from the genus 3 curve with label [21.84.3.a.1](https://beta.lmfdb.org/ModularCurve/Q/21.84.3.a.1/) to an ellitic curve $E/\mathbb{Q}(\sqrt{-3})$ that has rank zero and uses this to determine the $\mathbb{Q}(\sqrt{-3})$ points on 21.84.3.a.1.

We welcome any questions, comments, or suggestions.
