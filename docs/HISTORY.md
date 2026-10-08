# Historical context

Bourgain attributes the homogeneous-basis question to W. Rudin in §3 of his
[2015 preprint](https://arxiv.org/pdf/1506.05694). We assign no precise year to
Rudin’s original question. Bourgain constructed uniformly bounded orthonormal
bases in complex dimension two in *Proc. Amer. Math. Soc.* **93** (1985),
277–283, and dimension three in *Amer. J. Math.* **138** (2016), 571–584
(the latter appeared as a preprint in June 2015). These bounds are uniform in
the homogeneous degree. See the [bibliographic references](../CREDITS.md).

The homogeneous problem must be distinguished from the full Hardy-space
problem allowing polynomial basis elements of mixed degrees. Uniformly bounded
orthonormal polynomial bases in that setting were already known in every
complex dimension; Bourgain’s preprint distinguishes the two problems and
establishes the mixed-degree result in Proposition 2. We claim no novelty for
that existence statement. This repository’s formal endpoint is the finite
basis within each homogeneous degree, as specified in [SCOPE.md](SCOPE.md).

Marzo and Ortega-Cerdà obtain uniformly bounded orthonormal **systems** with
cardinality at least a fraction 1−ε of the ambient dimension in their
polynomial/holomorphic-section settings. This is a near-full system result,
not a complete orthonormal basis theorem; its bound may depend on ε.
See [*Uniformly bounded orthonormal polynomials on the sphere*](https://arxiv.org/abs/1405.5417),
*Bull. Lond. Math. Soc.* **47** (2015), 883–891.

Georgiev, Gómez-Serrano, Tao and Wagner explicitly record the homogeneous
holomorphic orthonormal-basis problem for complex dimension m≥4 as open in
[*Mathematical exploration and discovery at scale*, §6.37](https://arxiv.org/html/2511.02864v3),
“Rudin problem for polynomials,” version 3 dated 22 December 2025.
The subsection contains Problem 6.57; it is not Problem 6.37. This is a dated
record of the problem’s status, not a claim that it remains open after the
argument presented here. We cite the explicit homogeneous-basis sentence;
we do not adopt the subsection’s preceding spherical-harmonic formulation.

For normalized random holomorphic sections, Feng and Zelditch show that the
mean and median supremum norm have order √(log N) in fixed dimension; see
[arXiv:1303.4096](https://arxiv.org/abs/1303.4096), *J. Funct. Anal.* **266**
(2014), 5085–5107. This growing random-section estimate is not a theorem giving
a complete basis with a degree-independent bound. Our literature review did
not locate a randomized existence theorem with that complete-basis conclusion;
this is a qualified search finding, not an assertion that none exists.

Here “uniformly bounded” means a constant C_d chosen independently of degree N
for each fixed complex dimension d. It does not mean a constant independent of
d. “Orthonormal” refers to the complex L² inner product on the unit sphere
with measure normalized to mass one. “Explicit” refers to the displayed basis
formula, not an optimized value of C_d. The verified release still covers d≥2;
the separate d=1 monomial extension awaits integrated verification.
