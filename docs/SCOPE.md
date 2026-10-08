# Complex setting and exact endpoint

Title: **Explicit uniformly bounded bases of homogeneous holomorphic polynomials in every dimension**.

Fix d ≥ 2, write m = d−1, and let S_d be the unit sphere in ℂᵈ with probability
surface measure σ_d. Let P_N^(d) be the complex span of the monomials z^α with
nonnegative integer exponents whose sum is N. The inner product is inherited
from L²(S_d, σ_d), not unnormalized surface measure or a real-sphere polynomial
problem. The supremum bound is pointwise throughout the closed complex unit ball.

The exact quantifiers are:

```text
for every d ≥ 2, there exists C_d > 0 such that for every N ≥ 0:
  the explicit degree-N family has normalized-sphere Gram matrix δ_TU;
  its complex span is the full degree-N homogeneous polynomial space;
  |Φ_T(z)| ≤ C_d for every family member and every ‖z‖₂ ≤ 1.
```

C_d may depend on complex dimension d. It is independent of N and of the chosen
basis element. “Explicit” refers to the basis formula. No dimension-uniform bound or optimal
numerical constant is claimed.
The explicit normalized monomial factor is
sqrt((N+d−1)! / ((d−1)! product α_i!)).

## What Lean proves

BourgainBasis.uniformly_bounded_homogeneous_basis in BourgainBasis/Main.lean
and BourgainStatement.manuscript_main in Solution.lean quantify N after the
constant, but each Gram identity and span equality concerns that one degree N.
The polynomial space is represented as the span of actual monomial functions
on ℂᵈ; sphere integrals use those functions' restrictions. The independent
Challenge repeats this statement with Mathlib definitions and its own exponent
subtype. Verification/Semantics.lean also checks L² membership, integrability,
holomorphicity and linear independence.

## Hardy-space distinction

There is no formal Hardy-space H² model or theorem asserting that the union over
all N is a complete orthonormal basis of a Hardy space. Such an extension would
require the Hardy-space model and a proof that the degree-wise families form a
complete orthogonal system, including cross-degree orthogonality and density.
Those steps are not part of the current exported theorem. This is a distinction
in the formalized endpoint, not a claim that no Hardy-space consequence can be
deduced mathematically. In particular, the finite family is not advertised as
a basis of all of L²(S_d, σ_d).

## Dimension one and the title

The current verified release endpoint retains d≥2. In dimension one the natural
family is the singleton {z^N}, with the degree-independent bound C_1=1. The separate
`BourgainBasis.one_dimensional_homogeneous_basis` corollary passed Lean 4.34.1
and a 48,566-declaration kernel replay with only the three standard axioms
at proposal commit `b6fcaa1681dfb47973350f7bb949f3e471514a29`.
Its Lean 4.35.0-rc2 integration is blocked; it is not included in this release's exported theorem or its 4.35 verification
receipt. The phrase “in every dimension” does not mean that C_d is independent
of dimension. A unified all-positive-dimension export is not claimed here.
