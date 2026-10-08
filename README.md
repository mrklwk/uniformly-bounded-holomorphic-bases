# Explicit uniformly bounded bases of homogeneous holomorphic polynomials in every dimension

A Lean formalization of explicit uniformly bounded orthonormal bases of
homogeneous holomorphic polynomials.

For every fixed complex dimension **d ≥ 2**, there is a real **C_d > 0** such
that, for **every degree N ≥ 0**, the degree-N homogeneous holomorphic polynomials
on **ℂᵈ** have the specified finite basis. Its restrictions to the complex unit
sphere **S_d = {z ∈ ℂᵈ : ‖z‖₂ = 1}** are orthonormal in **L²(S_d, σ_d)**, where
**σ_d(S_d) = 1**. Every basis function satisfies **|Φ_T(z)| ≤ C_d** on the closed
complex unit ball **{z ∈ ℂᵈ : ‖z‖₂ ≤ 1}**.

The verified endpoint is a basis of **each homogeneous degree block**. It does
not include a formal Hardy-space definition or a completeness theorem for the
union of these bases across all degrees. See [precise scope](docs/SCOPE.md).

The current verified formal endpoint covers d≥2. The elementary d=1 case is
kept in a separate proposed extension until integrated verification is complete.
The title does not assert a dimension-independent bound. “Explicit” refers to
the actual basis formula, not an optimized numerical value of C_d.

The constant is chosen before N. It is not uniform in dimension: already in
degree one every normalized linear form has supremum norm √d. No optimal
constant or numerical table is asserted.

Historical attribution and the distinctions from near-full systems, random
sections and mixed-degree Hardy-space bases are recorded in
[historical context](docs/HISTORY.md), with primary references.

## Exact formal result

The expanded statement is
`BourgainBasis.uniformly_bounded_homogeneous_basis` in
[BourgainBasis/Main.lean](BourgainBasis/Main.lean). It assumes only `m : ℕ` and
`0 < m`, where **d = m+1**, and proves:

1. The actual sphere Gram integral of Φ_T and Φ_U is the Kronecker delta.
2. The complex span of the family equals the independently defined span of all
   monomials of total degree N.
3. Every member is bounded by one positive dimension-only constant on the
   closed unit ball, including degree zero and the origin.

The space is represented by polynomial functions, not a syntactic polynomial
subtype. Gram identity plus spanning is the orthonormal-basis formulation.
`explicitBourgainBasis_proved` proves the equivalent named contract.

[Challenge.lean](Challenge.lean) restates the explicit formula using only Mathlib
and independently defined exponent vectors. [Solution.lean](Solution.lean) proves
the same statement by identifying the formulas and applying the full theorem.
Its starting point was Claude’s independent restatement; the adaptation is
separately checked. It introduces no target-strength premise.

## Explicit construction

Fix an integer d≥2 and a degree N≥0. Put m=d−1 and L=N+m, so L≥1.
Write z=(z₁,…,z_d) for a point of ℂᵈ. Let σ_d be surface measure on the
unit sphere S_d={z: ‖z‖₂=1}, normalized to have total mass one.

For an exponent vector α=(α₁,…,α_d) of nonnegative integers with
α₁+⋯+α_d=N, write z^α=∏_{r=1}^d z_r^{α_r}. The normalized monomial is

$$
M_\alpha(z)=
\left(\frac{(N+d-1)!}{(d-1)!\prod_{r=1}^{d}\alpha_r!}\right)^{1/2}z^\alpha.
$$

These monomials form an orthonormal basis of the degree-N homogeneous
polynomials for the inner product $\int_{S_d} f(z)\overline{g(z)}\,d\sigma_d(z)$. The factor
(d−1)! in the denominator corresponds to the normalization σ_d(S_d)=1,
with S_d as defined above. Powers with exponent zero are one, including
at a zero coordinate.

Associate to α the integers

$$
s_j(\alpha)=j+\sum_{r=1}^{j}\alpha_r\qquad(1\le j\le m).
$$

They satisfy 1≤s₁(α)<⋯<s_m(α)≤L. Thus
S(α)={s₁(α),…,s_m(α)} is an m-element subset of {1,…,L}.
This is a bijection: given 1≤s₁<⋯<s_m≤L, its inverse is

$$
\alpha_1=s_1-1,\qquad
\alpha_j=s_j-s_{j-1}-1\ (2\le j\le m),\qquad
\alpha_d=L-s_m.
$$

The middle range is empty when d=2. The coordinates are nonnegative and
sum to L−m=N. Consequently both the exponent vectors and the m-element
subsets are indexed by a set of cardinality $\binom{N+d-1}{d-1}$.

Define the L×L normalized Fourier matrix by

$$
F_{ts}=\frac{1}{\sqrt L}\exp\!\left(\frac{2\pi i\,ts}{L}\right),
\qquad 1\le t,s\le L,
$$

where i is the imaginary unit. Both row and column indices start at one,
and the exponent has a positive sign.
For m-element subsets T={t₁<⋯<t_m} and S={s₁<⋯<s_m} of {1,…,L}, define

$$
U_{T,S}=\det\!\left[
\frac{1}{\sqrt L}\exp\!\left(\frac{2\pi i\,t_a s_b}{L}\right)
\right]_{a,b=1}^{m}.
$$

Thus the rows of this determinant are ordered by t₁,…,t_m and the columns
by s₁,…,s_m. This fixes the sign of every minor.

For each exponent vector α, set

$$
q_\alpha=\exp\!\left(2\pi i\sqrt2\sum_{r=1}^{d}\alpha_r^2\right).
$$

The basis is indexed by all m-element subsets T of {1,…,L}. Its member
corresponding to T is

$$
\Phi_T(z)=\sum_{\substack{\alpha_1,\ldots,\alpha_d\ge0\\
                         \alpha_1+\cdots+\alpha_d=N}}
U_{T,S(\alpha)}\,q_\alpha\,M_\alpha(z).
$$

The Fourier matrix is unitary. Cauchy–Binet implies that the square matrix
of its ordered m×m minors, (U_{T,S}), is also unitary. The map α↦S(α)
just reindexes its columns, and multiplication of each column by q_α
preserves unitarity because |q_α|=1. Applying this matrix to the normalized
monomials therefore gives another orthonormal basis of the same polynomial
space.

The nontrivial estimate is the pointwise bound: for each fixed d there is
C_d>0 such that |Φ_T(z)|≤C_d for every N≥0, every T, and every ‖z‖₂≤1.
Unitarity alone does not give a bound independent of N. The proof uses
cancellation from the quadratic phase together with estimates for the
monomial weights. The constant may depend on d; no optimized numerical
value is asserted.

The formula includes N=0. In this case L=m, the only exponent vector is zero,
and S(α)=T={1,…,m}. The normalized monomial and q_α both equal one, so the
single basis function is the constant det F, of absolute value one. It need
not be the constant one.

In Lean, coordinates and Fourier indices are stored starting at zero.
`BourgainStatement.bar` and `minor` insert the offsets displayed above;
the theorems `bar_eq`, `minor_eq` and `Φ_eq` in `Solution.lean` identify this formula with
`BourgainBasis.sourceBasisFunction`. The verified theorem assumes m>0,
equivalently d≥2. The elementary d=1 monomial construction is a separate
proposal and is not part of this release export.

The analytic proof treats the coupled quadratic form I+11ᵀ needed by this
construction. The arbitrary positive-definite integer-matrix version is not
proved or assumed here. The Poisson finite-difference estimates use a discrete
proof; the entire continuous-Gamma appendix is not formalized.

## Verification and reproducibility

The project pins Lean **4.35.0-rc2** and mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The only axioms of the final theorem
are `propext`, `Classical.choice`, and `Quot.sound`. There are no unresolved
proof placeholders or additional axioms in the proof development. The separate
`Challenge.lean` has exactly one deliberate statement-only placeholder; it is not
imported by `Solution.lean` or by the production proof.

See [verification instructions](docs/VERIFICATION.md) for a project-only fresh build using an
already installed pinned toolchain and dependency cache. Generated objects and
logs belong outside this source tree. The Lake files describe the same dependency
pins; no compiler or package installation is performed by the verification script.

## Provenance, scope and release status

See [theorem-to-paper mapping](docs/THEOREM_MAP.md), [provenance](PROVENANCE.md),
[credits](CREDITS.md), and [license status](LICENSE_STATUS.md).
The source comparison used the complete authenticated manuscript text. Original
TeX file bytes and the PDF have not been reconciled; no original-file hash or PDF
verification is claimed.

This repository has not been submitted to or registered with Palomar. The [Palomar preparation notes](docs/PALOMAR.md) identify the current
toolchain and packaging requirements still to satisfy. Authorship and AI
assistance are recorded in [CREDITS.md](CREDITS.md). Original project
contributions are licensed under AGPL-3.0-only; upstream contributions retain
their own licenses and notices. See [LICENSE](LICENSE), [NOTICE](NOTICE), and
[licensing scope](LICENSE_STATUS.md). The release metadata is in `formalization.yaml`.
