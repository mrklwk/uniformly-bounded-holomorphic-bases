# Explicit uniformly bounded bases of homogeneous holomorphic polynomials in every dimension

A Lean formalization of Mark Lewko's manuscript *Uniformly bounded bases of
homogeneous holomorphic polynomials* (September 12, 2026 revision).

This formalization arose from the author’s research. The author intends to write a paper presenting the argument.

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

Put m=d−1 and L=N+m. Degree indices α have nonnegative integer coordinates and
sum N. The increasing stars-and-bars subset is
S(α)={j+α₁+⋯+α_j : 1≤j≤m}. Let
F_ts=L^(−1/2)exp(2πits/L), with t,s in {1,…,L}, and U_TS=det(F_TS), using
increasing row and column order. The family is

```text
Φ_T(z) = Σ_{|α|=N} U_{T,S(α)} exp(2πi√2 Σ_r α_r²)
         √((N+m)! / (m! ∏_r α_r!)) z^α.
```

The denominator **m! = (d−1)!** is essential. Vanishing coordinates use 0^0=1.
The proof bounds the family by √(m!) times a proved multinomial cancellation
constant; it does not posit that estimate or the sphere moment identities.

The analytic argument proves the coupled form I+11ᵀ needed by the construction,
with arbitrary linear frequencies and anisotropic scales. The separate general
positive-definite integer-matrix cancellation proposition is not proved here
and is not a dependency of the main theorem. The full Poisson finite-difference
estimate is proved by a discrete argument rather than by formalizing the entire
continuous-Gamma appendix.

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
toolchain and packaging requirements still to satisfy. Mark Lewko is the human author and responsible maintainer. Original project
contributions are licensed under AGPL-3.0-only; upstream contributions retain
their own licenses and notices. See [LICENSE](LICENSE), [NOTICE](NOTICE), and
[licensing scope](LICENSE_STATUS.md). The metadata file is deliberately named `formalization.yaml`.
