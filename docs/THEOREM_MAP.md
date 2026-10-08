# Theorem-to-paper mapping

The mathematical source is nonpublic. Lean names below use namespace
`BourgainBasis`. Source locators identify the mathematical components.

| Mathematical component | Source locator | Lean declaration / module | Scope |
|---|---|---|---|
| Main explicit bounded-basis theorem | `thm:main` | `uniformly_bounded_homogeneous_basis`, `Main` | Proved for every d=m+1≥2, all N≥0 |
| Degree-N polynomial space and basis formula | Space definition; `eq:monomials`; Fourier-minor construction | `homogeneousPolynomialSpace`, `sourceBasisFunction`, `BasisFormula` | Actual monomial functions and explicit coefficients |
| Stars and bars | `eq:stars` | `starsBarsEquiv`, `starsBarsEquiv_sorted`, `StarsBars` | Exact increasing subset map |
| Cauchy–Binet and minor unitarity | Construction section | `FourierMinors` | Actual determinant minors |
| Full homogeneous span | Construction section | `sourceBasisFunction_span`, `BasisLinearAlgebra` | Equality with independently defined monomial span |
| Quadratic cancellation | `prop:quadratic` and its application | `coupled_quadratic_cancellation`, `CoupledCancellation` | Proved for I+11ᵀ; arbitrary SPD version remains outside scope |
| Poisson profile differences | `lem:profile` | `poissonProfileEstimate_proved`, `PoissonComplete` | All orders and decay exponents; all means≥0 and integer indices |
| Conditioned Poisson weights | `lem:conditioned`; `eq:slanted` | `poisson_weight_bound`; `PoissonSlice` | Actual slanted weight, support, conditioning and boundary cases |
| Multinomial cancellation | `prop:multinomial` | `multinomial_cancellation`, `CoordinatePermutation` | Every probability vector and every linear frequency; no largest-last restriction |
| Complex phase/amplitude | Reduction to multinomial sum | `normalizedMonomial_polar`, `MonomialPhase` | Includes zero coordinates |
| Pointwise basis bound | Main-theorem proof | `sourceBasisFunction_uniform_bound`, `UniformBound` | One positive constant chosen before N; whole closed ball |
| Sphere monomial moments | `eq:moment` | `sphere_monomial_moment`, `SphereOrthogonality` | Exact m!∏α!/(N+m)! normalization |
| Actual integral orthonormality | Construction / main theorem | `sourceBasisFunction_gram`, `Main` | Gram integrals equal Kronecker delta |

The actual zero-extended Poisson estimates use a discrete proof. This is not a
claim that the manuscript's entire Gamma/digamma appendix is formalized.

The exported theorem uses Gram identity and spanning equality. These identify an
orthonormal basis: the family is continuous and square integrable on the compact
probability sphere; coefficient recovery gives independence, including modulo
almost-everywhere equality; and the exact span is proved. The intended space is
not defined as the span of the proposed basis.

## Independent statement interface

`Challenge.lean` and `Solution.lean` declare `BourgainStatement.manuscript_main`.
They use their own nonnegative-exponent subtype, sorted determinant formula,
monomial span and normalized sphere measure. The Challenge imports only Mathlib.
Solution proves `bar_eq`, `minor_eq` and `Φ_eq` before deriving the statement from
`BourgainBasis.uniformly_bounded_homogeneous_basis`. There are no target-strength
hypotheses: only m>0, with the degree quantified after the bound constant.

`Verification/Semantics.lean` separately proves integrability, L² membership and
linear independence, excluding a vacuous reading of the Gram identity.
`Verification/Closure.lean` verifies the logical closure of both main theorem
roots. `comparator.json` selects the independent statement for a future official
comparison. Direct NanoDa, Lean checker and con-ron validation passed on the
4.35 exported Solution theorem. A subsequent sandboxed
Comparator run accepted public commit 2d23de9224f7f9436eaae70e4e1290cd39ef0592
with all three kernels. Full Palomar mechanical preflight remains separate.

## Endpoint boundary

Every mapped main theorem concerns P_N^(d) for each fixed degree N, with one
constant C_d valid for all degrees in that dimension. Orthonormality is in
normalized L² on the sphere in ℂᵈ, and the bound holds on the closed complex
unit ball. A full Hardy-space definition and completeness theorem for the union
over degrees are not present. See SCOPE.md.
