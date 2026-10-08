module
public import BourgainBasis.StarsBars
public import BourgainBasis.FourierMinors
public import BourgainBasis.SphereModel
public import BourgainBasis.HomogeneousBounds

@[expose] public section

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgainBasis

/-- The source's corrected monomial normalization includes m!=(d−1)!. -/
def monomialNormalization {m N : ℕ} (α : degreeIndices m N) : ℝ :=
  Real.sqrt (((N+m).factorial:ℝ)/((m.factorial:ℝ)*∏ i, (α.val i).factorial))

def homogeneousMonomial {m N : ℕ} (α : degreeIndices m N) (z : ComplexEuclidean m) : ℂ :=
  ∏ i, (z i)^(α.val i)

def normalizedMonomial {m N : ℕ} (α : degreeIndices m N) (z : ComplexEuclidean m) : ℂ :=
  monomialNormalization α * homogeneousMonomial α z

def basisCoefficient {m N : ℕ} (T : Set.powersetCard (Fin (N+m)) m)
    (α : degreeIndices m N) : ℂ :=
  orderedMinorMatrix m (sourceFourier (N+m)) T (starsBarsEquiv m N α) *
    phase (Real.sqrt 2*∑ i, (α.val i:ℝ)^2)

/-- The exact explicit basis functions, defined without assuming any theorem. -/
def sourceBasisFunction {m N : ℕ} (T : Set.powersetCard (Fin (N+m)) m)
    (z : ComplexEuclidean m) : ℂ :=
  ∑ α : degreeIndices m N, basisCoefficient T α * normalizedMonomial α z

def homogeneousPolynomialSpace (m N : ℕ) : Submodule ℂ (ComplexEuclidean m → ℂ) :=
  Submodule.span ℂ (Set.range (homogeneousMonomial (m := m) (N := N)))

/-- Exact main contract over an actual normalized Euclidean sphere measure.
This is a proposition definition only, neither an axiom nor a proved theorem. -/
def ExplicitBourgainBasis : Prop :=
  ∀ m : ℕ, 0 < m → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
    (∀ T U : Set.powersetCard (Fin (N+m)) m,
      (∫ z : ComplexUnitSphere m, sourceBasisFunction T z.val *
        star (sourceBasisFunction U z.val) ∂normalizedSphere m) = if T=U then 1 else 0) ∧
    Submodule.span ℂ (Set.range (sourceBasisFunction (m := m) (N := N))) =
      homogeneousPolynomialSpace m N ∧
    (∀ T : Set.powersetCard (Fin (N+m)) m, ∀ z : ComplexEuclidean m,
      ‖z‖ ≤ 1 → ‖sourceBasisFunction T z‖ ≤ C)

theorem monomialNormalization_pos {m N : ℕ} (α : degreeIndices m N) :
    0 < monomialNormalization α := by
  unfold monomialNormalization
  apply Real.sqrt_pos.mpr
  apply div_pos
  · positivity
  · apply mul_pos (by positivity)
    have hh : (0:ℕ) < ∏ i : Fin (m+1), (α.val i).factorial :=
      Finset.prod_pos (fun i _ => Nat.factorial_pos _)
    exact_mod_cast hh

theorem homogeneousMonomial_smul {m N : ℕ} (α : degreeIndices m N)
    (t : ℝ) (z : ComplexEuclidean m) :
    homogeneousMonomial α (t • z) = (t:ℂ)^N*homogeneousMonomial α z := by
  unfold homogeneousMonomial
  simp only [PiLp.smul_apply, Complex.real_smul, mul_pow, Finset.prod_mul_distrib]
  congr 1
  exact (Finset.prod_pow_eq_pow_sum _ _ _).trans (congrArg (fun k => (t:ℂ)^k) α.property)

theorem sourceBasisFunction_smul {m N : ℕ} (T : Set.powersetCard (Fin (N+m)) m)
    (t : ℝ) (z : ComplexEuclidean m) :
    sourceBasisFunction T (t • z) = (t:ℂ)^N*sourceBasisFunction T z := by
  unfold sourceBasisFunction normalizedMonomial
  simp_rw [homogeneousMonomial_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  ring

end BourgainBasis
