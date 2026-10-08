module
public import BourgainBasis.BasisFormula
public import BourgainBasis.CoupledPhase

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

local instance (m N : ℕ) : DecidableEq (degreeIndices m N) := Classical.decEq _

theorem phase_mul_star (t : ℝ) : phase t*star (phase t) = 1 := by
  rw [star_phase, ← phase_add, add_neg_cancel]
  simp [phase]

theorem sourceFourierMinors_columns (N m : ℕ) (hm : 0 < m)
    (S R : Set.powersetCard (Fin (N+m)) m) :
    (∑ T, star (orderedMinorMatrix m (sourceFourier (N+m)) T S)*
      orderedMinorMatrix m (sourceFourier (N+m)) T R) = if S=R then 1 else 0 := by
  classical
  have h := Matrix.mem_unitaryGroup_iff'.mp (sourceFourierMinors_unitary N m hm)
  have hh := congrArg (fun A => A S R) h
  simpa only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using hh

/-- Row orthogonality of the actual source coefficients, with the prescribed
stars-and-bars columns and quadratic unit phases. -/
theorem basisCoefficient_rows {m N : ℕ} (hm : 0 < m)
    (T U : Set.powersetCard (Fin (N+m)) m) :
    (∑ α : degreeIndices m N, basisCoefficient T α*star (basisCoefficient U α)) =
      if T=U then 1 else 0 := by
  classical
  calc
    _ = ∑ α : degreeIndices m N, orderedMinorMatrix m (sourceFourier (N+m)) T (starsBarsEquiv m N α)*
        star (orderedMinorMatrix m (sourceFourier (N+m)) U (starsBarsEquiv m N α)) := by
      apply Finset.sum_congr rfl
      intro α _
      unfold basisCoefficient
      rw [star_mul']
      have h := phase_mul_star (Real.sqrt 2*∑ i, (α.val i:ℝ)^2)
      calc
        _ = (orderedMinorMatrix m (sourceFourier (N+m)) T (starsBarsEquiv m N α)*
          star (orderedMinorMatrix m (sourceFourier (N+m)) U (starsBarsEquiv m N α)))*
          (phase (Real.sqrt 2*∑ i, (α.val i:ℝ)^2)*star (phase (Real.sqrt 2*∑ i, (α.val i:ℝ)^2))) := by ring
        _ = _ := by rw [h, mul_one]
    _ = ∑ S, orderedMinorMatrix m (sourceFourier (N+m)) T S*
        star (orderedMinorMatrix m (sourceFourier (N+m)) U S) :=
      Fintype.sum_equiv (starsBarsEquiv m N) _ _ (fun _ => rfl)
    _ = _ := sourceFourierMinors_rows N m hm T U

/-- Column orthogonality for actual multi-indices, without a sphere-moment premise. -/
theorem basisCoefficient_columns {m N : ℕ} (hm : 0 < m) (α β : degreeIndices m N) :
    (∑ T : Set.powersetCard (Fin (N+m)) m, star (basisCoefficient T α)*basisCoefficient T β) =
      if α=β then 1 else 0 := by
  classical
  let p := phase (Real.sqrt 2*∑ i, (α.val i:ℝ)^2)
  let q := phase (Real.sqrt 2*∑ i, (β.val i:ℝ)^2)
  have he (T : Set.powersetCard (Fin (N+m)) m) :
      star (basisCoefficient T α)*basisCoefficient T β = (star p*q)*
        (star (orderedMinorMatrix m (sourceFourier (N+m)) T (starsBarsEquiv m N α))*
          orderedMinorMatrix m (sourceFourier (N+m)) T (starsBarsEquiv m N β)) := by
    unfold basisCoefficient
    rw [star_mul']
    dsimp [p,q]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, sourceFourierMinors_columns N m hm]
  simp only [Equiv.apply_eq_iff_eq]
  split_ifs with h
  · subst β
    change star p*p*1=1
    rw [mul_one, mul_comm]
    exact phase_mul_star _
  · ring

/-- Explicit inverse coefficient transform, as pointwise functions. -/
theorem normalizedMonomial_inverse {m N : ℕ} (hm : 0 < m) (α : degreeIndices m N)
    (z : ComplexEuclidean m) :
    normalizedMonomial α z = ∑ T : Set.powersetCard (Fin (N+m)) m,
      star (basisCoefficient T α)*sourceBasisFunction T z := by
  classical
  simp_rw [sourceBasisFunction, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, basisCoefficient_columns hm]
  simp

/-- Every normalized monomial belongs to the actual homogeneous polynomial span. -/
theorem normalizedMonomial_mem_homogeneous {m N : ℕ} (α : degreeIndices m N) :
    normalizedMonomial α ∈ homogeneousPolynomialSpace m N := by
  have h : homogeneousMonomial α ∈ homogeneousPolynomialSpace m N :=
    Submodule.subset_span (Set.mem_range_self α)
  have hh := (homogeneousPolynomialSpace m N).smul_mem (monomialNormalization α:ℂ) h
  exact hh

theorem sourceBasisFunction_mem_homogeneous {m N : ℕ}
    (T : Set.powersetCard (Fin (N+m)) m) :
    sourceBasisFunction T ∈ homogeneousPolynomialSpace m N := by
  have he : sourceBasisFunction T = ∑ α : degreeIndices m N,
      basisCoefficient T α • normalizedMonomial α := by
    funext z
    simp only [sourceBasisFunction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  exact Submodule.sum_mem _ (fun α _ => Submodule.smul_mem _ _ (normalizedMonomial_mem_homogeneous α))

theorem normalizedMonomial_mem_source_span {m N : ℕ} (hm : 0 < m)
    (α : degreeIndices m N) :
    normalizedMonomial α ∈ Submodule.span ℂ (Set.range (sourceBasisFunction (m := m) (N := N))) := by
  have he : normalizedMonomial α = ∑ T : Set.powersetCard (Fin (N+m)) m,
      star (basisCoefficient T α) • sourceBasisFunction T := by
    funext z
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using normalizedMonomial_inverse hm α z
  rw [he]
  exact Submodule.sum_mem _ (fun T _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self T)))

/-- Exact finite-algebra spanning conclusion. No integral orthogonality or sphere
moments are assumed; the corrected positive normalization is inverted explicitly. -/
theorem sourceBasisFunction_span {m N : ℕ} (hm : 0 < m) :
    Submodule.span ℂ (Set.range (sourceBasisFunction (m := m) (N := N))) =
      homogeneousPolynomialSpace m N := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨T,rfl⟩
    exact sourceBasisFunction_mem_homogeneous T
  · apply Submodule.span_le.mpr
    rintro f ⟨α,rfl⟩
    have hn : (monomialNormalization α:ℂ) ≠ 0 := by
      exact_mod_cast (monomialNormalization_pos α).ne'
    have he : homogeneousMonomial α = (monomialNormalization α:ℂ)⁻¹ • normalizedMonomial α := by
      funext z
      simp only [Pi.smul_apply, smul_eq_mul, normalizedMonomial]
      rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    rw [he]
    exact Submodule.smul_mem _ _ (normalizedMonomial_mem_source_span hm α)

end BourgainBasis
