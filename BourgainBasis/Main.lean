module
public import BourgainBasis.SphereOrthogonality
public import BourgainBasis.UniformBound
public import BourgainBasis.BasisLinearAlgebra

@[expose] public section

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgainBasis

theorem normalizedMonomial_pair_integrable {m N : ℕ} (α β : degreeIndices m N) :
    Integrable (fun z : ComplexUnitSphere m => normalizedMonomial α z.val*star (normalizedMonomial β z.val))
      (normalizedSphere m) := by
  let := normalizedSphere_probability m
  have hc : Continuous (fun z : ComplexUnitSphere m => normalizedMonomial α z.val*star (normalizedMonomial β z.val)) :=
    ((normalizedMonomial_continuous α).comp continuous_subtype_val).mul
      (((normalizedMonomial_continuous β).comp continuous_subtype_val).star)
  exact hc.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))

/-- Integral orthonormality of the actual explicit functions for the actual sphere measure. -/
theorem sourceBasisFunction_gram {m N : ℕ} (hm : 0 < m)
    (T U : Set.powersetCard (Fin (N+m)) m) :
    (∫ z : ComplexUnitSphere m,sourceBasisFunction T z.val*star (sourceBasisFunction U z.val)
      ∂normalizedSphere m) = if T=U then 1 else 0 := by
  classical
  have he : (fun z : ComplexUnitSphere m => sourceBasisFunction T z.val*star (sourceBasisFunction U z.val)) =
      fun z => ∑ α : degreeIndices m N, ∑ β : degreeIndices m N,
        (basisCoefficient T α*star (basisCoefficient U β))*
          (normalizedMonomial α z.val*star (normalizedMonomial β z.val)) := by
    funext z
    unfold sourceBasisFunction
    simp only [star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  have hi (α β : degreeIndices m N) := (normalizedMonomial_pair_integrable α β).const_mul
    (basisCoefficient T α*star (basisCoefficient U β))
  rw [he,integral_finsetSum _ (fun α _ => integrable_finsetSum _ (fun β _ => hi α β))]
  simp_rw [integral_finsetSum _ (fun β _ => hi _ β),integral_const_mul,normalizedMonomial_gram]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  exact basisCoefficient_rows hm T U

/-- The manuscript's exact explicit-basis contract: normalized sphere Gram
orthonormality, full homogeneous span, and a positive dimension-only ball bound. -/
theorem explicitBourgainBasis_proved : ExplicitBourgainBasis := by
  intro m hm
  obtain ⟨C,hC,hbound⟩ := sourceBasisFunction_uniform_bound m hm
  refine ⟨C,hC,?_⟩
  intro N
  exact ⟨sourceBasisFunction_gram hm,sourceBasisFunction_span hm,hbound N⟩

/-- Expanded final statement, with m=d−1, the constant chosen before N,
normalized surface measure, and the closed Euclidean unit ball. -/
theorem uniformly_bounded_homogeneous_basis (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,
      (∀ T U : Set.powersetCard (Fin (N+m)) m,
        (∫ z : ComplexUnitSphere m,sourceBasisFunction T z.val *
          star (sourceBasisFunction U z.val) ∂normalizedSphere m) = if T=U then 1 else 0) ∧
      Submodule.span ℂ (Set.range (sourceBasisFunction (m:=m) (N:=N))) = homogeneousPolynomialSpace m N ∧
      (∀ T : Set.powersetCard (Fin (N+m)) m,∀ z : ComplexEuclidean m,
        ‖z‖≤1 → ‖sourceBasisFunction T z‖≤C) :=
  explicitBourgainBasis_proved m hm

end BourgainBasis
