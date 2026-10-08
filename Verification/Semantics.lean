module
public import BourgainBasis.Main

@[expose] public section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory BourgainBasis

/- These are audit-only consequences, in a separate file. No production source
   is edited. They make the semantic bridges explicit. -/

theorem audit_final_contract (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (∀ T U : Set.powersetCard (Fin (N+m)) m,
        (∫ z : Metric.sphere (0 : EuclideanSpace ℂ (Fin (m+1))) 1,
          sourceBasisFunction T z.val * star (sourceBasisFunction U z.val)
          ∂(((volume : Measure (EuclideanSpace ℂ (Fin (m+1)))).toSphere Set.univ)⁻¹ •
            (volume : Measure (EuclideanSpace ℂ (Fin (m+1)))).toSphere)) =
          if T=U then 1 else 0) ∧
      Submodule.span ℂ (Set.range (sourceBasisFunction (m:=m) (N:=N))) =
        Submodule.span ℂ (Set.range (fun α : degreeIndices m N =>
          fun z : EuclideanSpace ℂ (Fin (m+1)) => ∏ i, (z i)^(α.val i))) ∧
      (∀ T : Set.powersetCard (Fin (N+m)) m,
        ∀ z : EuclideanSpace ℂ (Fin (m+1)), ‖z‖ ≤ 1 → ‖sourceBasisFunction T z‖ ≤ C) := by
  exact uniformly_bounded_homogeneous_basis m hm

theorem audit_final_dimension (d : ℕ) (hd : 2 ≤ d) :
    (d-1)+1=d ∧ ExplicitBourgainBasis := by
  exact ⟨by omega, explicitBourgainBasis_proved⟩

theorem audit_actual_polynomial_formula {m N : ℕ}
    (T : Set.powersetCard (Fin (N+m)) m) (z : ComplexEuclidean m) :
    sourceBasisFunction T z =
      ∑ α : degreeIndices m N,
        (orderedMinorMatrix m (sourceFourier (N+m)) T (starsBarsEquiv m N α) *
          Complex.exp ((2*Real.pi*(Real.sqrt 2*∑ i, (α.val i:ℝ)^2):ℝ)*Complex.I)) *
        ((Real.sqrt (((N+m).factorial:ℝ)/((m.factorial:ℝ)*∏ i, (α.val i).factorial)):ℂ) *
          ∏ i, (z i)^(α.val i)) := by
  rfl

theorem audit_basis_functions_holomorphic {m N : ℕ}
    (T : Set.powersetCard (Fin (N+m)) m) :
    Differentiable ℂ (sourceBasisFunction T) := by
  unfold sourceBasisFunction normalizedMonomial homogeneousMonomial
  fun_prop

theorem audit_coordinate_gaussian_integrable {m N : ℕ} (α β : degreeIndices m N) :
    Integrable (fun x : ComplexEuclidean m =>
      homogeneousMonomial α x * star (homogeneousMonomial β x) *
        (Real.exp (-‖x‖^2):ℂ)) (coordinateVolume m) := by
  rw [coordinateVolume_eq]
  exact (gaussian_monomial_pair_integrable α β).smul_measure_nnreal

theorem audit_sphere_measure_nondegenerate (m : ℕ) :
    normalizedSphere m Set.univ = 1 ∧ 0 < sphereArea m := by
  refine ⟨normalizedSphere_mass m, ?_⟩
  exact lt_of_le_of_ne ENNReal.toReal_nonneg (sphereArea_ne_zero m).symm

theorem audit_gram_nonzero {m N : ℕ} (hm : 0 < m)
    (T : Set.powersetCard (Fin (N+m)) m) :
    (∫ z : ComplexUnitSphere m, sourceBasisFunction T z.val *
      star (sourceBasisFunction T z.val) ∂normalizedSphere m) = 1 := by
  simpa using sourceBasisFunction_gram hm T T

theorem audit_actual_L2_membership {m N : ℕ}
    (T : Set.powersetCard (Fin (N+m)) m) :
    MemLp (fun z : ComplexUnitSphere m => sourceBasisFunction T z.val) 2 (normalizedSphere m) := by
  let := normalizedSphere_probability m
  have hc : Continuous (fun z : ComplexUnitSphere m => sourceBasisFunction T z.val) :=
    (sourceBasisFunction_continuous T).comp continuous_subtype_val
  exact hc.memLp_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))

theorem audit_basis_index_card (m N : ℕ) :
    Fintype.card (Set.powersetCard (Fin (N+m)) m) = (N+m).choose m ∧
      0 < Fintype.card (Set.powersetCard (Fin (N+m)) m) := by
  have h := (Fintype.card_congr (starsBarsEquiv m N)).symm.trans (degreeIndices_card m N)
  refine ⟨h, ?_⟩
  rw [h]
  exact Nat.choose_pos (by omega)

theorem audit_coefficient_recovery {m N : ℕ} (hm : 0 < m)
    (a : Set.powersetCard (Fin (N+m)) m → ℂ)
    (U : Set.powersetCard (Fin (N+m)) m) :
    (∫ z : ComplexUnitSphere m,
      (∑ T, a T * sourceBasisFunction T z.val) * star (sourceBasisFunction U z.val)
      ∂normalizedSphere m) = a U := by
  classical
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun T _ => (sourceBasisFunction_gram_integrable T U).const_mul (a T))]
  simp_rw [integral_const_mul, sourceBasisFunction_gram hm]
  simp

theorem audit_L2_coefficient_independence {m N : ℕ} (hm : 0 < m)
    (a : Set.powersetCard (Fin (N+m)) m → ℂ)
    (ha : ∀ᵐ z : ComplexUnitSphere m ∂normalizedSphere m,
      (∑ T, a T * sourceBasisFunction T z.val) = 0) : ∀ U, a U = 0 := by
  intro U
  have hz : (∫ z : ComplexUnitSphere m,
      (∑ T, a T * sourceBasisFunction T z.val) * star (sourceBasisFunction U z.val)
      ∂normalizedSphere m) = 0 := by
    calc
      _ = ∫ _z : ComplexUnitSphere m, (0:ℂ) ∂normalizedSphere m :=
        integral_congr_ae (ha.mono (fun z h => by rw [h, zero_mul]))
      _ = 0 := integral_zero _ _
  exact (audit_coefficient_recovery hm a U).symm.trans hz

theorem audit_basis_linearIndependent {m N : ℕ} (hm : 0 < m) :
    LinearIndependent ℂ (sourceBasisFunction (m:=m) (N:=N)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha U
  have hpoint (z : ComplexEuclidean m) :
      (∑ T, a T * sourceBasisFunction T z) = 0 := by
    have h := congrFun ha z
    simpa using h
  have h := audit_coefficient_recovery hm a U
  simp_rw [hpoint, zero_mul, integral_zero] at h
  exact h.symm

set_option pp.proofs false in
#print uniformly_bounded_homogeneous_basis
set_option pp.proofs false in
#print audit_final_contract
#print ExplicitBourgainBasis
#print homogeneousPolynomialSpace
#print homogeneousMonomial
#print normalizedSphere
#print sourceFourier
#print monomialNormalization
#print axioms uniformly_bounded_homogeneous_basis
#print axioms explicitBourgainBasis_proved
#print axioms audit_final_contract
#print axioms audit_basis_functions_holomorphic
#print axioms audit_coordinate_gaussian_integrable
#print axioms audit_basis_linearIndependent
#print axioms audit_actual_L2_membership
#print axioms audit_L2_coefficient_independence
#check multinomial_cancellation
#check sphere_monomial_moment
#check sourceBasisFunction_uniform_bound
#check sourceBasisFunction_span
#check sourceBasisFunction_gram_integrable

#print axioms audit_final_dimension

#print axioms audit_actual_polynomial_formula

#print axioms audit_sphere_measure_nondegenerate

#print axioms audit_gram_nonzero

#print axioms audit_basis_index_card

#print axioms audit_coefficient_recovery
