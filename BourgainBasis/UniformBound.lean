module
public import BourgainBasis.MonomialPhase

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- Exact finite expansion into the already bounded multinomial sums. -/
theorem sourceBasisFunction_multinomial {m N : ℕ}
    (T : Set.powersetCard (Fin (N+m)) m) (z : ComplexEuclidean m) :
    sourceBasisFunction T z =
      ((Real.sqrt ((N+m:ℕ):ℝ):ℂ)⁻¹)^m * (Real.sqrt ((N+m).choose m:ℝ):ℂ) *
      ∑ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ:ℂ)*phase (sourcePermutationConstant T σ)*
        multinomialSum (N:=N) (coordinateProbability z)
          (fun k => sourcePermutationFrequency T σ k + coordinatePhase z k) := by
  unfold sourceBasisFunction basisCoefficient
  simp_rw [source_minor_affine_expansion,normalizedMonomial_polar]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  unfold multinomialSum
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  simp_rw [add_mul,Finset.sum_add_distrib,phase_add]
  ring

/-- The explicit manuscript functions have a degree-uniform closed-ball bound. -/
theorem sourceBasisFunction_uniform_bound (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,∀ T : Set.powersetCard (Fin (N+m)) m,
      ∀ z : ComplexEuclidean m, ‖z‖≤1 → ‖sourceBasisFunction T z‖≤C := by
  obtain ⟨C,hC,hbound⟩ := multinomial_cancellation m hm
  refine ⟨Real.sqrt (m.factorial:ℝ)*C,by positivity,?_⟩
  intro N T z hz
  apply homogeneous_closedBall_bound (sourceBasisFunction T) N _
    (fun t _ z => sourceBasisFunction_smul T t z) _ z hz
  intro u hu
  have hsum : ‖∑ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ:ℂ)*phase (sourcePermutationConstant T σ)*
      multinomialSum (N:=N) (coordinateProbability u)
        (fun k => sourcePermutationFrequency T σ k+coordinatePhase u k)‖ ≤ (m.factorial:ℝ)*C := by
    calc
      _ ≤ ∑ σ : Equiv.Perm (Fin m), ‖(Equiv.Perm.sign σ:ℂ)*phase (sourcePermutationConstant T σ)*
        multinomialSum (N:=N) (coordinateProbability u)
          (fun k => sourcePermutationFrequency T σ k+coordinatePhase u k)‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Equiv.Perm (Fin m), C := by
        apply Finset.sum_le_sum
        intro σ _
        rw [norm_mul,norm_mul,norm_phase,mul_one]
        have hs : ‖(Equiv.Perm.sign σ:ℂ)‖=1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h|h <;> simp [h]
        rw [hs,one_mul]
        exact hbound N (coordinateProbability u) (fun i => sq_nonneg _) (coordinateProbability_sum u hu) _
      _ = _ := by simp [Fintype.card_perm]
  rw [sourceBasisFunction_multinomial,norm_mul,norm_mul,norm_pow,norm_inv,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (Real.sqrt ((N+m:ℕ):ℝ))⁻¹^m * Real.sqrt ((N+m).choose m:ℝ)*((m.factorial:ℝ)*C) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((m.factorial:ℝ)*((Real.sqrt (N+m:ℝ))^m)⁻¹ * Real.sqrt ((N+m).choose m:ℝ))*C := by
      push_cast
      rw [inv_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (determinant_normalization_bound N m hm) hC.le

end BourgainBasis
