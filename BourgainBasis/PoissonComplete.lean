module
public import BourgainBasis.PoissonAllOrders
public import BourgainBasis.PoissonNegativeBoundary

@[expose] public section

noncomputable section
namespace BourgainBasis

/-- The full manuscript profile contract, all orders, decay exponents, means and
integer indices, proved from the natural-index induction and boundary stencils. -/
theorem poissonProfileEstimate_proved : PoissonProfileEstimate := by
  intro j R
  obtain ⟨C,hC,hmain⟩ := profile_nonnegative_all_orders j R
  refine ⟨C+negativeProfileConstant j R, add_pos hC (negativeProfileConstant_pos j R), ?_⟩
  intro μ hμ n
  have hM : 0<Real.sqrt (1+μ) := Real.sqrt_pos.mpr (by positivity)
  have hW : 0<1+|(n:ℝ)-μ|/Real.sqrt (1+μ) := by positivity
  have hscale : 0≤((Real.sqrt (1+μ))^j)⁻¹ := inv_nonneg.mpr (pow_nonneg hM.le _)
  have hdecay : 0≤((1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^R)⁻¹ := inv_nonneg.mpr (pow_nonneg hW.le _)
  by_cases hn : 0≤n
  · have hh := hmain μ hμ n.toNat
    rw [Int.toNat_of_nonneg hn] at hh
    have hcast : ((n.toNat:ℕ):ℝ)=(n:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
    rw [hcast] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith [negativeProfileConstant_pos j R]) hscale) hdecay)
  · exact (profile_negative_all_orders hμ j R n (lt_of_not_ge hn)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hscale) hdecay)

end BourgainBasis
