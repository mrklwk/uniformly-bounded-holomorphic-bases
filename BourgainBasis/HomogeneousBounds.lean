module
public import BourgainBasis.Contracts

@[expose] public section

noncomputable section
namespace BourgainBasis

/-- A homogeneous sphere bound extends to the closed ball, including degree zero
and the origin; no continuity or polynomial representation is assumed. -/
theorem homogeneous_closedBall_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] (f : E → ℂ) (N : ℕ) (C : ℝ)
    (hhom : ∀ (t : ℝ), 0 ≤ t → ∀ z, f (t • z) = (t:ℂ)^N*f z)
    (hbound : ∀ z, ‖z‖=1 → ‖f z‖ ≤ C) (z : E) (hz : ‖z‖ ≤ 1) :
    ‖f z‖ ≤ C := by
  by_cases hz0 : z=0
  · subst z
    obtain ⟨v,hv⟩ := exists_norm_eq (E := E) (by norm_num : (0:ℝ)≤1)
    have hh := hhom 0 (by norm_num) v
    simp only [zero_smul, Complex.ofReal_zero] at hh
    rw [hh, norm_mul, norm_pow, norm_zero]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num))
      (norm_nonneg _)).trans (by simpa using hbound v hv)
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    let u : E := ‖z‖⁻¹ • z
    have hu : ‖u‖=1 := by
      simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn]
      exact inv_mul_cancel₀ hn.ne'
    have hz' : ‖z‖ • u = z := by simp [u, smul_smul, hn.ne']
    have hh := hhom ‖z‖ hn.le u
    rw [hz'] at hh
    rw [hh, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
    calc
      _ ≤ 1*‖f u‖ := mul_le_mul_of_nonneg_right (pow_le_one₀ hn.le hz) (norm_nonneg _)
      _ ≤ C := by simpa using hbound u hu

end BourgainBasis
