module
public import BourgainBasis.PoissonGlobalSecond

@[expose] public section

noncomputable section
namespace BourgainBasis

/-- A simple finite-index growth bound, useful only for boundary stencils. -/
theorem profileNat_le_zero_scale {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    profileNat μ k ≤ profileNat μ 0*(Real.sqrt (1+μ))^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : (0:ℝ)<(k:ℝ)+1 := by positivity
    have hr : μ/((k:ℝ)+1) ≤ 1+μ := by
      apply (div_le_iff₀ hk).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) k, mul_nonneg hμ (Nat.cast_nonneg (α := ℝ) k)]
    rw [profileNat_succ hμ]
    calc
      _ ≤ (profileNat μ 0*(Real.sqrt (1+μ))^k)*Real.sqrt (1+μ) :=
        mul_le_mul ih (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _) (mul_nonneg (profileNat_nonneg μ 0) (pow_nonneg (Real.sqrt_nonneg _) _))
      _ = _ := by rw [pow_succ]; ring

def negativeProfileConstant (j R : ℕ) : ℝ :=
  (2:ℝ)^j*((j:ℝ)+1)^R*globalProfileConstant (R+2*j)

theorem negativeProfileConstant_pos (j R : ℕ) : 0 < negativeProfileConstant j R := by
  have hh := globalProfileConstant_pos (R+2*j)
  unfold negativeProfileConstant
  positivity

/-- Every negative crossing stencil, all orders, with the actual inverse-scale
and decay factors. Stencils entirely to the left vanish exactly. -/
theorem profile_negative_all_orders {μ : ℝ} (hμ : 0 ≤ μ) (j R : ℕ) (n : ℤ)
    (hn : n<0) :
    |(deltaOne^[j]) (profile μ) n| ≤ negativeProfileConstant j R *
      ((Real.sqrt (1+μ))^j)⁻¹ *
        ((1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^R)⁻¹ := by
  let M := Real.sqrt (1+μ)
  let W := 1+|(n:ℝ)-μ|/M
  let V := 1+((j:ℝ)+μ)/M
  have hM : 0<M := Real.sqrt_pos.mpr (by positivity)
  have hM₁ : 1≤M := by
    have hh := Real.sqrt_le_sqrt (show (1:ℝ)≤1+μ by linarith)
    simpa [M] using hh
  have hW : 0<W := by dsimp [W]; positivity
  have hV : 0<V := by dsimp [V]; positivity
  by_cases hjn : n < -(j:ℤ)
  · rw [profile_difference_vanishes_left μ j n hjn, abs_zero]
    exact mul_nonneg (mul_nonneg (negativeProfileConstant_pos j R).le
      (inv_nonneg.mpr (pow_nonneg hM.le _))) (inv_nonneg.mpr (pow_nonneg hW.le _))
  have hlocal (r : ℕ) (hr : r≤j) : |profile μ (n+r)| ≤ profileNat μ 0*M^j := by
    by_cases hnr : 0≤n+(r:ℤ)
    · have hk : (n+(r:ℤ)).toNat ≤ j := by omega
      rw [profile, ite_eq_left hnr, abs_of_nonneg (profileNat_nonneg μ _)]
      exact (profileNat_le_zero_scale hμ _).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM₁ hk) (profileNat_nonneg μ _))
    · rw [profile, ite_eq_right hnr, abs_zero]
      exact mul_nonneg (profileNat_nonneg μ 0) (pow_nonneg hM.le _)
  have hb := difference_local_bound (profile μ) j n (profileNat μ 0*M^j) hlocal
  have hzero := profile_zero_boundary_decay hμ j (2*j) R
  have hWV : W≤V := by
    have hnR : (n:ℝ)<0 := by exact_mod_cast hn
    have hjnR : -(j:ℝ)≤(n:ℝ) := by exact_mod_cast (le_of_not_gt hjn)
    dsimp [W, V]
    rw [abs_of_nonpos (by linarith : (n:ℝ)-μ≤0)]
    have hd : (-((n:ℝ)-μ))/M ≤ ((j:ℝ)+μ)/M :=
      div_le_div_of_nonneg_right (by linarith) hM.le
    linarith
  have hdecay : (V^R)⁻¹ ≤ (W^R)⁻¹ := inv_le_inv₀ (pow_pos hV _) (pow_pos hW _) |>.mpr
    (pow_le_pow_left₀ hW.le hWV _)
  change _ ≤ negativeProfileConstant j R*(M^j)⁻¹*(W^R)⁻¹
  calc
    _ ≤ (2:ℝ)^j*(profileNat μ 0*M^j) := hb
    _ ≤ (2:ℝ)^j*(((((j:ℝ)+1)^R*globalProfileConstant (R+2*j)) * (M^(2*j))⁻¹ * (V^R)⁻¹)*M^j) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hzero (pow_nonneg hM.le _)) (by positivity)
    _ = negativeProfileConstant j R*(M^j)⁻¹*(V^R)⁻¹ := by
      unfold negativeProfileConstant
      rw [show 2*j=j+j by omega, pow_add]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay
      (mul_nonneg (negativeProfileConstant_pos j R).le (inv_nonneg.mpr (pow_nonneg hM.le _)))

end BourgainBasis
