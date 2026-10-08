module
public import BourgainBasis.PoissonGlobal

@[expose] public section

noncomputable section
namespace BourgainBasis

/-- A uniform recurrence bound with an extra distance polynomial. This costs
three powers of decay but retains the required inverse-square-root scale. -/
theorem global_recurrence_ratio {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) :
    |μ/((n:ℝ)+1)-1| ≤ (64/Real.sqrt (1+μ)) *
      (1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^3 := by
  let M := Real.sqrt (1+μ)
  let W := 1+|(n:ℝ)-μ|/M
  have hM : 0<M := Real.sqrt_pos.mpr (by positivity)
  have hM₁ : 1≤M := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ)≤1+μ by linarith)
    simpa [M] using h
  have hM₂ : M^2=1+μ := Real.sq_sqrt (by positivity)
  have hW₁ : 1≤W := by
    dsimp [W]
    linarith [div_nonneg (abs_nonneg ((n:ℝ)-μ)) hM.le]
  have hW : 0<W := by linarith
  have hWpow : W ≤ W^3 := by nlinarith [sq_nonneg (W-1)]
  by_cases hc : 2≤μ ∧ μ≤2*(n:ℝ)
  · have h := central_recurrence_ratio hc.1 n hc.2
    change _ ≤ (64/M)*W^3
    apply h.trans
    change (4/M)*W ≤ _
    exact mul_le_mul (div_le_div_of_nonneg_right (by norm_num : (4:ℝ)≤64) hM.le) hWpow hW.le (by positivity)
  have hMW : M ≤ 4*W := by
    by_cases hs : μ≤2
    · have : M≤2 := by nlinarith
      linarith
    have hl : 2*(n:ℝ)<μ := by
      by_contra! hh
      exact hc ⟨by linarith, hh⟩
    have hd : μ/2 ≤ |(n:ℝ)-μ| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have he : M*W = M+|(n:ℝ)-μ| := by dsimp [W]; field_simp
    nlinarith
  have hraw : |μ/((n:ℝ)+1)-1| ≤ M^2 := by
    have ht : μ/((n:ℝ)+1) ≤ μ := div_le_self hμ (by norm_num)
    rw [hM₂]
    apply abs_le.mpr
    constructor
    · linarith [div_nonneg hμ (show 0≤(n:ℝ)+1 by positivity)]
    · linarith
  apply hraw.trans
  change M^2 ≤ (64/M)*W^3
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hM).mpr
  have hcube := pow_le_pow_left₀ hM.le hMW 3
  nlinarith

/-- Complete first-difference decay at every natural index and mean. -/
theorem profileNat_global_first_decay {μ : ℝ} (hμ : 0≤μ) (n R : ℕ) :
    |profileNat μ (n+1)-profileNat μ n| ≤
      (64*globalProfileConstant (R+3)) * (Real.sqrt (1+μ))⁻¹ *
        ((1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^R)⁻¹ := by
  let M := Real.sqrt (1+μ)
  let W := 1+|(n:ℝ)-μ|/M
  have hM : 0<M := Real.sqrt_pos.mpr (by positivity)
  have hW : 0<W := by dsimp [W]; positivity
  have hC := (globalProfileConstant_pos (R+3)).le
  calc
    _ ≤ profileNat μ n * |μ/((n:ℝ)+1)-1| := profile_first_difference hμ n
    _ ≤ (globalProfileConstant (R+3)*(W^(R+3))⁻¹) * ((64/M)*W^3) :=
      mul_le_mul (profileNat_global_decay hμ n (R+3)) (global_recurrence_ratio hμ n)
        (abs_nonneg _) (by positivity)
    _ = _ := by
      change _ = (64*globalProfileConstant (R+3))*M⁻¹*(W^R)⁻¹
      rw [pow_add]
      field_simp

/-- The boundary stencil at -1 retains the inverse scale, using one extra
power from the already proved global profile envelope. -/
theorem profile_boundary_first_decay {μ : ℝ} (hμ : 0≤μ) (R : ℕ) :
    profileNat μ 0 ≤ ((2:ℝ)^R*globalProfileConstant (R+1)) *
      (Real.sqrt (1+μ))⁻¹ *
        ((1+|(-1:ℝ)-μ|/Real.sqrt (1+μ))^R)⁻¹ := by
  let M := Real.sqrt (1+μ)
  let W := 1+μ/M
  let V := 1+(1+μ)/M
  have hM : 0<M := Real.sqrt_pos.mpr (by positivity)
  have hM₁ : 1≤M := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ)≤1+μ by linarith)
    simpa [M] using h
  have hM₂ : M^2=1+μ := Real.sq_sqrt (by positivity)
  have hW : 0<W := by dsimp [W]; positivity
  have hV : 0<V := by dsimp [V]; positivity
  have he : M*W=M+μ := by dsimp [W]; field_simp
  have hMW : M≤W := by nlinarith
  have hVW : V≤2*W := by
    have hev : M*V=M+1+μ := by dsimp [V]; field_simp; ring
    nlinarith
  have hC := (globalProfileConstant_pos (R+1)).le
  have hp := profileNat_global_decay hμ 0 (R+1)
  simp only [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hμ] at hp
  have hab : |(-1:ℝ)-μ|=1+μ := by rw [abs_of_nonpos (by linarith)]; ring
  rw [hab]
  change profileNat μ 0 ≤ ((2:ℝ)^R*globalProfileConstant (R+1))*M⁻¹*(V^R)⁻¹
  rw [mul_assoc, ← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (mul_pos hM (pow_pos hV R))).mpr
  calc
    _ ≤ (globalProfileConstant (R+1)*(W^(R+1))⁻¹) * (W*((2*W)^R)) := by
      apply mul_le_mul hp _ (by positivity) (by positivity)
      exact mul_le_mul hMW (pow_le_pow_left₀ hV.le hVW R) (by positivity) (by positivity)
    _ = _ := by rw [pow_succ, mul_pow]; field_simp

/-- Explicit first-difference constant, depending only on R. -/
def globalFirstConstant (R : ℕ) : ℝ :=
  64*globalProfileConstant (R+3) + (2:ℝ)^R*globalProfileConstant (R+1)

theorem globalFirstConstant_pos (R : ℕ) : 0<globalFirstConstant R := by
  have h₁ := globalProfileConstant_pos (R+3)
  have h₂ := globalProfileConstant_pos (R+1)
  unfold globalFirstConstant
  positivity

/-- Full global order-one decay: every nonnegative mean and every integer
index, including the boundary stencil at -1 and the zero extension to its left. -/
theorem profile_global_first_decay {μ : ℝ} (hμ : 0≤μ) (n : ℤ) (R : ℕ) :
    |(deltaOne^[1]) (profile μ) n| ≤ globalFirstConstant R *
      (Real.sqrt (1+μ))⁻¹ *
        ((1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^R)⁻¹ := by
  have h₁ := (globalProfileConstant_pos (R+3)).le
  have h₂ := (globalProfileConstant_pos (R+1)).le
  by_cases hn : 0≤n
  · obtain ⟨k,rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have h := profileNat_global_first_decay hμ k R
    simp only [Function.iterate_one, deltaOne,
      show (k:ℤ)+1=((k+1:ℕ):ℤ) by push_cast; ring, profile_nat]
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    unfold globalFirstConstant
    linarith [mul_nonneg (show (0:ℝ)≤2^R by positivity) h₂]
  by_cases he : n = -1
  · subst n
    have hid : (deltaOne^[1]) (profile μ) (-1) = profileNat μ 0 := by
      simp [deltaOne, profile]
    rw [hid, abs_of_nonneg (profileNat_nonneg μ 0)]
    apply (profile_boundary_first_decay hμ R).trans
    norm_num only [Int.cast_neg, Int.cast_one]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    unfold globalFirstConstant
    linarith
  have hz := profile_difference_vanishes_left μ 1 n (by omega)
  rw [hz, abs_zero]
  exact mul_nonneg (mul_nonneg (globalFirstConstant_pos R).le (by positivity)) (by positivity)

/-- Exact j=1 specialization of the global source contract, proved without
assuming any analytic input beyond the established profile definitions. -/
theorem poissonProfileEstimate_order_one (R : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ μ : ℝ, 0≤μ → ∀ n : ℤ,
      |(deltaOne^[1]) (profile μ) n| ≤ C * (Real.sqrt (1+μ)^1)⁻¹ *
        ((1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^R)⁻¹ := by
  refine ⟨globalFirstConstant R, globalFirstConstant_pos R, ?_⟩
  intro μ hμ n
  simpa using profile_global_first_decay hμ n R

end BourgainBasis
