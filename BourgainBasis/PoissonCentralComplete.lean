module
public import BourgainBasis.PoissonDecay

@[expose] public section

noncomputable section
namespace BourgainBasis

/-- The recurrence ratio has one inverse-scale gain throughout μ≤2n. -/
theorem central_recurrence_ratio {μ : ℝ} (hμ : 2 ≤ μ) (n : ℕ)
    (hcenter : μ ≤ 2 * (n : ℝ)) :
    |μ/((n:ℝ)+1)-1| ≤ (4 / Real.sqrt (1+μ)) *
      (1 + |(n:ℝ)-μ| / Real.sqrt (1+μ)) := by
  let M := Real.sqrt (1+μ)
  let D := |(n:ℝ)-μ|
  have hμ₀ : 0 < μ := by linarith
  have hM : 0 < M := Real.sqrt_pos.mpr (by linarith)
  have hM₁ : 1 ≤ M := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1+μ by linarith)
    simpa [M] using h
  have hM₂ : M^2 = 1+μ := Real.sq_sqrt (by linarith)
  have hD : 0 ≤ D := abs_nonneg _
  have hx : (0:ℝ)<n+1 := by positivity
  have ht : |μ-((n:ℝ)+1)| ≤ D+1 := by
    have hh := abs_sub_le μ (n:ℝ) ((n:ℝ)+1)
    simpa [D, abs_sub_comm μ (n:ℝ)] using hh
  have hab : |μ/((n:ℝ)+1)-1| ≤ 2*(D+1)/μ := by
    have hid : μ/((n:ℝ)+1)-1 = (μ-((n:ℝ)+1))/((n:ℝ)+1) := by field_simp
    rw [hid, abs_div, abs_of_pos hx]
    apply (div_le_div_iff₀ hx hμ₀).mpr
    calc
      _ ≤ (D+1)*μ := mul_le_mul_of_nonneg_right ht hμ₀.le
      _ ≤ _ := by nlinarith
  have h₁ : (D+1)/μ ≤ 2*(D+M)/M^2 := by
    apply (div_le_div_iff₀ hμ₀ (sq_pos_of_pos hM)).mpr
    rw [hM₂]
    nlinarith [mul_nonneg (show 0 ≤ μ-1 by linarith) (show 0 ≤ D+1 by linarith),
      mul_nonneg hμ₀.le (show 0 ≤ M-1 by linarith)]
  calc
    _ ≤ 2*((D+1)/μ) := by convert hab using 1; ring
    _ ≤ 2*(2*(D+M)/M^2) := by gcongr
    _ = _ := by change _ = (4/M)*(1+D/M); field_simp; ring

/-- The adjacent-ratio curvature has two inverse-scale gains. -/
theorem central_recurrence_curvature {μ : ℝ} (hμ : 2 ≤ μ) (n : ℕ)
    (hcenter : μ ≤ 2 * (n : ℝ)) :
    μ/(((n:ℝ)+1)*((n:ℝ)+2)) ≤ 8 / (Real.sqrt (1+μ))^2 := by
  have hμ₀ : 0 < μ := by linarith
  have hx : (0:ℝ)<n+1 := by positivity
  have hy : (0:ℝ)<n+2 := by positivity
  have h : μ/(((n:ℝ)+1)*((n:ℝ)+2)) ≤ 4/μ := by
    apply (div_le_div_iff₀ (mul_pos hx hy) hμ₀).mpr
    have hh : μ^2 ≤ (2*(n:ℝ))^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  apply h.trans
  rw [Real.sq_sqrt (show 0 ≤ 1+μ by linarith)]
  apply (div_le_div_iff₀ hμ₀ (by linarith)).mpr
  linarith

/-- The complete second recurrence factor retains two inverse-scale gains. -/
theorem central_second_recurrence_factor {μ : ℝ} (hμ : 2 ≤ μ) (n : ℕ)
    (hcenter : μ ≤ 2 * (n : ℝ)) :
    (μ/((n:ℝ)+1)-1)^2 + μ/(((n:ℝ)+1)*((n:ℝ)+2)) ≤
      (24 / (Real.sqrt (1+μ))^2) *
        (1 + |(n:ℝ)-μ| / Real.sqrt (1+μ))^2 := by
  let M := Real.sqrt (1+μ)
  let W := 1 + |(n:ℝ)-μ| / M
  have hM : 0 < M := Real.sqrt_pos.mpr (by linarith)
  have hW : 1 ≤ W := by
    dsimp [W]
    linarith [div_nonneg (abs_nonneg ((n:ℝ)-μ)) hM.le]
  have h := central_recurrence_ratio hμ n hcenter
  have hs := pow_le_pow_left₀ (abs_nonneg (μ/((n:ℝ)+1)-1)) h 2
  rw [sq_abs] at hs
  have hc := central_recurrence_curvature hμ n hcenter
  change (μ/((n:ℝ)+1)-1)^2 ≤ ((4/M)*W)^2 at hs
  change μ/(((n:ℝ)+1)*((n:ℝ)+2)) ≤ 8/M^2 at hc
  change _ ≤ (24/M^2)*W^2
  calc
    _ ≤ ((4/M)*W)^2 + 8/M^2 := add_le_add hs hc
    _ ≤ ((4/M)*W)^2 + (8/M^2)*W^2 := by
      have hw : (1:ℝ) ≤ W^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hw (show 0 ≤ 8/M^2 by positivity)]
    _ = _ := by field_simp; ring

/-- The full source-shaped central order-one estimate, with constants only
in the requested decay order R, not the degree, index, or mean. -/
theorem profile_central_first_decay {μ : ℝ} (hμ : 2 ≤ μ) (n : ℕ)
    (hleft : μ ≤ 2 * (n:ℝ)) (hright : (n:ℝ) ≤ 4*μ) (R : ℕ) :
    |profileNat μ (n+1)-profileNat μ n| ≤
      (8 * (40:ℝ)^(R+1) * ((R+1).factorial:ℝ) * Real.exp (1/20)) *
        (Real.sqrt (1+μ))⁻¹ *
        ((1 + |(n:ℝ)-μ| / Real.sqrt (1+μ))^R)⁻¹ := by
  have hμ₀ : 0 < μ := by linarith
  have hn : 0 < n := by
    by_contra! h
    simp only [Nat.le_zero.mp h, Nat.cast_zero, mul_zero] at hleft
    linarith
  let M := Real.sqrt (1+μ)
  let W := 1 + |(n:ℝ)-μ| / M
  have hM : 0 < M := Real.sqrt_pos.mpr (by linarith)
  have hW : 0 < W := by dsimp [W]; positivity
  have hp := profile_central_decay hμ₀ n hn hleft hright (R+1)
  have hr := central_recurrence_ratio hμ n hleft
  calc
    _ ≤ profileNat μ n * |μ/((n:ℝ)+1)-1| := profile_first_difference hμ₀.le n
    _ ≤ ((2*(40:ℝ)^(R+1)*((R+1).factorial:ℝ)*Real.exp (1/20)) * (W^(R+1))⁻¹) * ((4/M)*W) :=
      mul_le_mul hp hr (abs_nonneg _) (by positivity)
    _ = _ := by
      change _ = (8*(40:ℝ)^(R+1)*((R+1).factorial:ℝ)*Real.exp (1/20))*M⁻¹*(W^R)⁻¹
      rw [pow_succ]
      field_simp
      ring

/-- The full source-shaped central order-two estimate, retaining the
M⁻² gain while absorbing the recurrence's distance polynomial. -/
theorem profile_central_second_decay {μ : ℝ} (hμ : 2 ≤ μ) (n : ℕ)
    (hleft : μ ≤ 2 * (n:ℝ)) (hright : (n:ℝ) ≤ 4*μ) (R : ℕ) :
    |profileNat μ (n+2)-2*profileNat μ (n+1)+profileNat μ n| ≤
      (48 * (40:ℝ)^(R+2) * ((R+2).factorial:ℝ) * Real.exp (1/20)) *
        ((Real.sqrt (1+μ))^2)⁻¹ *
        ((1 + |(n:ℝ)-μ| / Real.sqrt (1+μ))^R)⁻¹ := by
  have hμ₀ : 0 < μ := by linarith
  have hn : 0 < n := by
    by_contra! h
    simp only [Nat.le_zero.mp h, Nat.cast_zero, mul_zero] at hleft
    linarith
  let M := Real.sqrt (1+μ)
  let W := 1 + |(n:ℝ)-μ| / M
  have hM : 0 < M := Real.sqrt_pos.mpr (by linarith)
  have hW : 0 < W := by dsimp [W]; positivity
  have hp := profile_central_decay hμ₀ n hn hleft hright (R+2)
  have hr := central_second_recurrence_factor hμ n hleft
  calc
    _ ≤ profileNat μ n * ((μ/((n:ℝ)+1)-1)^2 + μ/(((n:ℝ)+1)*((n:ℝ)+2))) := profile_second_difference hμ₀.le n
    _ ≤ ((2*(40:ℝ)^(R+2)*((R+2).factorial:ℝ)*Real.exp (1/20)) * (W^(R+2))⁻¹) * ((24/M^2)*W^2) :=
      mul_le_mul hp hr (by positivity) (by positivity)
    _ = _ := by
      change _ = (48*(40:ℝ)^(R+2)*((R+2).factorial:ℝ)*Real.exp (1/20))*(M^2)⁻¹*(W^R)⁻¹
      rw [pow_add]
      field_simp
      ring

/-- Order-one source estimate for the actual integer zero-extended profile. -/
theorem profile_central_first_decay_int {μ : ℝ} (hμ : 2 ≤ μ) (n : ℕ)
    (hleft : μ ≤ 2 * (n:ℝ)) (hright : (n:ℝ) ≤ 4*μ) (R : ℕ) :
    |(deltaOne^[1]) (profile μ) (n:ℤ)| ≤
      (8 * (40:ℝ)^(R+1) * ((R+1).factorial:ℝ) * Real.exp (1/20)) *
        (Real.sqrt (1+μ))⁻¹ *
        ((1 + |(n:ℝ)-μ| / Real.sqrt (1+μ))^R)⁻¹ := by
  simpa only [Function.iterate_one, deltaOne,
    show (n:ℤ)+1=((n+1:ℕ):ℤ) by push_cast; ring, profile_nat]
    using profile_central_first_decay hμ n hleft hright R

/-- Order-two source estimate for the actual integer zero-extended profile. -/
theorem profile_central_second_decay_int {μ : ℝ} (hμ : 2 ≤ μ) (n : ℕ)
    (hleft : μ ≤ 2 * (n:ℝ)) (hright : (n:ℝ) ≤ 4*μ) (R : ℕ) :
    |(deltaOne^[2]) (profile μ) (n:ℤ)| ≤
      (48 * (40:ℝ)^(R+2) * ((R+2).factorial:ℝ) * Real.exp (1/20)) *
        ((Real.sqrt (1+μ))^2)⁻¹ *
        ((1 + |(n:ℝ)-μ| / Real.sqrt (1+μ))^R)⁻¹ := by
  have hid : (deltaOne^[2]) (profile μ) (n:ℤ) =
      profileNat μ (n+2)-2*profileNat μ (n+1)+profileNat μ n := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, deltaOne]
    rw [show (n:ℤ)+1+1=((n+2:ℕ):ℤ) by push_cast; ring,
      show (n:ℤ)+1=((n+1:ℕ):ℤ) by push_cast; ring]
    rw [profile_nat, profile_nat, profile_nat]
    ring
  rw [hid]
  exact profile_central_second_decay hμ n hleft hright R

end BourgainBasis
