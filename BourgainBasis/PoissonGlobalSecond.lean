module
public import BourgainBasis.PoissonGlobalFirst

@[expose] public section

noncomputable section
namespace BourgainBasis

/-- Global curvature control with two inverse-scale powers, trading four
powers of the distance envelope. -/
theorem global_recurrence_curvature {μ : ℝ} (hμ : 0≤μ) (n : ℕ) :
    μ/(((n:ℝ)+1)*((n:ℝ)+2)) ≤
      (256/(Real.sqrt (1+μ))^2)*(1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^4 := by
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
  have hW4 : (1:ℝ)≤W^4 := one_le_pow₀ hW₁
  by_cases hc : 2≤μ ∧ μ≤2*(n:ℝ)
  · apply (central_recurrence_curvature hc.1 n hc.2).trans
    change 8/M^2 ≤ (256/M^2)*W^4
    calc
      _ ≤ 256/M^2 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hW4 (show 0≤256/M^2 by positivity)]
  have hMW : M≤4*W := by
    by_cases hs : μ≤2
    · have : M≤2 := by nlinarith
      linarith
    have hl : 2*(n:ℝ)<μ := by
      by_contra! hh
      exact hc ⟨by linarith,hh⟩
    have hd : μ/2≤|(n:ℝ)-μ| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have he : M*W=M+|(n:ℝ)-μ| := by dsimp [W]; field_simp
    nlinarith
  have hraw : μ/(((n:ℝ)+1)*((n:ℝ)+2)) ≤ M^2 := by
    have ht : μ/(((n:ℝ)+1)*((n:ℝ)+2))≤μ :=
      div_le_self hμ (by nlinarith [Nat.cast_nonneg (α:=ℝ) n])
    linarith
  apply hraw.trans
  change M^2≤(256/M^2)*W^4
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hM)).mpr
  have hp := pow_le_pow_left₀ hM.le hMW 4
  nlinarith

/-- The complete second recurrence factor has a global inverse-scale-square
bound, using six extra distance powers. -/
theorem global_second_recurrence_factor {μ : ℝ} (hμ : 0≤μ) (n : ℕ) :
    (μ/((n:ℝ)+1)-1)^2 + μ/(((n:ℝ)+1)*((n:ℝ)+2)) ≤
      (4352/(Real.sqrt (1+μ))^2)*(1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^6 := by
  let M := Real.sqrt (1+μ)
  let W := 1+|(n:ℝ)-μ|/M
  have hM : 0<M := Real.sqrt_pos.mpr (by positivity)
  have hW₁ : 1≤W := by
    dsimp [W]
    linarith [div_nonneg (abs_nonneg ((n:ℝ)-μ)) hM.le]
  have hW : 0<W := by linarith
  have h46 : W^4≤W^6 := pow_le_pow_right₀ hW₁ (by omega)
  have hr := global_recurrence_ratio hμ n
  have hs := pow_le_pow_left₀ (abs_nonneg (μ/((n:ℝ)+1)-1)) hr 2
  rw [sq_abs] at hs
  have hc := global_recurrence_curvature hμ n
  change _ ≤ ((64/M)*W^3)^2 at hs
  change _ ≤ (256/M^2)*W^4 at hc
  change _ ≤ (4352/M^2)*W^6
  calc
    _ ≤ ((64/M)*W^3)^2 + (256/M^2)*W^4 := add_le_add hs hc
    _ ≤ ((64/M)*W^3)^2 + (256/M^2)*W^6 := by gcongr
    _ = _ := by field_simp; ring

/-- Exact global second-difference decay at all natural indices. -/
theorem profileNat_global_second_decay {μ : ℝ} (hμ : 0≤μ) (n R : ℕ) :
    |profileNat μ (n+2)-2*profileNat μ (n+1)+profileNat μ n| ≤
      (4352*globalProfileConstant (R+6)) * ((Real.sqrt (1+μ))^2)⁻¹ *
        ((1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^R)⁻¹ := by
  let M := Real.sqrt (1+μ)
  let W := 1+|(n:ℝ)-μ|/M
  have hM : 0<M := Real.sqrt_pos.mpr (by positivity)
  have hW : 0<W := by dsimp [W]; positivity
  have hC := (globalProfileConstant_pos (R+6)).le
  calc
    _ ≤ profileNat μ n*((μ/((n:ℝ)+1)-1)^2+μ/(((n:ℝ)+1)*((n:ℝ)+2))) := profile_second_difference hμ n
    _ ≤ (globalProfileConstant (R+6)*(W^(R+6))⁻¹)*((4352/M^2)*W^6) :=
      mul_le_mul (profileNat_global_decay hμ n (R+6)) (global_second_recurrence_factor hμ n)
        (by positivity) (by positivity)
    _ = _ := by
      change _ = (4352*globalProfileConstant (R+6))*(M^2)⁻¹*(W^R)⁻¹
      rw [pow_add]
      field_simp

/-- The value at zero has arbitrary inverse-scale gain at any fixed negative
boundary distance. The constant depends only on that distance and the orders. -/
theorem profile_zero_boundary_decay {μ : ℝ} (hμ : 0≤μ) (k j R : ℕ) :
    profileNat μ 0 ≤ (((k:ℝ)+1)^R*globalProfileConstant (R+j)) *
      ((Real.sqrt (1+μ))^j)⁻¹ *
        ((1+((k:ℝ)+μ)/Real.sqrt (1+μ))^R)⁻¹ := by
  let M := Real.sqrt (1+μ)
  let W := 1+μ/M
  let V := 1+((k:ℝ)+μ)/M
  have hM : 0<M := Real.sqrt_pos.mpr (by positivity)
  have hM₁ : 1≤M := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ)≤1+μ by linarith)
    simpa [M] using h
  have hM₂ : M^2=1+μ := Real.sq_sqrt (by positivity)
  have hW : 0<W := by dsimp [W]; positivity
  have hV : 0<V := by dsimp [V]; positivity
  have he : M*W=M+μ := by dsimp [W]; field_simp
  have hMW : M≤W := by nlinarith
  have hVW : V≤((k:ℝ)+1)*W := by
    have hev : M*V=M+(k:ℝ)+μ := by dsimp [V]; field_simp; ring
    have hk := mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (show 0≤M-1+μ by linarith)
    nlinarith
  have hC := (globalProfileConstant_pos (R+j)).le
  have hp := profileNat_global_decay hμ 0 (R+j)
  simp only [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hμ] at hp
  change profileNat μ 0 ≤ (((k:ℝ)+1)^R*globalProfileConstant (R+j))*(M^j)⁻¹*(V^R)⁻¹
  rw [mul_assoc, ←mul_inv, ←div_eq_mul_inv]
  apply (le_div_iff₀ (mul_pos (pow_pos hM j) (pow_pos hV R))).mpr
  calc
    _ ≤ (globalProfileConstant (R+j)*(W^(R+j))⁻¹)*(W^j*((((k:ℝ)+1)*W)^R)) := by
      apply mul_le_mul hp _ (by positivity) (by positivity)
      exact mul_le_mul (pow_le_pow_left₀ hM.le hMW j) (pow_le_pow_left₀ hV.le hVW R)
        (by positivity) (by positivity)
    _ = _ := by rw [pow_add,mul_pow]; field_simp

/-- The -1 second-difference stencil is controlled by three times M times
the zero-index value. -/
theorem profile_second_boundary_height {μ : ℝ} (hμ : 0≤μ) :
    |profileNat μ 1-2*profileNat μ 0| ≤
      3*Real.sqrt (1+μ)*profileNat μ 0 := by
  have hM₁ : 1≤Real.sqrt (1+μ) := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ)≤1+μ by linarith)
    simpa using h
  have hs : Real.sqrt μ ≤ Real.sqrt (1+μ) := Real.sqrt_le_sqrt (by linarith)
  have hP := profileNat_nonneg μ 0
  have hr := profileNat_succ hμ 0
  norm_num only [Nat.cast_zero,zero_add,div_one] at hr
  rw [hr]
  calc
    _ ≤ |profileNat μ 0*Real.sqrt μ|+|2*profileNat μ 0| := abs_sub _ _
    _ = profileNat μ 0*Real.sqrt μ+2*profileNat μ 0 := by
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_right hs (profileNat_nonneg μ 0),
        mul_nonneg (show 0≤Real.sqrt (1+μ)-1 by linarith) (profileNat_nonneg μ 0)]

/-- Boundary decay at -1 for order two, retaining M⁻². -/
theorem profile_second_boundary_decay {μ : ℝ} (hμ : 0≤μ) (R : ℕ) :
    |profileNat μ 1-2*profileNat μ 0| ≤
      (3*(2:ℝ)^R*globalProfileConstant (R+3)) * ((Real.sqrt (1+μ))^2)⁻¹ *
        ((1+(1+μ)/Real.sqrt (1+μ))^R)⁻¹ := by
  have hM : 0<Real.sqrt (1+μ) := Real.sqrt_pos.mpr (by positivity)
  have h := profile_zero_boundary_decay hμ 1 3 R
  norm_num only [Nat.cast_one] at h
  calc
    _ ≤ 3*Real.sqrt (1+μ)*profileNat μ 0 := profile_second_boundary_height hμ
    _ ≤ 3*Real.sqrt (1+μ)*(((2:ℝ)^R*globalProfileConstant (R+3))*
      ((Real.sqrt (1+μ))^3)⁻¹*((1+(1+μ)/Real.sqrt (1+μ))^R)⁻¹) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

/-- Explicit global second-difference constant. -/
def globalSecondConstant (R : ℕ) : ℝ :=
  4352*globalProfileConstant (R+6) +
  3*(2:ℝ)^R*globalProfileConstant (R+3) +
  (3:ℝ)^R*globalProfileConstant (R+2)

theorem globalSecondConstant_pos (R : ℕ) : 0<globalSecondConstant R := by
  have h₁ := globalProfileConstant_pos (R+6)
  have h₂ := globalProfileConstant_pos (R+3)
  have h₃ := globalProfileConstant_pos (R+2)
  unfold globalSecondConstant
  positivity

/-- Exact global second-difference bound, including both negative boundary
stencils and the complete zero extension. -/
theorem profile_global_second_decay {μ : ℝ} (hμ : 0≤μ) (n : ℤ) (R : ℕ) :
    |(deltaOne^[2]) (profile μ) n| ≤ globalSecondConstant R *
      ((Real.sqrt (1+μ))^2)⁻¹ *
        ((1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^R)⁻¹ := by
  have hA : 0≤4352*globalProfileConstant (R+6) :=
    mul_nonneg (by norm_num) (globalProfileConstant_pos _).le
  have hB : 0≤3*(2:ℝ)^R*globalProfileConstant (R+3) :=
    mul_nonneg (by positivity) (globalProfileConstant_pos _).le
  have hC : 0≤(3:ℝ)^R*globalProfileConstant (R+2) :=
    mul_nonneg (by positivity) (globalProfileConstant_pos _).le
  by_cases hn : 0≤n
  · obtain ⟨k,rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hid : (deltaOne^[2]) (profile μ) (k:ℤ) =
        profileNat μ (k+2)-2*profileNat μ (k+1)+profileNat μ k := by
      simp only [Function.iterate_succ_apply',Function.iterate_zero_apply,deltaOne]
      rw [show (k:ℤ)+1+1=((k+2:ℕ):ℤ) by push_cast; ring,
        show (k:ℤ)+1=((k+1:ℕ):ℤ) by push_cast; ring]
      rw [profile_nat,profile_nat,profile_nat]
      ring
    rw [hid]
    apply (profileNat_global_second_decay hμ k R).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    unfold globalSecondConstant
    linarith
  by_cases h1 : n = -1
  · subst n
    have hid : (deltaOne^[2]) (profile μ) (-1) = profileNat μ 1-2*profileNat μ 0 := by
      simp [Function.iterate_succ_apply',deltaOne,profile]
      ring
    rw [hid]
    have hab : |((-1:ℤ):ℝ)-μ|=1+μ := by
      norm_num only [Int.cast_neg,Int.cast_one]
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [hab]
    apply (profile_second_boundary_decay hμ R).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    unfold globalSecondConstant
    linarith
  by_cases h2 : n = -2
  · subst n
    have hid : (deltaOne^[2]) (profile μ) (-2) = profileNat μ 0 := by
      simp [Function.iterate_succ_apply',deltaOne,profile]
    rw [hid,abs_of_nonneg (profileNat_nonneg μ 0)]
    have hab : |((-2:ℤ):ℝ)-μ|=2+μ := by
      norm_num only [Int.cast_neg,Int.cast_ofNat]
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [hab]
    have h := profile_zero_boundary_decay hμ 2 2 R
    norm_num only [Nat.cast_ofNat] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    unfold globalSecondConstant
    linarith
  have hz := profile_difference_vanishes_left μ 2 n (by omega)
  rw [hz,abs_zero]
  exact mul_nonneg (mul_nonneg (globalSecondConstant_pos R).le (by positivity)) (by positivity)

/-- The exact order-two specialization of the full source profile contract. -/
theorem poissonProfileEstimate_order_two (R : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ μ : ℝ, 0≤μ → ∀ n : ℤ,
      |(deltaOne^[2]) (profile μ) n| ≤ C * (Real.sqrt (1+μ)^2)⁻¹ *
        ((1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^R)⁻¹ := by
  refine ⟨globalSecondConstant R,globalSecondConstant_pos R,?_⟩
  intro μ hμ n
  exact profile_global_second_decay hμ n R

end BourgainBasis
