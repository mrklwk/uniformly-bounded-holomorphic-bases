module
public import BourgainBasis.PoissonCentralComplete

@[expose] public section

noncomputable section
namespace BourgainBasis

/-- Polynomial absorption in a uniform exponential tail. -/
theorem polynomial_mul_exp_bound {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) (k : ℕ) :
    (1+x)^k * Real.exp (-c*x) ≤
      (k.factorial:ℝ) * Real.exp c / c^k := by
  have h := Real.pow_div_factorial_le_exp (c*(1+x)) (by positivity) k
  have hf : (0:ℝ)<k.factorial := by positivity
  have hp : (c*(1+x))^k ≤ Real.exp (c*(1+x)) * (k.factorial:ℝ) :=
    (div_le_iff₀ hf).mp h
  apply (le_div_iff₀ (by positivity : 0<c^k)).mpr
  calc
    _ = (c*(1+x))^k * Real.exp (-c*x) := by rw [mul_pow]; ring
    _ ≤ (Real.exp (c*(1+x)) * (k.factorial:ℝ)) * Real.exp (-c*x) := by gcongr
    _ = _ := by
      have he : Real.exp (c*(1+x)) * Real.exp (-c*x) = Real.exp c := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (k.factorial:ℝ) * (Real.exp (c*(1+x)) * Real.exp (-c*x)) := by ring
        _ = _ := by rw [he]

/-- The normalization prefactor costs at most one polynomial power. -/
theorem profile_prefactor_le {μ : ℝ} (hμ : 0 ≤ μ) :
    Real.sqrt (Real.sqrt (1+μ)) ≤ 1+μ := by
  have h₁ : 1 ≤ Real.sqrt (1+μ) := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ)≤1+μ by linarith)
    simpa using h
  have h₂ := Real.sq_sqrt (show 0≤1+μ by positivity)
  have h₃ := Real.sq_sqrt (Real.sqrt_nonneg (1+μ))
  have h₄ := Real.sqrt_nonneg (Real.sqrt (1+μ))
  nlinarith [sq_nonneg (Real.sqrt (Real.sqrt (1+μ))-1)]

/-- A tail bound in n+μ yields the normalized polynomial envelope, with
constant independent of both parameters. -/
theorem profile_tail_to_decay {μ c : ℝ} (hμ : 0 ≤ μ) (hc : 0 < c) (n R : ℕ)
    (htail : profileNat μ n ≤ (1+μ)*Real.exp (-c*((n:ℝ)+μ))) :
    profileNat μ n ≤ (((R+1).factorial:ℝ)*Real.exp c/c^(R+1)) *
      ((1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^R)⁻¹ := by
  let x := (n:ℝ)+μ
  let W := 1+|(n:ℝ)-μ|/Real.sqrt (1+μ)
  have hx : 0≤x := by dsimp [x]; positivity
  have hM : 1≤Real.sqrt (1+μ) := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ)≤1+μ by linarith)
    simpa using h
  have hw : W ≤ 1+x := by
    have hab : |(n:ℝ)-μ| ≤ x := by
      dsimp [x]
      exact abs_sub_le_iff.mpr ⟨by linarith [Nat.cast_nonneg (α:=ℝ) n], by linarith [Nat.cast_nonneg (α:=ℝ) n]⟩
    have hd : |(n:ℝ)-μ|/Real.sqrt (1+μ) ≤ |(n:ℝ)-μ| :=
      div_le_self (abs_nonneg _) hM
    dsimp [W]
    linarith
  have hW : 0<W := by dsimp [W]; positivity
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hW R)).mpr
  calc
    _ ≤ ((1+μ)*Real.exp (-c*x)) * W^R := by gcongr
    _ ≤ ((1+x)*Real.exp (-c*x)) * (1+x)^R := by
      gcongr
      dsimp [x]
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    _ = (1+x)^(R+1)*Real.exp (-c*x) := by rw [pow_succ]; ring
    _ ≤ _ := polynomial_mul_exp_bound hc hx (R+1)

/-- The full right-tail polynomial envelope, all nonnegative means. -/
theorem profile_right_decay {μ : ℝ} (hμ : 0 ≤ μ) (n R : ℕ)
    (hright : 4*μ ≤ (n:ℝ)) :
    profileNat μ n ≤ (((R+1).factorial:ℝ)*Real.exp (1/16)/(1/16:ℝ)^(R+1)) *
      ((1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^R)⁻¹ := by
  apply profile_tail_to_decay hμ (by norm_num : (0:ℝ)<1/16)
  calc
    _ ≤ Real.sqrt (Real.sqrt (1+μ))*Real.exp (-(n:ℝ)/8) := profile_right_tail hμ n hright
    _ ≤ (1+μ)*Real.exp (-(1/16:ℝ)*((n:ℝ)+μ)) := by
      apply mul_le_mul (profile_prefactor_le hμ) _ (by positivity) (by positivity)
      apply Real.exp_le_exp.mpr
      linarith

/-- The full left-tail polynomial envelope, including n=0. -/
theorem profile_left_decay {μ : ℝ} (hμ : 0 ≤ μ) (n R : ℕ)
    (hleft : (n:ℝ) ≤ μ/2) :
    profileNat μ n ≤
      (((R+1).factorial:ℝ)*Real.exp ((1-Real.log 2)/8)/((1-Real.log 2)/8)^(R+1)) *
      ((1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^R)⁻¹ := by
  have hc : 0<(1-Real.log 2)/8 := by linarith [left_tail_rate_pos]
  apply profile_tail_to_decay hμ hc
  have h := profile_left_tail hμ (n:ℤ) (by exact_mod_cast hleft)
  rw [profile_nat] at h
  apply h.trans
  apply mul_le_mul (profile_prefactor_le hμ) _ (by positivity) (by positivity)
  apply Real.exp_le_exp.mpr
  have hp := mul_nonneg (show 0≤1-Real.log 2 by linarith [left_tail_rate_pos])
    (show 0≤μ-(n:ℝ) by linarith)
  nlinarith

/-- An explicit global order-zero constant; depends only on the decay order. -/
def globalProfileConstant (R : ℕ) : ℝ :=
  (2*(40:ℝ)^R*(R.factorial:ℝ)*Real.exp (1/20)) +
  (((R+1).factorial:ℝ)*Real.exp (1/16)/(1/16:ℝ)^(R+1)) +
  (((R+1).factorial:ℝ)*Real.exp ((1-Real.log 2)/8)/((1-Real.log 2)/8)^(R+1))

theorem globalProfileConstant_pos (R : ℕ) : 0 < globalProfileConstant R := by
  have hc : 0 < (1-Real.log 2)/8 := by linarith [left_tail_rate_pos]
  unfold globalProfileConstant
  positivity

/-- Global order-zero polynomial decay at all natural indices, including
zero mean, zero index, small means, central band and both tails. -/
theorem profileNat_global_decay {μ : ℝ} (hμ : 0 ≤ μ) (n R : ℕ) :
    profileNat μ n ≤ globalProfileConstant R *
      ((1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^R)⁻¹ := by
  have hc : 0 < (1-Real.log 2)/8 := by linarith [left_tail_rate_pos]
  have ha : 0 ≤ 2*(40:ℝ)^R*(R.factorial:ℝ)*Real.exp (1/20) := by positivity
  have hb : 0 ≤ ((R+1).factorial:ℝ)*Real.exp (1/16)/(1/16:ℝ)^(R+1) := by positivity
  have hd : 0 ≤ ((R+1).factorial:ℝ)*Real.exp ((1-Real.log 2)/8)/((1-Real.log 2)/8)^(R+1) := by positivity
  by_cases hl : (n:ℝ) ≤ μ/2
  · apply (profile_left_decay hμ n R hl).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    unfold globalProfileConstant
    linarith
  by_cases hr : 4*μ ≤ (n:ℝ)
  · apply (profile_right_decay hμ n R hr).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    unfold globalProfileConstant
    linarith
  have hμ₀ : 0 < μ := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hn : 0 < n := by
    have : (0:ℝ) < n := by linarith
    exact_mod_cast this
  apply (profile_central_decay hμ₀ n hn (by linarith) (by linarith) R).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  unfold globalProfileConstant
  linarith

/-- The complete global order-zero source bound for the actual zero-extended
integer profile, with no missing parameter or boundary regime. -/
theorem profile_global_decay {μ : ℝ} (hμ : 0 ≤ μ) (n : ℤ) (R : ℕ) :
    |profile μ n| ≤ globalProfileConstant R *
      ((1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^R)⁻¹ := by
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [profile_nat, abs_of_nonneg (profileNat_nonneg μ k)]
    simpa using profileNat_global_decay hμ k R
  · simp only [profile, ite_eq_right hn, abs_zero]
    exact mul_nonneg (globalProfileConstant_pos R).le (by positivity)

/-- The j=0 specialization of the source's global profile contract is proved,
including its uniform existential constant and all integer indices. -/
theorem poissonProfileEstimate_order_zero (R : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ μ : ℝ, 0≤μ → ∀ n : ℤ,
      |(deltaOne^[0]) (profile μ) n| ≤ C * (Real.sqrt (1+μ)^0)⁻¹ *
        ((1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^R)⁻¹ := by
  refine ⟨globalProfileConstant R, globalProfileConstant_pos R, ?_⟩
  intro μ hμ n
  simpa using profile_global_decay hμ n R

end BourgainBasis
