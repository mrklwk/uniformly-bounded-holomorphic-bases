module
public import BourgainBasis.Calibration

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- Global Chernoff bound, with arbitrary real tilt and every nonnegative mean.
No asymptotic or tail hypothesis is assumed. -/
theorem poisson_exponential_bound {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) (t : ℝ) :
    poisson μ n ≤ Real.exp (μ * (Real.exp t - 1) - (n : ℝ) * t) := by
  have hid : poisson μ n = Real.exp (-μ - (n : ℝ) * t) *
      ((μ * Real.exp t)^n / (n.factorial : ℝ)) := by
    unfold poisson
    rw [mul_pow, ← Real.exp_nat_mul]
    have he : Real.exp (-μ - (n : ℝ) * t) * Real.exp ((n : ℝ) * t) =
        Real.exp (-μ) := by rw [← Real.exp_add]; congr 1; ring
    calc
      _ = (Real.exp (-μ - (n : ℝ) * t) * Real.exp ((n : ℝ) * t)) *
          μ ^ n / (n.factorial : ℝ) := by rw [he]
      _ = _ := by ring
  rw [hid]
  calc
    _ ≤ Real.exp (-μ - (n : ℝ) * t) * Real.exp (μ * Real.exp t) :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp _ (by positivity) n)
        (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem poisson_le_one {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) : poisson μ n ≤ 1 := by
  simpa using poisson_exponential_bound hμ n 0

/-- Optimized large-deviation rate, valid on both sides of the mean. -/
theorem poisson_rate_bound {μ : ℝ} (hμ : 0 < μ) (n : ℕ) (hn : 0 < n) :
    poisson μ n ≤ Real.exp (-((n : ℝ) * Real.log ((n : ℝ) / μ) - n + μ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := poisson_exponential_bound hμ.le n (Real.log ((n : ℝ) / μ))
  rw [Real.exp_log (by positivity : 0 < (n : ℝ) / μ)] at h
  convert h using 1
  congr 1
  field_simp
  ring

/-- The left tail, including the n=0 boundary, with fixed positive-rate form.
The constant `(1-log 2)/2` is independent of both n and μ. -/
theorem poisson_left_tail {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) (hn : (n : ℝ) ≤ μ / 2) :
    poisson μ n ≤ Real.exp (-((1 - Real.log 2) / 2) * μ) := by
  have h := poisson_exponential_bound hμ n (-Real.log 2)
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

/-- A fixed-rate right tail, uniform in μ≥0, on n≥4μ. -/
theorem poisson_right_tail {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) (hn : 4 * μ ≤ (n : ℝ)) :
    poisson μ n ≤ Real.exp (-(1 / 4 : ℝ) * n) := by
  have h := poisson_exponential_bound hμ n (Real.log 2)
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hlog := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hlog ⊢
    linarith
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem left_tail_rate_pos : 0 < (1 - Real.log 2) / 2 := by
  have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)
  linarith

theorem profile_right_tail {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) (hn : 4 * μ ≤ (n : ℝ)) :
    profileNat μ n ≤ Real.sqrt (Real.sqrt (1 + μ)) * Real.exp (-(n : ℝ) / 8) := by
  unfold profileNat
  have h := Real.sqrt_le_sqrt (poisson_right_tail hμ n hn)
  rw [← Real.exp_half] at h
  have he : (-(1 / 4 : ℝ) * n) / 2 = -(n : ℝ) / 8 := by ring
  rw [he] at h
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- Only the j+1 values in the actual difference stencil are required. -/
theorem difference_local_bound (f : ℤ → ℝ) (j : ℕ) (n : ℤ) (K : ℝ)
    (hf : ∀ r : ℕ, r ≤ j → |f (n + r)| ≤ K) :
    |(deltaOne^[j]) f n| ≤ 2^j * K := by
  induction j generalizing n with
  | zero => simpa using hf 0 (by omega)
  | succ j ih =>
    rw [Function.iterate_succ_apply', deltaOne]
    have h₁ := ih (n + 1) (by
      intro r hr
      have h := hf (r + 1) (by omega)
      convert h using 1
      push_cast
      congr 2
      omega)
    have h₀ := ih n (fun r hr => hf r (by omega))
    calc
      _ ≤ |(deltaOne^[j]) f (n + 1)| + |(deltaOne^[j]) f n| := abs_sub _ _
      _ ≤ 2^j * K + 2^j * K := add_le_add h₁ h₀
      _ = _ := by rw [pow_succ]; ring

/-- All finite-difference orders in the right tail, including μ=0. The eventual
absorption of the polynomial scale factors is not presumed here. -/
theorem profile_right_tail_differences {μ : ℝ} (hμ : 0 ≤ μ) (j n : ℕ)
    (hn : 4 * μ ≤ (n : ℝ)) :
    |(deltaOne^[j]) (profile μ) (n : ℤ)| ≤
      2^j * (Real.sqrt (Real.sqrt (1 + μ)) * Real.exp (-(n : ℝ) / 8)) := by
  apply difference_local_bound
  intro r _
  rw [← Int.natCast_add, profile_nat, abs_of_nonneg (profileNat_nonneg μ (n+r))]
  have hnr : 4 * μ ≤ (n + r : ℕ) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) r]
  apply (profile_right_tail hμ (n+r) hnr).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) r]

theorem profile_nonneg (μ : ℝ) (n : ℤ) : 0 ≤ profile μ n := by
  unfold profile
  split_ifs
  · exact profileNat_nonneg μ _
  · rfl

/-- Left-tail height including the negative-index zero extension. -/
theorem profile_left_tail {μ : ℝ} (hμ : 0 ≤ μ) (n : ℤ) (hn : (n : ℝ) ≤ μ / 2) :
    profile μ n ≤ Real.sqrt (Real.sqrt (1 + μ)) *
      Real.exp (-(1 - Real.log 2) * μ / 4) := by
  by_cases hz : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    rw [profile_nat]
    unfold profileNat
    have h := Real.sqrt_le_sqrt (poisson_left_tail hμ k (by exact_mod_cast hn))
    rw [← Real.exp_half] at h
    have he : (-((1 - Real.log 2) / 2) * μ) / 2 = -(1 - Real.log 2) * μ / 4 := by ring
    rw [he] at h
    exact mul_le_mul_of_nonneg_left h (by positivity)
  · simpa [profile, hz] using
      (show 0 ≤ Real.sqrt (Real.sqrt (1 + μ)) *
        Real.exp (-(1 - Real.log 2) * μ / 4) by positivity)

/-- The whole stencil lies left of μ/2. This includes the negative boundary
stencils, and the constant is uniform in μ and n. -/
theorem profile_left_tail_differences {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) (n : ℤ)
    (hn : (n : ℝ) + j ≤ μ / 2) :
    |(deltaOne^[j]) (profile μ) n| ≤
      2^j * (Real.sqrt (Real.sqrt (1 + μ)) * Real.exp (-(1 - Real.log 2) * μ / 4)) := by
  apply difference_local_bound
  intro r hr
  rw [abs_of_nonneg (profile_nonneg μ _)]
  apply profile_left_tail hμ
  push_cast
  have : (r : ℝ) ≤ j := by exact_mod_cast hr
  linarith

theorem profile_zero_mean (n : ℤ) : profile 0 n = if n = 0 then 1 else 0 := by
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    cases k with
    | zero => simp [profile, profileNat, poisson]
    | succ k =>
      simp [profile, profileNat, poisson]
      omega
  · have hne : n ≠ 0 := by omega
    simp [profile, hn, hne]

/-- An iterated forward difference cannot escape the translated support to the left. -/
theorem difference_vanishes_left (f : ℤ → ℝ) (hf : ∀ n < 0, f n = 0)
    (j : ℕ) (n : ℤ) (hn : n < -(j : ℤ)) : (deltaOne^[j]) f n = 0 := by
  induction j generalizing n with
  | zero => simpa using hf n (by simpa using hn)
  | succ j ih =>
    rw [Function.iterate_succ_apply', deltaOne]
    rw [ih (n + 1) (by omega), ih n (by omega), sub_self]

theorem difference_vanishes_right (f : ℤ → ℝ) (hf : ∀ n > 0, f n = 0)
    (j : ℕ) (n : ℤ) (hn : 0 < n) : (deltaOne^[j]) f n = 0 := by
  induction j generalizing n with
  | zero => simpa using hf n hn
  | succ j ih =>
    rw [Function.iterate_succ_apply', deltaOne]
    rw [ih (n + 1) (by omega), ih n hn, sub_self]

theorem profile_difference_vanishes_left (μ : ℝ) (j : ℕ) (n : ℤ)
    (hn : n < -(j : ℤ)) : (deltaOne^[j]) (profile μ) n = 0 := by
  apply difference_vanishes_left _ _ j n hn
  intro k hk
  simp [profile, show ¬0 ≤ k by omega]

theorem difference_uniform_bound (f : ℤ → ℝ) (K : ℝ) (hf : ∀ n, |f n| ≤ K)
    (j : ℕ) (n : ℤ) : |(deltaOne^[j]) f n| ≤ 2 ^ j * K := by
  induction j generalizing n with
  | zero => simpa using hf n
  | succ j ih =>
    rw [Function.iterate_succ_apply', deltaOne]
    calc
      _ ≤ |(deltaOne^[j]) f (n + 1)| + |(deltaOne^[j]) f n| := abs_sub _ _
      _ ≤ 2 ^ j * K + 2 ^ j * K := add_le_add (ih _) (ih _)
      _ = _ := by rw [pow_succ]; ring

/-- The full source profile estimate at μ=0, all orders, decay exponents and integer
indices, with explicit constants depending only on j and R. -/
theorem zero_mean_profile_estimate (j R : ℕ) (n : ℤ) :
    |(deltaOne^[j]) (profile 0) n| ≤
      ((2 : ℝ)^j * (j + 1 : ℝ)^R) * ((1 + |(n : ℝ)|)^R)⁻¹ := by
  have hb := difference_uniform_bound (profile 0) 1 (by
    intro k; rw [profile_zero_mean]; split_ifs <;> norm_num) j n
  simp only [mul_one] at hb
  by_cases hl : n < -(j : ℤ)
  · rw [difference_vanishes_left (profile 0) (by
      intro k hk; rw [profile_zero_mean]; simp [show k ≠ 0 by omega]) j n hl]
    simp only [abs_zero]
    positivity
  by_cases hr : 0 < n
  · rw [difference_vanishes_right (profile 0) (by
      intro k hk; rw [profile_zero_mean]; simp [show k ≠ 0 by omega]) j n hr]
    simp only [abs_zero]
    positivity
  have hab : |(n : ℝ)| ≤ (j : ℝ) := by
    rw [abs_of_nonpos (by exact_mod_cast (le_of_not_gt hr))]
    exact_mod_cast (by omega : -n ≤ (j : ℤ))
  have hp : (1 + |(n : ℝ)|)^R ≤ (j + 1 : ℝ)^R :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hd : 0 < (1 + |(n : ℝ)|)^R := by positivity
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hd).mpr
  exact (mul_le_mul_of_nonneg_right hb (le_of_lt hd)).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))

end BourgainBasis
