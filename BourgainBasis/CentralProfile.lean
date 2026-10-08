module
public import BourgainBasis.PoissonBounds

@[expose] public section

noncomputable section
namespace BourgainBasis

/-- Stirling height and the large-deviation exponential in the same bound;
neither factor is lost by taking the minimum of separate estimates. -/
theorem poisson_stirling_rate {μ : ℝ} (hμ : 0 < μ) (n : ℕ) (hn : 0 < n) :
    poisson μ n ≤ Real.exp
      (-((n : ℝ) * Real.log ((n : ℝ) / μ) - n + μ) - Real.log n / 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac := Stirling.le_log_factorial_stirling (by omega : n ≠ 0)
  have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  apply (Real.log_le_log_iff (by unfold poisson; positivity) (by positivity)).mp
  rw [Real.log_exp, Real.log_div (ne_of_gt hnR) (ne_of_gt hμ)]
  unfold poisson
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow]
  linarith

/-- The missing peak-height factor from Stirling, uniform in the mean.
This is stronger than the Chernoff bound near the peak. -/
theorem poisson_le_inv_sqrt {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) (hn : 0 < n) :
    poisson μ n ≤ (Real.sqrt (n : ℝ))⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rcases eq_or_lt_of_le hμ with hzero | hpos
  · rw [← hzero]
    simp [poisson, zero_pow (by omega : n ≠ 0)]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hpos hnR)
  rw [Real.log_div (ne_of_gt hpos) (ne_of_gt hnR)] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog hnR.le
  have hcancel : (n : ℝ) * (μ / n - 1) = μ - n := by field_simp
  rw [hcancel] at hscaled
  have hfac := Stirling.le_log_factorial_stirling (by omega : n ≠ 0)
  have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  apply (Real.log_le_log_iff (by unfold poisson; positivity) (by positivity)).mp
  rw [Real.log_inv, Real.log_sqrt hnR.le]
  unfold poisson
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow]
  linarith

/-- Uniform central height. The assumptions permit all μ≤2n, not just a narrow
central window. The n=0 singularity of Stirling is excluded explicitly. -/
theorem profile_central_height {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) (hn : 0 < n)
    (hcenter : μ ≤ 2 * (n : ℝ)) : profileNat μ n ≤ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hs : Real.sqrt (1 + μ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have ha := Real.sq_sqrt (by positivity : 0 ≤ 1 + μ)
    have hb := Real.sq_sqrt hnR.le
    have hc := Real.sqrt_nonneg (1 + μ)
    nlinarith
  have he : profileNat μ n ^ 2 = Real.sqrt (1 + μ) * poisson μ n := by
    unfold profileNat
    rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (poisson_nonneg hμ n)]
  have hb : profileNat μ n ^ 2 ≤ 2 := by
    rw [he]
    calc
      _ ≤ Real.sqrt (1 + μ) * (Real.sqrt (n : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left (poisson_le_inv_sqrt hμ n hn) (Real.sqrt_nonneg _)
      _ ≤ (2 * Real.sqrt (n : ℝ)) * (Real.sqrt (n : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hs (by positivity)
      _ = 2 := by field_simp
  nlinarith [profileNat_nonneg μ n]

/-- First-difference gain with an explicit distance from the mean. -/
theorem profile_central_first_difference {μ : ℝ} (hμ : 2 ≤ μ) (n : ℕ)
    (hcenter : μ ≤ 2 * (n : ℝ)) :
    |profileNat μ (n + 1) - profileNat μ n| ≤ 4 * (|(n : ℝ) - μ| + 1) / μ := by
  have hμ₀ : 0 < μ := by linarith
  have hn : 0 < n := by by_contra! h; simp only [Nat.le_zero.mp h, Nat.cast_zero, mul_zero] at hcenter; linarith
  have hn₁ : (0 : ℝ) < n + 1 := by positivity
  have he : |μ / ((n : ℝ) + 1) - 1| = |μ - ((n : ℝ) + 1)| / ((n : ℝ) + 1) := by
    have hh : μ / ((n : ℝ) + 1) - 1 = (μ - ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
      field_simp
    rw [hh, abs_div, abs_of_pos hn₁]
  have ht : |μ - ((n : ℝ) + 1)| ≤ |(n : ℝ) - μ| + 1 := by
    have hh := abs_sub_le μ (n : ℝ) ((n : ℝ) + 1)
    simpa [abs_sub_comm μ (n : ℝ)] using hh
  calc
    _ ≤ profileNat μ n * |μ / ((n : ℝ) + 1) - 1| := profile_first_difference hμ₀.le n
    _ ≤ 2 * |μ / ((n : ℝ) + 1) - 1| :=
      mul_le_mul_of_nonneg_right (profile_central_height hμ₀.le n hn hcenter) (abs_nonneg _)
    _ = 2 * (|μ - ((n : ℝ) + 1)| / ((n : ℝ) + 1)) := by rw [he]
    _ ≤ 2 * ((|(n : ℝ) - μ| + 1) / ((n : ℝ) + 1)) := by gcongr
    _ ≤ _ := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hn₁ hμ₀).mpr
      nlinarith [abs_nonneg ((n : ℝ) - μ)]

/-- The first central difference in the paper's natural scale M=√(1+μ).
The distance factor is explicit; this is not yet the arbitrary-order decay lemma. -/
theorem profile_central_first_difference_scaled {μ : ℝ} (hμ : 2 ≤ μ) (n : ℕ)
    (hcenter : μ ≤ 2 * (n : ℝ)) :
    |profileNat μ (n + 1) - profileNat μ n| ≤
      (8 / Real.sqrt (1 + μ)) * (1 + |(n : ℝ)-μ| / Real.sqrt (1 + μ)) := by
  let M := Real.sqrt (1 + μ)
  let D := |(n : ℝ)-μ|
  have hμ₀ : 0 < μ := by linarith
  have hM : 0 < M := Real.sqrt_pos.mpr (by linarith)
  have hM₁ : 1 ≤ M := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + μ by linarith)
    simpa [M] using h
  have hM₂ : M^2 = 1 + μ := Real.sq_sqrt (by linarith)
  have hD : 0 ≤ D := abs_nonneg _
  calc
    _ ≤ 4 * (D + 1) / μ := profile_central_first_difference hμ n hcenter
    _ ≤ 8 * (M + D) / (1 + μ) := by
      apply (div_le_div_iff₀ hμ₀ (by linarith)).mpr
      nlinarith [mul_nonneg (show 0 ≤ μ-1 by linarith) (show 0 ≤ D+1 by linarith),
        mul_nonneg hμ₀.le (show 0 ≤ M-1 by linarith)]
    _ = _ := by
      change 8 * (M + D) / (1 + μ) = (8 / M) * (1 + D / M)
      rw [← hM₂]
      field_simp

end BourgainBasis
