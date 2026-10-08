module
public import BourgainBasis.CentralProfile

@[expose] public section

noncomputable section
namespace BourgainBasis

/-- The curvature of adjacent square-root recurrence ratios, without losing
one power of the central scale. Valid also at zero mean and index zero. -/
theorem sqrt_ratio_curvature {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) :
    Real.sqrt (μ / (n + 1)) *
      |Real.sqrt (μ / (n + 2)) - Real.sqrt (μ / (n + 1))| ≤
        μ / ((n + 1) * (n + 2)) := by
  have hx : (0 : ℝ) < n + 1 := by positivity
  have hy : (0 : ℝ) < n + 2 := by positivity
  have hdiv : μ / (n + 2) ≤ μ / (n + 1) := by
    apply div_le_div_of_nonneg_left hμ hx
    linarith
  have hle := Real.sqrt_le_sqrt hdiv
  have ha := Real.sqrt_nonneg (μ / (n + 1))
  have hb := Real.sqrt_nonneg (μ / (n + 2))
  have hsa := Real.sq_sqrt (show 0 ≤ μ / (n + 1) by positivity)
  have hsb := Real.sq_sqrt (show 0 ≤ μ / (n + 2) by positivity)
  have hid : μ / (n + 1) - μ / (n + 2) = μ / ((n + 1) * (n + 2)) := by
    field_simp
    ring
  rw [abs_of_nonpos (sub_nonpos.mpr hle), ← hid]
  nlinarith [mul_nonneg hb (sub_nonneg.mpr hle)]

/-- A genuine second-difference estimate retaining the actual profile height.
The curvature term is O(μ/n²), unlike the coarse triangle inequality between
first differences. No central-window assumption is needed. -/
theorem profile_second_difference {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) :
    |profileNat μ (n + 2) - 2 * profileNat μ (n + 1) + profileNat μ n| ≤
      profileNat μ n *
        ((μ / (n + 1) - 1)^2 + μ / ((n + 1) * (n + 2))) := by
  let a := Real.sqrt (μ / ((n : ℝ) + 1))
  let b := Real.sqrt (μ / ((n : ℝ) + 2))
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hc := sqrt_ratio_curvature hμ n
  have hs := sqrt_sub_one_bound (show 0 ≤ μ / ((n : ℝ) + 1) by positivity)
  have hsq : (a - 1)^2 ≤ (μ / ((n : ℝ) + 1) - 1)^2 := by
    nlinarith [sq_abs (a - 1), sq_abs (μ / ((n : ℝ) + 1) - 1),
      mul_nonneg (sub_nonneg.mpr hs) (add_nonneg (abs_nonneg (μ / ((n : ℝ) + 1) - 1)) (abs_nonneg (a - 1)))]
  have hrec : profileNat μ (n + 2) = profileNat μ n * a * b := by
    rw [show n + 2 = (n + 1) + 1 by omega, profileNat_succ hμ, profileNat_succ hμ]
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp [a, b]
    congr 2
    ring
  rw [hrec, profileNat_succ hμ]
  change |profileNat μ n * a * b - 2 * (profileNat μ n * a) + profileNat μ n| ≤ _
  have hid : profileNat μ n * a * b - 2 * (profileNat μ n * a) + profileNat μ n =
      profileNat μ n * ((a - 1)^2 + a * (b - a)) := by ring
  rw [hid, abs_mul, abs_of_nonneg (profileNat_nonneg μ n)]
  apply mul_le_mul_of_nonneg_left _ (profileNat_nonneg μ n)
  calc
    _ ≤ |(a - 1)^2| + |a * (b - a)| := abs_add_le _ _
    _ = (a - 1)^2 + a * |b - a| := by rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_of_nonneg ha]
    _ ≤ _ := add_le_add hsq hc

/-- Central second-difference gain, uniform in μ and n. The distance
polynomial is kept explicit so that a later rate estimate can absorb it. -/
theorem profile_central_second_difference {μ : ℝ} (hμ : 2 ≤ μ) (n : ℕ)
    (hcenter : μ ≤ 2 * (n : ℝ)) :
    |profileNat μ (n + 2) - 2 * profileNat μ (n + 1) + profileNat μ n| ≤
      8 * ((|(n : ℝ) - μ| + 1)^2 + μ) / μ^2 := by
  have hμ₀ : 0 < μ := by linarith
  have hn : 0 < n := by
    by_contra! h
    simp only [Nat.le_zero.mp h, Nat.cast_zero, mul_zero] at hcenter
    linarith
  have hx : (0 : ℝ) < n + 1 := by positivity
  have hy : (0 : ℝ) < n + 2 := by positivity
  let D := |(n : ℝ) - μ| + 1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have ht : |μ - ((n : ℝ) + 1)| ≤ D := by
    have hh := abs_sub_le μ (n : ℝ) ((n : ℝ) + 1)
    simpa [D, abs_sub_comm μ (n : ℝ)] using hh
  have hab : |μ / ((n : ℝ) + 1) - 1| ≤ 2 * D / μ := by
    have hid : μ / ((n : ℝ) + 1) - 1 = (μ - ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by field_simp
    rw [hid, abs_div, abs_of_pos hx]
    apply (div_le_div_iff₀ hx hμ₀).mpr
    calc
      _ ≤ D * μ := mul_le_mul_of_nonneg_right ht hμ₀.le
      _ ≤ _ := by nlinarith
  have hsq : (μ / ((n : ℝ) + 1) - 1)^2 ≤ (2 * D / μ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (μ / ((n : ℝ) + 1) - 1)) hab 2
  have hcurv : μ / (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤ 4 / μ := by
    apply (div_le_div_iff₀ (mul_pos hx hy) hμ₀).mpr
    have hh : μ^2 ≤ (2 * (n : ℝ))^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ profileNat μ n * ((μ / (n + 1) - 1)^2 + μ / ((n + 1) * (n + 2))) :=
      profile_second_difference hμ₀.le n
    _ ≤ 2 * ((μ / (n + 1) - 1)^2 + μ / ((n + 1) * (n + 2))) :=
      mul_le_mul_of_nonneg_right (profile_central_height hμ₀.le n hn hcenter) (by positivity)
    _ ≤ 2 * ((2 * D / μ)^2 + 4 / μ) := by gcongr
    _ = _ := by dsimp [D]; field_simp; ring

/-- Stirling's height and rate survive taking the normalized square root. -/
theorem profile_stirling_rate {μ : ℝ} (hμ : 0 < μ) (n : ℕ) (hn : 0 < n) :
    profileNat μ n ≤ Real.sqrt (Real.sqrt (1 + μ)) *
      Real.exp (-((n : ℝ) * Real.log ((n : ℝ) / μ) - n + μ) / 2 -
        Real.log n / 4) := by
  unfold profileNat
  have h := Real.sqrt_le_sqrt (poisson_stirling_rate hμ n hn)
  rw [← Real.exp_half] at h
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  convert h using 1
  congr 1
  ring

/-- Second finite differences retain the Stirling peak height and exponential
rate together. Thus the recurrence argument does not discard tail decay. -/
theorem profile_second_difference_rate {μ : ℝ} (hμ : 0 < μ) (n : ℕ) (hn : 0 < n) :
    |profileNat μ (n + 2) - 2 * profileNat μ (n + 1) + profileNat μ n| ≤
      (Real.sqrt (Real.sqrt (1 + μ)) *
        Real.exp (-((n : ℝ) * Real.log ((n : ℝ) / μ) - n + μ) / 2 -
          Real.log n / 4)) *
      ((μ / (n + 1) - 1)^2 + μ / ((n + 1) * (n + 2))) := by
  exact (profile_second_difference hμ.le n).trans
    (mul_le_mul_of_nonneg_right (profile_stirling_rate hμ n hn) (by positivity))

/-- The order-two central estimate for the actual zero-extended integer profile;
nonnegative indices ensure its whole stencil lies in the natural domain. -/
theorem profile_central_second_difference_int {μ : ℝ} (hμ : 2 ≤ μ) (n : ℕ)
    (hcenter : μ ≤ 2 * (n : ℝ)) :
    |(deltaOne^[2]) (profile μ) (n : ℤ)| ≤
      8 * ((|(n : ℝ) - μ| + 1)^2 + μ) / μ^2 := by
  have hid : (deltaOne^[2]) (profile μ) (n : ℤ) =
      profileNat μ (n + 2) - 2 * profileNat μ (n + 1) + profileNat μ n := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, deltaOne]
    rw [show (n : ℤ) + 1 + 1 = ((n + 2 : ℕ) : ℤ) by push_cast; ring,
      show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring]
    rw [profile_nat, profile_nat, profile_nat]
    ring
  rw [hid]
  exact profile_central_second_difference hμ n hcenter

/-- The central order-two bound in the natural scale M=√(1+μ), with
an explicit polynomial distance factor and a uniform numerical constant. -/
theorem profile_central_second_difference_scaled {μ : ℝ} (hμ : 2 ≤ μ) (n : ℕ)
    (hcenter : μ ≤ 2 * (n : ℝ)) :
    |(deltaOne^[2]) (profile μ) (n : ℤ)| ≤
      (48 / (Real.sqrt (1 + μ))^2) *
        (1 + |(n : ℝ) - μ| / Real.sqrt (1 + μ))^2 := by
  let M := Real.sqrt (1 + μ)
  let D := |(n : ℝ) - μ|
  have hμ₀ : 0 < μ := by linarith
  have hM : 0 < M := Real.sqrt_pos.mpr (by linarith)
  have hM₁ : 1 ≤ M := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + μ by linarith)
    simpa [M] using h
  have hM₂ : M^2 = 1 + μ := Real.sq_sqrt (by linarith)
  have hD : 0 ≤ D := abs_nonneg _
  have h₁ : (D + 1) / μ ≤ 2 * (D + M) / M^2 := by
    apply (div_le_div_iff₀ hμ₀ (sq_pos_of_pos hM)).mpr
    rw [hM₂]
    nlinarith [mul_nonneg (show 0 ≤ μ-1 by linarith) (show 0 ≤ D+1 by linarith),
      mul_nonneg hμ₀.le (show 0 ≤ M-1 by linarith)]
  have h₂ : 1 / μ ≤ 2 / M^2 := by
    apply (div_le_div_iff₀ hμ₀ (sq_pos_of_pos hM)).mpr
    nlinarith
  have h₃ : 1 / M^2 ≤ ((D + M) / M^2)^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hM)).mpr
    have hh : M^2 ≤ (D + M)^2 := by nlinarith
    field_simp
    exact hh
  have hs := pow_le_pow_left₀ (show 0 ≤ (D+1)/μ by positivity) h₁ 2
  calc
    _ ≤ 8 * ((D + 1)^2 + μ) / μ^2 := profile_central_second_difference_int hμ n hcenter
    _ = 8 * ((D+1)/μ)^2 + 8 * (1/μ) := by field_simp
    _ ≤ 8 * (2 * (D+M)/M^2)^2 + 8 * (2/M^2) := by gcongr
    _ = 32 * ((D+M)/M^2)^2 + 16 * (1/M^2) := by ring
    _ ≤ 48 * ((D+M)/M^2)^2 := by linarith
    _ = _ := by change _ = (48/M^2) * (1+D/M)^2; field_simp; ring

end BourgainBasis
