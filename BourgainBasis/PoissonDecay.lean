module
public import BourgainBasis.PoissonHigher

@[expose] public section

noncomputable section
namespace BourgainBasis

/-- A global Hellinger lower bound for the Poisson rate, without asymptotics. -/
theorem poisson_rate_sqrt_lower {x μ : ℝ} (hx : 0 < x) (hμ : 0 < μ) :
    (Real.sqrt x - Real.sqrt μ)^2 ≤ x * Real.log (x / μ) - x + μ := by
  have hsx := Real.sq_sqrt hx.le
  have hsμ := Real.sq_sqrt hμ.le
  have hpx := Real.sqrt_pos.mpr hx
  have hpμ := Real.sqrt_pos.mpr hμ
  have hl := Real.log_le_sub_one_of_pos (div_pos hpμ hpx)
  rw [Real.log_div (ne_of_gt hpμ) (ne_of_gt hpx), Real.log_sqrt hμ.le,
    Real.log_sqrt hx.le] at hl
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * x by positivity)
  have he : 2 * x * (Real.sqrt μ / Real.sqrt x - 1) =
      2 * Real.sqrt x * Real.sqrt μ - 2 * x := by
    field_simp
    nlinarith
  rw [he] at hm
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hμ)]
  nlinarith

/-- Quadratic lower bound for the rate, globally in both positive parameters. -/
theorem poisson_rate_quadratic_lower {x μ : ℝ} (hx : 0 < x) (hμ : 0 < μ) :
    (x - μ)^2 / (2 * (x + μ)) ≤ x * Real.log (x / μ) - x + μ := by
  have hsx := Real.sq_sqrt hx.le
  have hsμ := Real.sq_sqrt hμ.le
  have hid : 2 * (x + μ) * (Real.sqrt x - Real.sqrt μ)^2 - (x - μ)^2 =
      (Real.sqrt x - Real.sqrt μ)^4 := by
    have hid (a b : ℝ) : 2*(a^2+b^2)*(a-b)^2-(a^2-b^2)^2=(a-b)^4 := by ring
    simpa only [hsx, hsμ] using hid (Real.sqrt x) (Real.sqrt μ)
  have hgap : (x - μ)^2 ≤ 2 * (x + μ) * (Real.sqrt x - Real.sqrt μ)^2 := by
    nlinarith [show 0 ≤ (Real.sqrt x - Real.sqrt μ)^4 by positivity]
  apply (div_le_iff₀ (show 0 < 2 * (x+μ) by positivity)).mpr
  exact hgap.trans (by
    nlinarith [mul_le_mul_of_nonneg_left (poisson_rate_sqrt_lower hx hμ)
      (show 0 ≤ 2 * (x+μ) by positivity)])

/-- Fixed constants on the entire central-to-right-transition region x≤4μ. -/
theorem poisson_rate_central_lower {x μ : ℝ} (hx : 0 < x) (hμ : 0 < μ)
    (hcenter : x ≤ 4 * μ) :
    (x - μ)^2 / (10 * μ) ≤ x * Real.log (x / μ) - x + μ := by
  apply le_trans _ (poisson_rate_quadratic_lower hx hμ)
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  linarith

/-- Uniform central height with the complete rate factor retained. -/
theorem profile_central_rate {μ : ℝ} (hμ : 0 < μ) (n : ℕ) (hn : 0 < n)
    (hcenter : μ ≤ 2 * (n : ℝ)) :
    profileNat μ n ≤ 2 * Real.exp
      (-((n : ℝ) * Real.log ((n : ℝ) / μ) - n + μ) / 2) := by
  let I := (n : ℝ) * Real.log ((n : ℝ) / μ) - n + μ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt (1 + μ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have ha := Real.sq_sqrt (show 0 ≤ 1 + μ by positivity)
    have hb := Real.sq_sqrt hnR.le
    nlinarith [Real.sqrt_nonneg (1+μ), Real.sqrt_nonneg (n:ℝ)]
  have hp := poisson_stirling_rate hμ n hn
  have he : Real.exp (-I - Real.log n / 2) = Real.exp (-I) / Real.sqrt n := by
    rw [Real.exp_sub, ← Real.log_sqrt hnR.le, Real.exp_log (Real.sqrt_pos.mpr hnR)]
  change poisson μ n ≤ Real.exp (-I - Real.log n / 2) at hp
  rw [he] at hp
  have hb : profileNat μ n ^ 2 ≤ 2 * Real.exp (-I) := by
    unfold profileNat
    rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (poisson_nonneg hμ.le n)]
    calc
      _ ≤ Real.sqrt (1+μ) * (Real.exp (-I) / Real.sqrt n) :=
        mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)
      _ ≤ (2 * Real.sqrt n) * (Real.exp (-I) / Real.sqrt n) := by gcongr
      _ = _ := by field_simp
  have hexp : Real.exp (-I / 2)^2 = Real.exp (-I) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  change profileNat μ n ≤ 2 * Real.exp (-I/2)
  nlinarith [Real.exp_pos (-I/2), Real.exp_pos (-I)]

/-- Genuine Gaussian decay, uniform in the whole central band μ/2≤n≤4μ. -/
theorem profile_central_gaussian {μ : ℝ} (hμ : 0 < μ) (n : ℕ) (hn : 0 < n)
    (hleft : μ ≤ 2 * (n : ℝ)) (hright : (n : ℝ) ≤ 4 * μ) :
    profileNat μ n ≤ 2 * Real.exp (-((n : ℝ) - μ)^2 / (20 * μ)) := by
  apply (profile_central_rate hμ n hn hleft).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have h := poisson_rate_central_lower (show (0:ℝ)<n by exact_mod_cast hn) hμ hright
  have he : -((n : ℝ)-μ)^2/(20*μ) = -(((n : ℝ)-μ)^2/(10*μ))/2 := by ring
  rw [he]
  linarith

/-- The Gaussian bound uses exactly the source scale √(1+μ). -/
theorem profile_central_gaussian_scaled {μ : ℝ} (hμ : 0 < μ) (n : ℕ) (hn : 0 < n)
    (hleft : μ ≤ 2 * (n : ℝ)) (hright : (n : ℝ) ≤ 4 * μ) :
    profileNat μ n ≤ 2 * Real.exp (-((n : ℝ)-μ)^2 / (20 * (1+μ))) := by
  apply (profile_central_gaussian hμ n hn hleft hright).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have h : ((n : ℝ)-μ)^2 / (20*(1+μ)) ≤ ((n : ℝ)-μ)^2/(20*μ) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  simpa only [neg_div] using neg_le_neg h

/-- Explicit arbitrary-power absorption, obtained from the exponential series.
The constant is uniform in the nonnegative variable. -/
theorem gaussian_polynomial_absorption (x : ℝ) (R : ℕ) :
    Real.exp (-x^2 / 20) ≤
      ((20 : ℝ)^R * (R.factorial : ℝ) * Real.exp (1/20)) / (1+x^2)^R := by
  let t := (1+x^2)/20
  have ht : 0 < t := by dsimp [t]; positivity
  have h := Real.pow_div_factorial_le_exp t ht.le R
  have hfac : (0 : ℝ) < R.factorial := by positivity
  have hh : t^R ≤ (R.factorial : ℝ) * Real.exp t := by
    have := (div_le_iff₀ hfac).mp h
    nlinarith
  have hp : (1+x^2)^R = (20 : ℝ)^R * t^R := by
    rw [← mul_pow]
    congr 1
    dsimp [t]
    ring
  apply (le_div_iff₀ (by positivity : 0 < (1+x^2)^R)).mpr
  rw [hp]
  calc
    _ ≤ Real.exp (-x^2/20) * ((20:ℝ)^R * ((R.factorial:ℝ) * Real.exp t)) := by gcongr
    _ = _ := by
      have he : Real.exp (-x^2/20) * Real.exp t = Real.exp (1/20) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [t]
        ring
      calc
        _ = (20:ℝ)^R * (R.factorial:ℝ) * (Real.exp (-x^2/20) * Real.exp t) := by ring
        _ = _ := by rw [he]

/-- A genuinely decaying central profile estimate of every polynomial order.
The denominator (1+(distance/M)²)^R gives decay of order 2R. -/
theorem profile_central_polynomial {μ : ℝ} (hμ : 0 < μ) (n : ℕ) (hn : 0 < n)
    (hleft : μ ≤ 2 * (n : ℝ)) (hright : (n : ℝ) ≤ 4 * μ) (R : ℕ) :
    profileNat μ n ≤
      (2 * (20 : ℝ)^R * (R.factorial : ℝ) * Real.exp (1/20)) /
        (1 + (((n : ℝ)-μ) / Real.sqrt (1+μ))^2)^R := by
  have hs : Real.sqrt (1+μ)^2 = 1+μ := Real.sq_sqrt (by positivity)
  have he : -((n : ℝ)-μ)^2/(20*(1+μ)) =
      -(((n : ℝ)-μ)/Real.sqrt (1+μ))^2/20 := by rw [div_pow, hs]; field_simp
  have h := profile_central_gaussian_scaled hμ n hn hleft hright
  rw [he] at h
  apply h.trans
  have ha := mul_le_mul_of_nonneg_left
    (gaussian_polynomial_absorption (((n : ℝ)-μ)/Real.sqrt (1+μ)) R) (by norm_num : (0:ℝ)≤2)
  convert ha using 1
  ring

/-- The source's polynomial envelope for order zero, with an explicit
constant depending only on R throughout the central band. -/
theorem profile_central_decay {μ : ℝ} (hμ : 0 < μ) (n : ℕ) (hn : 0 < n)
    (hleft : μ ≤ 2 * (n : ℝ)) (hright : (n : ℝ) ≤ 4 * μ) (R : ℕ) :
    profileNat μ n ≤
      (2 * (40 : ℝ)^R * (R.factorial : ℝ) * Real.exp (1/20)) *
        ((1 + |(n : ℝ)-μ| / Real.sqrt (1+μ))^R)⁻¹ := by
  let x := ((n : ℝ)-μ)/Real.sqrt (1+μ)
  have hab : |x| = |(n : ℝ)-μ| / Real.sqrt (1+μ) := by
    dsimp [x]
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hx : 1 + |x| ≤ 2 * (1+x^2) := by nlinarith [sq_nonneg (|x|-1), sq_abs x]
  have hp := pow_le_pow_left₀ (show 0 ≤ 1+|x| by positivity) hx R
  rw [mul_pow] at hp
  have h := profile_central_polynomial hμ n hn hleft hright R
  change profileNat μ n ≤ (2 * (20:ℝ)^R * (R.factorial:ℝ) * Real.exp (1/20)) / (1+x^2)^R at h
  rw [← hab, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1+|x|)^R)).mpr
  calc
    _ ≤ ((2 * (20:ℝ)^R * (R.factorial:ℝ) * Real.exp (1/20))/(1+x^2)^R) * (1+|x|)^R := by gcongr
    _ ≤ ((2 * (20:ℝ)^R * (R.factorial:ℝ) * Real.exp (1/20))/(1+x^2)^R) * ((2:ℝ)^R * (1+x^2)^R) := by gcongr
    _ = _ := by
      have hne : (1+x^2)^R ≠ 0 := by positivity
      rw [show (40:ℝ)^R = (20:ℝ)^R * (2:ℝ)^R by rw [← mul_pow]; norm_num]
      field_simp

/-- The first difference with actual Gaussian decay retained, uniformly in
μ≥2 and μ/2≤n≤4μ. -/
theorem profile_central_first_gaussian {μ : ℝ} (hμ : 2 ≤ μ) (n : ℕ)
    (hleft : μ ≤ 2 * (n : ℝ)) (hright : (n : ℝ) ≤ 4 * μ) :
    |profileNat μ (n+1)-profileNat μ n| ≤
      (4 * (|(n : ℝ)-μ|+1)/μ) * Real.exp (-((n : ℝ)-μ)^2/(20*μ)) := by
  have hμ₀ : 0 < μ := by linarith
  have hn : 0 < n := by
    by_contra! h
    simp only [Nat.le_zero.mp h, Nat.cast_zero, mul_zero] at hleft
    linarith
  have hx : (0:ℝ)<n+1 := by positivity
  have ht : |μ-((n:ℝ)+1)| ≤ |(n:ℝ)-μ|+1 := by
    have hh := abs_sub_le μ (n:ℝ) ((n:ℝ)+1)
    simpa [abs_sub_comm μ (n:ℝ)] using hh
  have hab : |μ/((n:ℝ)+1)-1| ≤ 2*(|(n:ℝ)-μ|+1)/μ := by
    have hid : μ/((n:ℝ)+1)-1 = (μ-((n:ℝ)+1))/((n:ℝ)+1) := by field_simp
    rw [hid, abs_div, abs_of_pos hx]
    apply (div_le_div_iff₀ hx hμ₀).mpr
    calc
      _ ≤ (|(n:ℝ)-μ|+1)*μ := mul_le_mul_of_nonneg_right ht hμ₀.le
      _ ≤ _ := by nlinarith [abs_nonneg ((n:ℝ)-μ)]
  calc
    _ ≤ profileNat μ n * |μ/((n:ℝ)+1)-1| := profile_first_difference hμ₀.le n
    _ ≤ (2 * Real.exp (-((n:ℝ)-μ)^2/(20*μ))) * (2*(|(n:ℝ)-μ|+1)/μ) :=
      mul_le_mul (profile_central_gaussian hμ₀ n hn hleft hright) hab (abs_nonneg _) (by positivity)
    _ = _ := by ring

end BourgainBasis
