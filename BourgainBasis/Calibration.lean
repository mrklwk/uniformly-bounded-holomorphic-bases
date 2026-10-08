module
public import BourgainBasis.Contracts

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- Summation by parts for a lattice character. The hypotheses are only its
shift law, a nonzero multiplier, and absolute convergence of the original sum. -/
theorem summation_by_parts (f χ : ℤ → ℂ) (ζ : ℂ) (hζ : ζ ≠ 0)
    (hχ : ∀ n, χ (n + 1) = ζ * χ n)
    (hf : Summable (fun n => f n * χ n)) :
    Summable (fun n => (f (n + 1) - f n) * χ n) ∧
    (∑' n, (f (n + 1) - f n) * χ n) = (ζ⁻¹ - 1) * ∑' n, f n * χ n := by
  have hs : Summable (fun n : ℤ => f (n + 1) * χ (n + 1)) :=
    (Equiv.addRight (1 : ℤ)).summable_iff.mpr hf
  have he : (fun n => (f (n + 1) - f n) * χ n) =
      (fun n => ζ⁻¹ * (f (n + 1) * χ (n + 1)) - f n * χ n) := by
    funext n
    rw [hχ]
    field_simp
  rw [he]
  refine ⟨(hs.mul_left ζ⁻¹).sub hf, ?_⟩
  rw [((hs.mul_left ζ⁻¹).tsum_sub hf), tsum_mul_left]
  have ht := (Equiv.addRight (1 : ℤ)).tsum_eq (fun n => f n * χ n)
  change (∑' n : ℤ, f (n + 1) * χ (n + 1)) = ∑' n, f n * χ n at ht
  rw [ht]
  ring

/-- The order-two version used for each high-frequency coordinate. -/
theorem summation_by_parts_twice (f χ : ℤ → ℂ) (ζ : ℂ) (hζ : ζ ≠ 0)
    (hχ : ∀ n, χ (n + 1) = ζ * χ n)
    (hf : Summable (fun n => f n * χ n)) :
    (∑' n, ((f (n + 1 + 1) - f (n + 1)) - (f (n + 1) - f n)) * χ n) =
      (ζ⁻¹ - 1)^2 * ∑' n, f n * χ n := by
  have h₁ := summation_by_parts f χ ζ hζ hχ hf
  have h₂ := summation_by_parts (fun n => f (n + 1) - f n) χ ζ hζ hχ h₁.1
  rw [h₂.2, h₁.2]
  ring

/-- The one-coordinate product rule, with the shifts actually used in the paper. -/
theorem slanted_first (f g : ℤ → ℝ) (x t : ℤ) :
    f (x + 1) * g (t - 1) - f x * g t =
      (f (x + 1) - f x) * g (t - 1) - f x * (g t - g (t - 1)) := by ring

/-- Polarization of the quadratic form used after eliminating the largest mean. -/
theorem eliminated_phase_difference {m : ℕ} (x h : Fin m → ℝ) (N : ℝ) :
    ((∑ i, (x i + h i)^2) + (N - ∑ i, (x i + h i))^2) -
      ((∑ i, x i ^ 2) + (N - ∑ i, x i)^2) =
    (∑ i, h i ^ 2) + (∑ i, h i)^2 +
      2 * (∑ i, x i * h i) + 2 * (∑ i, x i) * (∑ i, h i) -
      2 * N * (∑ i, h i) := by
  have hp : (∑ i, (x i + h i)^2) =
      (∑ i, x i ^ 2) + (∑ i, h i ^ 2) + 2 * ∑ i, x i * h i := by
    simp only [add_sq, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hp, Finset.sum_add_distrib]
  ring

theorem poisson_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) : 0 ≤ poisson μ n := by
  unfold poisson
  positivity

theorem poisson_succ (μ : ℝ) (n : ℕ) :
    poisson μ (n + 1) = poisson μ n * (μ / (n + 1)) := by
  unfold poisson
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem profileNat_nonneg (μ : ℝ) (n : ℕ) : 0 ≤ profileNat μ n := by
  unfold profileNat
  positivity

theorem profileNat_succ {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) :
    profileNat μ (n + 1) = profileNat μ n * Real.sqrt (μ / (n + 1)) := by
  unfold profileNat
  rw [poisson_succ, Real.sqrt_mul (poisson_nonneg hμ n)]
  ring

theorem sqrt_sub_one_bound {t : ℝ} (ht : 0 ≤ t) :
    |Real.sqrt t - 1| ≤ |t - 1| := by
  have hs := Real.sq_sqrt ht
  have hn := Real.sqrt_nonneg t
  rcases le_total 1 (Real.sqrt t) with h | h
  · rw [abs_of_nonneg (by linarith : 0 ≤ Real.sqrt t - 1),
      abs_of_nonneg (by nlinarith : 0 ≤ t - 1)]
    nlinarith
  · rw [abs_of_nonpos (by linarith : Real.sqrt t - 1 ≤ 0),
      abs_of_nonpos (by nlinarith : t - 1 ≤ 0)]
    nlinarith [sq_nonneg (Real.sqrt t)]

/-- Genuine finite-difference estimate, uniform in all nonnegative means and n≥0.
Near n≈μ this gives the first-difference gain; global tails and higher differences
remain separate obligations, not hypotheses hidden in a full-profile theorem. -/
theorem profile_first_difference {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) :
    |profileNat μ (n + 1) - profileNat μ n| ≤
      profileNat μ n * |μ / (n + 1) - 1| := by
  rw [profileNat_succ hμ]
  calc
    |profileNat μ n * Real.sqrt (μ / (n + 1)) - profileNat μ n| =
        profileNat μ n * |Real.sqrt (μ / (n + 1)) - 1| := by
      rw [← mul_sub_one, abs_mul, abs_of_nonneg (profileNat_nonneg μ n)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sqrt_sub_one_bound (by positivity))
      (profileNat_nonneg μ n)

theorem profile_nat (μ : ℝ) (n : ℕ) : profile μ (n : ℤ) = profileNat μ n := by
  simp [profile]

/-- The estimate for the actual zero-extended profile at nonnegative indices. -/
theorem profile_first_difference_int {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) :
    |deltaOne (profile μ) (n : ℤ)| ≤ profile μ (n : ℤ) * |μ / (n + 1) - 1| := by
  have hs : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by simp
  rw [deltaOne, hs, profile_nat, profile_nat]
  exact profile_first_difference hμ n

end BourgainBasis
