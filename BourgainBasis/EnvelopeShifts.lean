module
public import BourgainBasis.WeightCorrelation

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- A shift of at most twice the scale costs 3^4, uniformly in positive M. -/
theorem decay4_shift_two_scale {M : ℝ} (hM : 0 < M) (x t : ℝ) (ht : |t| ≤ 2*M) :
    decay4 M (x+t) ≤ 81*decay4 M x := by
  have ha : 0 < 1+|x+t|/M := by positivity
  have hb : 0 < 1+|x|/M := by positivity
  have hd : |x| ≤ |x+t|+2*M := by
    have hh : |x| ≤ |x+t|+|t| := by
      simpa using abs_sub_le (x+t) 0 t
    linarith
  have hc : 1+|x|/M ≤ 3*(1+|x+t|/M) := by
    have hh := div_le_div_of_nonneg_right hd hM.le
    rw [add_div, mul_div_cancel_right₀ _ hM.ne'] at hh
    have : 0 ≤ |x+t|/M := by positivity
    linarith
  have hp := pow_le_pow_left₀ hb.le hc 4
  norm_num [mul_pow] at hp
  unfold decay4
  rw [← one_div, ← one_div, mul_one_div]
  apply (div_le_div_iff₀ (pow_pos ha 4) (pow_pos hb 4)).mpr
  linarith

theorem decay4_shift_two {M : ℝ} (hM : 1 ≤ M) (x t : ℝ) (ht : |t| ≤ 2) :
    decay4 M (x+t) ≤ 81*decay4 M x :=
  decay4_shift_two_scale (by linarith) x t (by linarith)

/-- Bounded coordinate shifts, including negative coordinates and zero shifts. -/
theorem envelope_shift_two_bound {m : ℕ} (M c : Fin m → ℝ) (hM : ∀ i, 1 ≤ M i)
    (n k : Lattice m) (hk : ∀ i, |(k i:ℝ)| ≤ 2) :
    envelope M c (n+k) ≤ 81^m * envelope M c n := by
  change (∏ i, decay4 (M i) (((n+k) i:ℝ)-c i)) ≤
    81^m * ∏ i, decay4 (M i) ((n i:ℝ)-c i)
  calc
    _ ≤ ∏ i, 81*decay4 (M i) ((n i:ℝ)-c i) := by
      apply Finset.prod_le_prod₀ (fun i _ => decay4_nonneg _ _)
      intro i _
      simpa only [Pi.add_apply, Int.cast_add, add_sub_right_comm] using
        decay4_shift_two (hM i) ((n i:ℝ)-c i) (k i:ℝ) (hk i)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- Shifted center correlation retains full decay in the arbitrary shift h, while
the auxiliary shift k contributes only a dimension constant. -/
theorem envelope_shifted_correlation {m : ℕ} (M c : Fin m → ℝ)
    (hM : ∀ i, 1 ≤ M i) (h k : Lattice m) (hk : ∀ i, |(k i:ℝ)| ≤ 2) :
    Summable (fun n => envelope M c (n+h)*envelope M c (n+k)) ∧
    (∑' n, envelope M c (n+h)*envelope M c (n+k)) ≤
      165888^m * (∏ i, M i) * envelope M 0 h := by
  let a := fun i => c i-(h i:ℝ)
  have hs := (envelope_correlation_hasSum M a c (fun i => by linarith [hM i])).summable
  have hb (n : Lattice m) : envelope M c (n+h)*envelope M c (n+k) ≤
      81^m * (envelope M a n*envelope M c n) := by
    calc
      _ ≤ envelope M c (n+h) * (81^m*envelope M c n) :=
        mul_le_mul_of_nonneg_left (envelope_shift_two_bound M c hM n k hk)
          (envelope_nonneg _ _ _)
      _ = _ := by rw [envelope_translate]; ring
  have hs' := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (envelope_nonneg _ _ _) (envelope_nonneg _ _ _)) hb (hs.mul_left (81^m))
  refine ⟨hs', ?_⟩
  calc
    _ ≤ ∑' n, 81^m*(envelope M a n*envelope M c n) := hs'.tsum_le_tsum hb (hs.mul_left _)
    _ = 81^m*∑' n, envelope M a n*envelope M c n := tsum_mul_left
    _ ≤ 81^m*(2048^m*(∏ i, M i)*∏ i, decay4 (M i) (a i-c i)) :=
      mul_le_mul_of_nonneg_left (envelope_convolution_bound M a c hM) (by positivity)
    _ = _ := by
      have he : (∏ i, decay4 (M i) (a i-c i)) = envelope M 0 h := by
        apply Finset.prod_congr rfl
        intro i _
        simp [a, decay4, sub_sub_cancel_left, abs_neg]
      rw [he]
      have hc : (81:ℝ)^m*2048^m = 165888^m := by rw [← mul_pow]; norm_num
      rw [← mul_assoc, ← mul_assoc, hc]

/-- Every pair of permitted mixed derivatives has an absolutely summable shifted
correlation. All derivative scale gains and every h-coordinate decay are retained. -/
theorem mixedDelta_shifted_correlation {m : ℕ} (M c : Fin m → ℝ) (C₀ : ℝ)
    (w : Lattice m → ℂ) (hM : ∀ i, 1 ≤ M i) (hC : 0 ≤ C₀)
    (hw : WeightBound M c C₀ w) (α β : Fin m → ℕ)
    (hα : ∀ i, α i ≤ 2) (hβ : ∀ i, β i ≤ 2)
    (h k : Lattice m) (hk : ∀ i, |(k i:ℝ)| ≤ 2) :
    Summable (fun n => ‖mixedDelta α w (n+h)*star (mixedDelta β w (n+k))‖) ∧
    (∑' n, ‖mixedDelta α w (n+h)*star (mixedDelta β w (n+k))‖) ≤
      (C₀^2*(∏ i, (M i^α i)⁻¹)*(∏ i, (M i^β i)⁻¹)) *
      (165888^m*(∏ i, M i)*envelope M 0 h) := by
  let A := C₀*(∏ i, (M i^α i)⁻¹)
  let B := C₀*(∏ i, (M i^β i)⁻¹)
  have hAn : 0 ≤ A := mul_nonneg hC (Finset.prod_nonneg (fun i _ =>
    inv_nonneg.mpr (pow_nonneg (by linarith [hM i]) _)))
  have hBn : 0 ≤ B := mul_nonneg hC (Finset.prod_nonneg (fun i _ =>
    inv_nonneg.mpr (pow_nonneg (by linarith [hM i]) _)))
  have he := envelope_shifted_correlation M c hM h k hk
  have hb (n : Lattice m) : ‖mixedDelta α w (n+h)*star (mixedDelta β w (n+k))‖ ≤
      (A*B)*(envelope M c (n+h)*envelope M c (n+k)) := by
    rw [norm_mul, norm_star]
    calc
      _ ≤ (A*envelope M c (n+h))*(B*envelope M c (n+k)) :=
        mul_le_mul (hw α hα _) (hw β hβ _) (norm_nonneg _)
          (mul_nonneg hAn (envelope_nonneg _ _ _))
      _ = _ := by ring
  have hs := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb (he.1.mul_left (A*B))
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n, (A*B)*(envelope M c (n+h)*envelope M c (n+k)) :=
      hs.tsum_le_tsum hb (he.1.mul_left _)
    _ = (A*B)*∑' n, envelope M c (n+h)*envelope M c (n+k) := tsum_mul_left
    _ ≤ (A*B)*(165888^m*(∏ i, M i)*envelope M 0 h) :=
      mul_le_mul_of_nonneg_left he.2 (mul_nonneg hAn hBn)
    _ = _ := by dsimp [A, B]; ring

end BourgainBasis
