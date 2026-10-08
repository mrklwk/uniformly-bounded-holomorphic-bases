module
public import BourgainBasis.TensorEnvelope

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

theorem envelope_nonneg {m : ℕ} (M c : Fin m → ℝ) (n : Lattice m) :
    0 ≤ envelope M c n := by
  exact Finset.prod_nonneg (fun i _ => decay4_nonneg _ _)

theorem weight_pointwise {m : ℕ} {M c : Fin m → ℝ} {C₀ : ℝ}
    {w : Lattice m → ℂ} (hw : WeightBound M c C₀ w) (n : Lattice m) :
    ‖w n‖ ≤ C₀ * envelope M c n := by
  have h := hw (fun _ => 0) (by simp) n
  simpa only [mixedDelta_zero, pow_zero, inv_one, Finset.prod_const_one, mul_one] using h

theorem envelope_translate {m : ℕ} (M c : Fin m → ℝ) (h n : Lattice m) :
    envelope M c (n+h) = envelope M (fun i => c i-(h i:ℝ)) n := by
  unfold envelope
  congr 1
  funext i
  simp only [Pi.add_apply, Int.cast_add]
  rw [show (n i : ℝ) + (h i : ℝ) - c i = (n i : ℝ) - (c i - (h i : ℝ)) by ring]

/-- Summable autocorrelation with explicit decay in each shift coordinate. -/
theorem weight_correlation_bound {m : ℕ} (M c : Fin m → ℝ) (C₀ : ℝ)
    (w : Lattice m → ℂ) (hM : ∀ i, 1 ≤ M i) (hC : 0 ≤ C₀)
    (hw : WeightBound M c C₀ w) (h : Lattice m) :
    Summable (fun n => ‖w (n+h) * star (w n)‖) ∧
    (∑' n, ‖w (n+h) * star (w n)‖) ≤
      C₀^2 * (2048^m * (∏ i, M i) * ∏ i, decay4 (M i) (h i:ℝ)) := by
  let a : Fin m → ℝ := fun i => c i-(h i:ℝ)
  have he := (envelope_correlation_hasSum M a c (fun i => by linarith [hM i])).summable.mul_left (C₀^2)
  have hb (n : Lattice m) : ‖w (n+h) * star (w n)‖ ≤
      C₀^2 * (envelope M a n * envelope M c n) := by
    rw [norm_mul, norm_star]
    calc
      _ ≤ (C₀*envelope M c (n+h))*(C₀*envelope M c n) :=
        mul_le_mul (weight_pointwise hw _) (weight_pointwise hw _) (norm_nonneg _)
          (mul_nonneg hC (envelope_nonneg _ _ _))
      _ = _ := by rw [envelope_translate]; ring
  have hs := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb he
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n, C₀^2 * (envelope M a n * envelope M c n) := hs.tsum_le_tsum hb he
    _ = C₀^2 * ∑' n, envelope M a n * envelope M c n := tsum_mul_left
    _ ≤ C₀^2 * (2048^m * (∏ i, M i) * ∏ i, decay4 (M i) (a i-c i)) :=
      mul_le_mul_of_nonneg_left (envelope_convolution_bound M a c hM) (sq_nonneg _)
    _ = _ := by
      congr 2
      apply Finset.prod_congr rfl
      intro i _
      simp [a, decay4, sub_sub_cancel_left, abs_neg]

end BourgainBasis
