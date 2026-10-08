module
public import BourgainBasis.MixedCorrelation
public import BourgainBasis.CharacterBounds
public import BourgainBasis.FrequencySelection
public import BourgainBasis.TorusPacking

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- Full frequency decay for the actual correlation from the source WeightBound. -/
theorem correlation_fourier_bound {m : ℕ} (M c θ : Fin m → ℝ) (C₀ : ℝ)
    (w : Lattice m → ℂ) (hM : ∀ i, 1 ≤ M i) (hC : 0 ≤ C₀)
    (hw : WeightBound M c C₀ w) (h : Lattice m) :
    ‖∑' n, (w (n+h)*star (w n))*latticeCharacter θ n‖ ≤
      (16:ℝ)^m * (C₀^2*(165888^m*(∏ i, M i)*envelope M 0 h)) *
        torusKernel M (fun i => (θ i:UnitAddCircle)) := by
  let f : Lattice m → ℂ := fun n => w (n+h)*star (w n)
  let χ := latticeCharacter θ
  let B : ℝ := C₀^2*(165888^m*(∏ i, M i)*envelope M 0 h)
  have hMn (i) : 0 ≤ M i := by linarith [hM i]
  have hMp (i) : 0 < M i := by linarith [hM i]
  have hs : Summable (fun n => f n*χ n) := by
    apply Summable.of_norm
    simpa only [f, χ, norm_mul, norm_latticeCharacter, mul_one] using
      (weight_correlation_bound M c C₀ w hM hC hw h).1
  change ‖∑' n, f n*χ n‖ ≤ (16:ℝ)^m*B*∏ i, ((1+M i*‖(θ i:UnitAddCircle)‖)^2)⁻¹
  refine frequency_selection (‖∑' n, f n*χ n‖) B (fun i => M i*‖(θ i:UnitAddCircle)‖)
    (fun i => M i*‖(phase (θ i))⁻¹-1‖) (norm_nonneg _) ?_
    (fun i => mul_nonneg (hMn i) (norm_nonneg _)) ?_ ?_
  · have he := envelope_nonneg M 0 h
    dsimp [B]
    exact mul_nonneg (sq_nonneg _) (mul_nonneg
      (mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => hMn i))) he)
  · intro i
    apply mul_le_mul_of_nonneg_left _ (hMn i)
    have hh := phase_inv_sub_one_lower (θ i)
    linarith [norm_nonneg (θ i:UnitAddCircle)]
  · intro ν hν
    have hd := mixed_correlation_bound M c C₀ w hM hC hw ν hν h
    have hc := mixed_summation_by_parts ν f χ (fun i => phase (θ i))
      (fun i => phase_ne_zero _) (latticeCharacter_shift θ) hs
    have hdχ : Summable (fun n => ‖mixedDelta ν f n * χ n‖) := by
      simpa only [f, χ, norm_mul, norm_latticeCharacter, mul_one] using hd.1
    have hnorm : ‖∑' n, f n*χ n‖*(∏ i, ‖(phase (θ i))⁻¹-1‖^(ν i)) ≤
        (2:ℝ)^(∑ i, ν i) * ((C₀^2*(∏ i, (M i^(ν i))⁻¹)) *
          (165888^m*(∏ i, M i)*envelope M 0 h)) := by
      calc
        _ = ‖∑' n, mixedDelta ν f n*χ n‖ := by
          rw [hc.2]
          simp only [norm_mul, norm_prod, norm_pow]
          ring
        _ ≤ ∑' n, ‖mixedDelta ν f n*χ n‖ := norm_tsum_le_tsum_norm hdχ
        _ = ∑' n, ‖mixedDelta ν f n‖ := by simp only [χ, norm_mul, norm_latticeCharacter, mul_one]
        _ ≤ _ := hd.2
    have hP : (∏ i, M i^(ν i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr
      (fun i _ => pow_ne_zero _ (hMp i).ne')
    have hcancel : (∏ i, (M i^(ν i))⁻¹)*(∏ i, M i^(ν i)) = 1 := by
      rw [Finset.prod_inv_distrib, inv_mul_cancel₀ hP]
    have hscale : 0 ≤ ∏ i, M i^(ν i) :=
      Finset.prod_nonneg (fun i _ => pow_nonneg (hMn i) _)
    have hb := mul_le_mul_of_nonneg_right hnorm hscale
    calc
      _ = (‖∑' n, f n*χ n‖*(∏ i, ‖(phase (θ i))⁻¹-1‖^(ν i)))*(∏ i, M i^(ν i)) := by
        simp only [mul_pow, Finset.prod_mul_distrib]
        ring
      _ ≤ _ := hb
      _ = B*(2:ℝ)^(∑ i, ν i) := by
        dsimp [B]
        calc
          _ = (C₀^2*(165888^m*(∏ i, M i)*envelope M 0 h))*(2:ℝ)^(∑ i, ν i) *
              ((∏ i, (M i^(ν i))⁻¹)*(∏ i, M i^(ν i))) := by ring
          _ = _ := by rw [hcancel, mul_one]

end BourgainBasis
