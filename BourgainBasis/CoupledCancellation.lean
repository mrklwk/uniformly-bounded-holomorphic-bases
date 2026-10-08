module
public import BourgainBasis.CorrelationFourier
public import BourgainBasis.CoupledPhase
public import BourgainBasis.WeightedPacking
public import BourgainBasis.Autocorrelation

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- Square-root volume cancellation for the actual eliminated quadratic phase.
All mixed estimates, separation, packing and convergence are proved inputs. -/
theorem coupled_quadratic_cancellation {m : ℕ} (hm : 0 < m)
    (M c ξ : Fin m → ℝ) (N C₀ : ℝ) (w : Lattice m → ℂ)
    (hM : ∀ i, 1 ≤ M i) (hC : 0 ≤ C₀) (hw : WeightBound M c C₀ w) :
    Summable (fun n => w n*phase (coupledQuadraticPhase N ξ n)) ∧
    ‖∑' n, w n*phase (coupledQuadraticPhase N ξ n)‖ ≤
      Real.sqrt ((16:ℝ)^m*165888^m*(786432*(m:ℝ)^2)^m) *
        C₀ * Real.sqrt (∏ i, M i) := by
  let f : Lattice m → ℂ := fun n => w n*phase (coupledQuadraticPhase N ξ n)
  let A : ℝ := (16:ℝ)^m*C₀^2*165888^m*(∏ i, M i)
  let K : Lattice m → ℝ := fun h => envelope M 0 h*torusKernel M (coupledTorusPoint h)
  have hMn (i) : 0 ≤ M i := by linarith [hM i]
  have hP : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hMn i)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hk := weighted_coupled_packing hm M hM
  have hb (h : Lattice m) : ‖∑' n, f (n+h)*star (f n)‖ ≤ A*K h := by
    change ‖∑' n, (w (n+h)*phase (coupledQuadraticPhase N ξ (n+h))) *
      star (w n*phase (coupledQuadraticPhase N ξ n))‖ ≤ _
    rw [coupled_phase_correlation_tsum_norm]
    have hh := correlation_fourier_bound M c (coupledCharacterFrequency h) C₀ w hM hC hw h
    simp only [coupledCharacterFrequency_to_torus] at hh
    convert hh using 1
    dsimp [A, K]
    ring
  have hd : Summable (fun h => A*K h) := hk.1.mul_left A
  have hs := Summable.of_nonneg_of_le (fun h => norm_nonneg _) hb hd
  have hnorm : ‖∑' n, f n‖^2 ≤ A*(786432*(m:ℝ)^2)^m := by
    calc
      _ = ‖(∑' n, f n)*star (∑' n, f n)‖ := by rw [norm_mul, norm_star, pow_two]
      _ = ‖∑' h, ∑' n, f (n+h)*star (f n)‖ := by
        rw [weighted_phase_autocorrelation M c C₀ w hM hw (coupledQuadraticPhase N ξ)]
      _ ≤ ∑' h, ‖∑' n, f (n+h)*star (f n)‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' h, A*K h := hs.tsum_le_tsum hb hd
      _ = A*∑' h, K h := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left hk.2 hA
  refine ⟨weighted_phase_summable M c C₀ w hM hw _, ?_⟩
  have hD : 0 ≤ (16:ℝ)^m*165888^m*(786432*(m:ℝ)^2)^m := by positivity
  have hsqD := Real.sq_sqrt hD
  have hsqP := Real.sq_sqrt hP
  have hn := norm_nonneg (∑' n, f n)
  have hsD := Real.sqrt_nonneg ((16:ℝ)^m*165888^m*(786432*(m:ℝ)^2)^m)
  have hsP := Real.sqrt_nonneg (∏ i, M i)
  change ‖∑' n, f n‖ ≤ _
  have hright : 0 ≤ Real.sqrt ((16:ℝ)^m*165888^m*(786432*(m:ℝ)^2)^m)*C₀*Real.sqrt (∏ i, M i) :=
    mul_nonneg (mul_nonneg hsD hC) hsP
  apply (sq_le_sq₀ hn hright).mp
  rw [mul_pow, mul_pow, hsqD, hsqP]
  dsimp [A] at hnorm
  nlinarith only [hnorm]

end BourgainBasis
