module
public import BourgainBasis.WeightCorrelation

@[expose] public section

noncomputable section
namespace BourgainBasis

/-- Difference/position coordinates on pairs of lattice points. -/
def correlationEquiv (m : ℕ) : (Lattice m × Lattice m) ≃ (Lattice m × Lattice m) where
  toFun p := (p.2+p.1,p.2)
  invFun p := (p.1-p.2,p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

/-- All rearrangements in the squared-sum identity are justified by absolute convergence. -/
theorem autocorrelation_summable {m : ℕ} (f : Lattice m → ℂ)
    (hf : Summable (fun n => ‖f n‖)) :
    Summable (fun p : Lattice m × Lattice m => ‖f (p.2+p.1) * star (f p.2)‖) := by
  have hg : Summable (fun n => ‖star (f n)‖) := by simpa only [norm_star] using hf
  have hp := hf.mul_norm hg
  exact (correlationEquiv m).summable_iff.mpr hp

/-- The actual complex squared-sum correlation identity on the whole lattice. -/
theorem autocorrelation_identity {m : ℕ} (f : Lattice m → ℂ)
    (hf : Summable (fun n => ‖f n‖)) :
    (∑' n, f n) * star (∑' n, f n) =
      ∑' h : Lattice m, ∑' n : Lattice m, f (n+h) * star (f n) := by
  have hg : Summable (fun n => ‖star (f n)‖) := by simpa only [norm_star] using hf
  rw [tsum_star, tsum_mul_tsum_of_summable_norm hf hg]
  rw [← (correlationEquiv m).tsum_eq (fun p => f p.1 * star (f p.2))]
  exact (autocorrelation_summable f hf).of_norm.tsum_prod

/-- Specialization to the source weight hypothesis and any unimodular phase. -/
theorem weighted_phase_autocorrelation {m : ℕ} (M c : Fin m → ℝ) (C₀ : ℝ)
    (w : Lattice m → ℂ) (hM : ∀ i, 1 ≤ M i) (hw : WeightBound M c C₀ w)
    (q : Lattice m → ℝ) :
    let f := fun n => w n * phase (q n)
    (∑' n, f n) * star (∑' n, f n) =
      ∑' h : Lattice m, ∑' n : Lattice m, f (n+h) * star (f n) := by
  apply autocorrelation_identity
  simpa only [norm_mul, norm_phase, mul_one] using weight_norm_summable M c C₀ w hM hw

end BourgainBasis
