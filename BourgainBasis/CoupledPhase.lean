module
public import BourgainBasis.CharacterBounds
public import BourgainBasis.TorusKernel

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- Exact phase after eliminating the last multinomial coordinate. N is allowed
to be any real number; in the polynomial application it is the degree. -/
def coupledQuadraticPhase {m : ℕ} (N : ℝ) (ξ : Fin m → ℝ) (n : Lattice m) : ℝ :=
  Real.sqrt 2*((∑ i, (n i:ℝ)^2)+(N-∑ i, (n i:ℝ))^2)+∑ i, ξ i*(n i:ℝ)

def coupledCharacterFrequency {m : ℕ} (h : Lattice m) (i : Fin m) : ℝ :=
  Real.sqrt 2*(coupledFrequency h i:ℝ)

def coupledPhaseConstant {m : ℕ} (N : ℝ) (ξ : Fin m → ℝ) (h : Lattice m) : ℝ :=
  Real.sqrt 2*((∑ i, (h i:ℝ)^2)+(∑ i, (h i:ℝ))^2-2*N*(∑ i, (h i:ℝ)))+
    ∑ i, ξ i*(h i:ℝ)

theorem coupledCharacterFrequency_linear {m : ℕ} (h n : Lattice m) :
    (∑ i, coupledCharacterFrequency h i*(n i:ℝ)) =
      Real.sqrt 2*(2*(∑ i, (n i:ℝ)*(h i:ℝ))+
        2*(∑ i, (n i:ℝ))*(∑ i, (h i:ℝ))) := by
  simp only [coupledCharacterFrequency, coupledFrequency, Int.cast_mul, Int.cast_ofNat,
    Int.cast_add, Int.cast_sum]
  simp_rw [show ∀ x y z : ℝ, Real.sqrt 2*(2*(x+y))*z =
    (2*Real.sqrt 2)*(z*x)+(2*Real.sqrt 2)*z*y by intros; ring]
  rw [Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Exact phase difference, including all N-dependent and linear constant terms. -/
theorem coupledQuadraticPhase_difference {m : ℕ} (N : ℝ) (ξ : Fin m → ℝ)
    (n h : Lattice m) :
    coupledQuadraticPhase N ξ (n+h)-coupledQuadraticPhase N ξ n =
      coupledPhaseConstant N ξ h+∑ i, coupledCharacterFrequency h i*(n i:ℝ) := by
  rw [coupledCharacterFrequency_linear]
  have hp := eliminated_phase_difference (fun i => (n i:ℝ)) (fun i => (h i:ℝ)) N
  unfold coupledQuadraticPhase coupledPhaseConstant
  simp only [Pi.add_apply, Int.cast_add]
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hp' := congrArg (fun z : ℝ => Real.sqrt 2*z) hp
  simp only [Finset.sum_add_distrib] at hp'
  nlinarith only [hp']

theorem star_phase (t : ℝ) : star (phase t) = phase (-t) := by
  change starRingEnd ℂ (Complex.exp _) = Complex.exp _
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- Exact weighted autocorrelation identity for the actual oscillatory sum. -/
theorem coupled_phase_correlation {m : ℕ} (N : ℝ) (ξ : Fin m → ℝ)
    (w : Lattice m → ℂ) (n h : Lattice m) :
    (w (n+h)*phase (coupledQuadraticPhase N ξ (n+h))) *
      star (w n*phase (coupledQuadraticPhase N ξ n)) =
    phase (coupledPhaseConstant N ξ h) * (w (n+h)*star (w n)) *
      latticeCharacter (coupledCharacterFrequency h) n := by
  rw [star_mul, star_phase]
  have hp : phase (coupledQuadraticPhase N ξ (n+h))*phase (-coupledQuadraticPhase N ξ n) =
      phase (coupledPhaseConstant N ξ h)*latticeCharacter (coupledCharacterFrequency h) n := by
    rw [← phase_add, ← sub_eq_add_neg, coupledQuadraticPhase_difference, phase_add]
    rfl
  calc
    _ = (w (n+h)*star (w n)) *
        (phase (coupledQuadraticPhase N ξ (n+h))*phase (-coupledQuadraticPhase N ξ n)) := by ring
    _ = _ := by rw [hp]; ring

/-- The real frequencies used in the character are precisely the torus points
already controlled by concrete anisotropic packing. -/
theorem coupledCharacterFrequency_to_torus {m : ℕ} (h : Lattice m) (i : Fin m) :
    (coupledCharacterFrequency h i:UnitAddCircle) = coupledTorusPoint h i := by
  unfold coupledCharacterFrequency coupledTorusPoint
  congr 1
  ring

/-- The constant phase has unit modulus and disappears from the autocorrelation
norm. This is an algebraic tsum identity; convergence is supplied separately by
the proved weight-correlation and oscillatory summability theorems. -/
theorem coupled_phase_correlation_tsum_norm {m : ℕ} (N : ℝ) (ξ : Fin m → ℝ)
    (w : Lattice m → ℂ) (h : Lattice m) :
    ‖∑' n, (w (n+h)*phase (coupledQuadraticPhase N ξ (n+h))) *
      star (w n*phase (coupledQuadraticPhase N ξ n))‖ =
    ‖∑' n, (w (n+h)*star (w n))*latticeCharacter (coupledCharacterFrequency h) n‖ := by
  simp_rw [coupled_phase_correlation, mul_assoc]
  rw [tsum_mul_left, norm_mul, norm_phase, one_mul]

end BourgainBasis
