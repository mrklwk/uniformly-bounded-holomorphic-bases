module
public import BourgainBasis.TensorEnvelope

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

theorem phase_ne_zero (t : ℝ) : phase t ≠ 0 := Complex.exp_ne_zero _

theorem phase_add (s t : ℝ) : phase (s+t) = phase s*phase t := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_neg (t : ℝ) : phase (-t) = (phase t)⁻¹ := by
  unfold phase
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem phase_sub (s t : ℝ) : phase (s-t) = phase s / phase t := by
  rw [sub_eq_add_neg, phase_add, phase_neg, div_eq_mul_inv]

theorem phase_int (p : ℤ) : phase (p:ℝ) = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I p using 1
  congr 1
  push_cast
  ring

theorem phase_sub_int (t : ℝ) (p : ℤ) : phase (t-p) = phase t := by
  rw [phase_sub, phase_int, div_one]

/-- Exact chord length for the source's exponential phase normalization. -/
theorem norm_phase_sub_one (t : ℝ) : ‖phase t-1‖ = 2*|Real.sin (Real.pi*t)| := by
  unfold phase
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
  congr 3
  ring

/-- Uniform chord-distance lower bound, obtained from Jordan's inequality after
reducing by the nearest integer. This includes integer and half-integer endpoints. -/
theorem phase_sub_one_lower (t : ℝ) :
    4*‖(t:UnitAddCircle)‖ ≤ ‖phase t-1‖ := by
  let u := t-(round t:ℝ)
  have hu : |u| ≤ 1/2 := abs_sub_round t
  have hpi := Real.pi_pos
  have harg : |Real.pi*u| ≤ Real.pi/2 := by
    rw [abs_mul, abs_of_pos hpi]
    nlinarith
  have hs := Real.mul_abs_le_abs_sin harg
  rw [abs_mul, abs_of_pos hpi] at hs
  have hs' : 2*|u| ≤ |Real.sin (Real.pi*u)| := by
    have he : 2/Real.pi*(Real.pi*|u|) = 2*|u| := by field_simp
    rwa [he] at hs
  rw [← phase_sub_int t (round t), norm_phase_sub_one, UnitAddCircle.norm_eq]
  change 4*|u| ≤ 2*|Real.sin (Real.pi*u)|
  linarith

/-- The multiplier appearing in summation by parts has the same lower bound. -/
theorem phase_inv_sub_one_lower (t : ℝ) :
    4*‖(t:UnitAddCircle)‖ ≤ ‖(phase t)⁻¹-1‖ := by
  simpa only [phase_neg, AddCircle.coe_neg, norm_neg] using phase_sub_one_lower (-t)

def latticeCharacter {m : ℕ} (θ : Fin m → ℝ) (n : Lattice m) : ℂ :=
  phase (∑ i, θ i*(n i:ℝ))

theorem norm_latticeCharacter {m : ℕ} (θ : Fin m → ℝ) (n : Lattice m) :
    ‖latticeCharacter θ n‖ = 1 := norm_phase _

theorem latticeCharacter_add {m : ℕ} (θ : Fin m → ℝ) (n h : Lattice m) :
    latticeCharacter θ (n+h) = latticeCharacter θ n*latticeCharacter θ h := by
  unfold latticeCharacter
  simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib, phase_add]

theorem latticeCharacter_single {m : ℕ} (θ : Fin m → ℝ) (i : Fin m) :
    latticeCharacter θ (Pi.single i 1) = phase (θ i) := by
  unfold latticeCharacter
  congr 1
  simp [Pi.single_apply]

theorem latticeCharacter_shift {m : ℕ} (θ : Fin m → ℝ) (i : Fin m) (n : Lattice m) :
    latticeCharacter θ (n+Pi.single i 1) = phase (θ i)*latticeCharacter θ n := by
  rw [latticeCharacter_add, latticeCharacter_single, mul_comm]

/-- Zero-order and twice-differenced bounds combine into the torus kernel factor,
with no division by a possibly zero character multiplier. Integer frequencies and
zero scales are handled by the zero-order branch. -/
theorem character_two_bound (M θ y A : ℝ) (hM : 0 ≤ M) (hy : 0 ≤ y)
    (hA : 0 ≤ A) (hzero : y ≤ A)
    (htwo : (M*‖(phase θ)⁻¹-1‖)^2*y ≤ A) :
    y ≤ 4*A*((1+M*‖(θ:UnitAddCircle)‖)^2)⁻¹ := by
  let d := ‖(θ:UnitAddCircle)‖
  let z := ‖(phase θ)⁻¹-1‖
  have hd : 0 ≤ d := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have hl : 4*d ≤ z := phase_inv_sub_one_lower θ
  have hden : 0 < (1+M*d)^2 := by positivity
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hden).mpr
  by_cases hlow : M*d ≤ 1
  · have hsq : (1+M*d)^2 ≤ 4 := by nlinarith [mul_nonneg hM hd]
    have hp := mul_le_mul_of_nonneg_left hsq hy
    nlinarith
  · have hhigh : 1 < M*d := lt_of_not_ge hlow
    have hlinear : 1+M*d ≤ M*z := by nlinarith [mul_le_mul_of_nonneg_left hl hM]
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1+M*d) hlinear 2
    have hp := mul_le_mul_of_nonneg_right hsq hy
    change (M*z)^2*y ≤ A at htwo
    nlinarith

end BourgainBasis
