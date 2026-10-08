module
public import BourgainBasis.SphereMoments
public import Mathlib.Analysis.Complex.Isometry

@[expose] public section

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgainBasis

theorem complex_gaussian_diagonal_real (a : ℕ) :
    (∫ z : ℂ, ‖z‖^(2*a)*Real.exp (-‖z‖^2)) = Real.pi*a.factorial := by
  have h := Complex.integral_rpow_mul_exp_neg_rpow (p := (2:ℝ))
    (q := ((2*a:ℕ):ℝ)) (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) (2*a); linarith)
  have he : (((2*a:ℕ):ℝ)+2)/2 = (a:ℝ)+1 := by push_cast; ring
  rw [he, Real.Gamma_nat_eq_factorial] at h
  simp only [Real.rpow_natCast, Real.rpow_two] at h
  convert h using 1
  ring

theorem complex_gaussian_diagonal (a : ℕ) :
    (∫ z : ℂ, z^a*star (z^a)*(Real.exp (-‖z‖^2):ℂ)) =
      (Real.pi:ℂ)*(a.factorial:ℂ) := by
  calc
    _ = ∫ z : ℂ, ((‖z‖^(2*a)*Real.exp (-‖z‖^2):ℝ):ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [star_pow, Complex.star_def, ← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.ofReal_mul, Complex.ofReal_pow, pow_mul]
    _ = Complex.ofReal (∫ z : ℂ, ‖z‖^(2*a)*Real.exp (-‖z‖^2)) := integral_ofReal
    _ = _ := by rw [complex_gaussian_diagonal_real]; push_cast; rfl

end BourgainBasis
