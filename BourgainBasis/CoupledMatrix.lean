module
public import BourgainBasis.CoupledCancellation

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

def coupledMatrix (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  fun i j => (if i=j then 1 else 0)+1

theorem coupledMatrix_symmetric (m : ℕ) (i j : Fin m) :
    coupledMatrix m i j = coupledMatrix m j i := by
  simp [coupledMatrix, eq_comm]

theorem coupledMatrix_energy {m : ℕ} (x : Fin m → ℝ) :
    (∑ i, ∑ j, x i*(coupledMatrix m i j:ℝ)*x j) =
      (∑ i, (x i)^2)+(∑ i, x i)^2 := by
  simp only [coupledMatrix, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero,
    mul_add, add_mul, Finset.sum_add_distrib]
  have he (i : Fin m) : (∑ j, x i*(if i=j then 1 else 0)*x j) = (x i)^2 := by
    simp [mul_ite, ite_mul, pow_two]
  simp_rw [he]
  rw [pow_two, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [Finset.mul_sum]

theorem coupledMatrix_positiveDefinite (m : ℕ) : positiveDefinite (coupledMatrix m) := by
  intro x hx
  rw [coupledMatrix_energy]
  have hex : ∃ i, x i ≠ 0 := by
    by_contra! hh
    apply hx
    ext i
    exact hh i
  obtain ⟨i, hi⟩ := hex
  have hs : 0 < ∑ j, (x j)^2 := Finset.sum_pos' (fun j _ => sq_nonneg _)
    ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  linarith [sq_nonneg (∑ i, x i)]

theorem quadratic_coupledMatrix {m : ℕ} (n : Lattice m) :
    quadratic (coupledMatrix m) n =
      (∑ i, (n i:ℝ)^2)+(∑ i, (n i:ℝ))^2 := coupledMatrix_energy _

/-- The concrete SPD-matrix specialization of the source quadratic-cancellation
contract. This is derived from the proved sum estimate, not an assumed target. -/
theorem coupledMatrix_cancellation {m : ℕ} (hm : 0 < m)
    (M c ξ : Fin m → ℝ) (C₀ : ℝ) (w : Lattice m → ℂ)
    (hM : ∀ i, 1 ≤ M i) (hC : 0 ≤ C₀) (hw : WeightBound M c C₀ w) :
    Summable (fun n => w n*phase (Real.sqrt 2*quadratic (coupledMatrix m) n+
      ∑ i, ξ i*(n i:ℝ))) ∧
    ‖∑' n, w n*phase (Real.sqrt 2*quadratic (coupledMatrix m) n+∑ i, ξ i*(n i:ℝ))‖ ≤
      Real.sqrt ((16:ℝ)^m*165888^m*(786432*(m:ℝ)^2)^m)*C₀*Real.sqrt (∏ i, M i) := by
  have hh := coupled_quadratic_cancellation hm M c ξ 0 C₀ w hM hC hw
  simpa only [coupledQuadraticPhase, zero_sub, neg_sq, ← quadratic_coupledMatrix] using hh

end BourgainBasis
