module
public import BourgainBasis.MixedLeibniz
public import BourgainBasis.EnvelopeShifts
public import BourgainBasis.ListNormBounds

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

theorem word_scale_split {m : ℕ} (M : Fin m → ℝ) (l : List (Fin m))
    (p : List (Fin m) × List (Fin m)) (hp : p ∈ wordSplits l) :
    (∏ i, (M i^(p.1.count i))⁻¹)*(∏ i, (M i^(p.2.count i))⁻¹) =
      ∏ i, (M i^(l.count i))⁻¹ := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← mul_inv, ← pow_add, wordSplits_counts l p hp i]

/-- Every mixed derivative of the actual correlation is absolutely summable, with
all derivative-scale gains and all shift-decay factors retained. -/
theorem word_correlation_bound {m : ℕ} (M c : Fin m → ℝ) (C₀ : ℝ)
    (w : Lattice m → ℂ) (hM : ∀ i, 1 ≤ M i) (hC : 0 ≤ C₀)
    (hw : WeightBound M c C₀ w) (l : List (Fin m)) (hl : ∀ i, l.count i ≤ 2)
    (h : Lattice m) :
    Summable (fun n => ‖wordDelta l (fun n => w (n+h)*star (w n)) n‖) ∧
    (∑' n, ‖wordDelta l (fun n => w (n+h)*star (w n)) n‖) ≤
      (2:ℝ)^l.length * ((C₀^2*(∏ i, (M i^(l.count i))⁻¹)) *
        (165888^m*(∏ i, M i)*envelope M 0 h)) := by
  let F := fun (p : List (Fin m) × List (Fin m)) (n : Lattice m) =>
    wordDelta p.1 w (n+h)*star (wordDelta p.2 w (n+wordShift p.1))
  have hh := list_sum_norm_bound (wordSplits l) F
    ((C₀^2*(∏ i, (M i^(l.count i))⁻¹))*(165888^m*(∏ i, M i)*envelope M 0 h))
  have hp (p : List (Fin m) × List (Fin m)) (hp : p ∈ wordSplits l) :
      Summable (fun n => ‖F p n‖) ∧ (∑' n, ‖F p n‖) ≤
        (C₀^2*(∏ i, (M i^(l.count i))⁻¹))*(165888^m*(∏ i, M i)*envelope M 0 h) := by
    have hc := wordSplits_counts l p hp
    have ha (i) : p.1.count i ≤ 2 := by have := hc i; have := hl i; omega
    have hb (i) : p.2.count i ≤ 2 := by have := hc i; have := hl i; omega
    have hk (i) : |((wordShift p.1 i):ℝ)| ≤ 2 := by
      simp only [wordShift, Int.cast_natCast, Nat.abs_cast]
      exact_mod_cast ha i
    have he := mixedDelta_shifted_correlation M c C₀ w hM hC hw
      (fun i => p.1.count i) (fun i => p.2.count i) ha hb h (wordShift p.1) hk
    simp only [← wordDelta_eq_mixedDelta] at he
    rw [mul_assoc (C₀^2), word_scale_split M l p hp] at he
    exact he
  have hh' := hh hp
  have hid (n : Lattice m) : wordDelta l (fun n => w (n+h)*star (w n)) n =
      ((wordSplits l).map (fun p => F p n)).sum := by
    rw [wordDelta_product]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    have ht := congrFun (wordDelta_translate p.1 h w) n
    have hs := congrFun (wordDelta_star p.2 w) (n+wordShift p.1)
    change wordDelta p.1 (translate h w) n * _ = _
    rw [ht, hs]
    rfl
  simpa only [← hid, wordSplits_length, Nat.cast_pow, Nat.cast_ofNat] using hh'

/-- Exact source mixed-index estimate; the combinatorial factor is explicit. -/
theorem mixed_correlation_bound {m : ℕ} (M c : Fin m → ℝ) (C₀ : ℝ)
    (w : Lattice m → ℂ) (hM : ∀ i, 1 ≤ M i) (hC : 0 ≤ C₀)
    (hw : WeightBound M c C₀ w) (ν : Fin m → ℕ) (hν : ∀ i, ν i ≤ 2)
    (h : Lattice m) :
    Summable (fun n => ‖mixedDelta ν (fun n => w (n+h)*star (w n)) n‖) ∧
    (∑' n, ‖mixedDelta ν (fun n => w (n+h)*star (w n)) n‖) ≤
      (2:ℝ)^(∑ i, ν i) * ((C₀^2*(∏ i, (M i^(ν i))⁻¹)) *
        (165888^m*(∏ i, M i)*envelope M 0 h)) := by
  have he := word_correlation_bound M c C₀ w hM hC hw (indexWord ν)
    (fun i => by rw [count_indexWord]; exact hν i) h
  rw [wordDelta_indexWord] at he
  simp only [count_indexWord] at he
  simpa only [indexWord, List.length_flatten, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply, List.length_replicate] using he

end BourgainBasis
