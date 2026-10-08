module
public import BourgainBasis.DifferenceAlgebra
public import BourgainBasis.LatticeSummation

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

def wordDelta {m : ℕ} (l : List (Fin m)) (f : Lattice m → ℂ) : Lattice m → ℂ :=
  l.foldr delta f

def indexWord {m : ℕ} (ν : Fin m → ℕ) : List (Fin m) :=
  (List.ofFn fun i => List.replicate (ν i) i).flatten

theorem wordDelta_permutation {m : ℕ} {l k : List (Fin m)} (hp : l.Perm k)
    (f : Lattice m → ℂ) : wordDelta l f = wordDelta k f := by
  exact hp.foldr_eq' (fun i _ j _ f => delta_commute j i f) f

theorem wordDelta_append {m : ℕ} (l k : List (Fin m)) (f : Lattice m → ℂ) :
    wordDelta (l++k) f = wordDelta l (wordDelta k f) := by
  exact List.foldr_append

theorem wordDelta_replicate {m : ℕ} (i : Fin m) (k : ℕ) (f : Lattice m → ℂ) :
    wordDelta (List.replicate k i) f = ((delta i)^[k]) f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change delta i (wordDelta (List.replicate k i) f) = _
    rw [ih, Function.iterate_succ_apply']

theorem wordDelta_indexWord {m : ℕ} (ν : Fin m → ℕ) (f : Lattice m → ℂ) :
    wordDelta (indexWord ν) f = mixedDelta ν f := by
  have hh (l : List (Fin m)) :
      wordDelta ((l.map (fun i => List.replicate (ν i) i)).flatten) f =
        (l.map (fun i => (delta i)^[ν i])).foldr (· ∘ ·) id f := by
    induction l generalizing f with
    | nil => rfl
    | cons i l ih =>
      simp only [List.map_cons, List.flatten_cons, List.foldr_cons, Function.comp_apply]
      rw [wordDelta_append, wordDelta_replicate, ih]
  simpa [indexWord, mixedDelta, List.map_ofFn] using hh (List.ofFn id)

theorem count_indexWord {m : ℕ} (ν : Fin m → ℕ) (i : Fin m) :
    (indexWord ν).count i = ν i := by
  simp [indexWord, List.count_flatten, List.map_ofFn, List.count_replicate,
    List.sum_ofFn, Finset.sum_ite_eq']

theorem wordDelta_eq_mixedDelta {m : ℕ} (l : List (Fin m)) (f : Lattice m → ℂ) :
    wordDelta l f = mixedDelta (fun i => l.count i) f := by
  rw [← wordDelta_indexWord]
  apply wordDelta_permutation
  apply List.perm_iff_count.mpr
  intro i
  rw [count_indexWord]

theorem wordDelta_translate {m : ℕ} (l : List (Fin m)) (h : Lattice m)
    (f : Lattice m → ℂ) : wordDelta l (translate h f) = translate h (wordDelta l f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change delta i (wordDelta l (translate h f)) = translate h (delta i (wordDelta l f))
    rw [ih, delta_translate]

theorem wordDelta_star {m : ℕ} (l : List (Fin m)) (f : Lattice m → ℂ) :
    wordDelta l (fun n => star (f n)) = fun n => star (wordDelta l f n) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change delta i (wordDelta l (fun n => star (f n))) = _
    rw [ih, delta_star]
    rfl

/-- The full mixed-character multiplier, with summability preserved at each step. -/
theorem word_summation_by_parts {m : ℕ} (l : List (Fin m)) (f χ : Lattice m → ℂ)
    (ζ : Fin m → ℂ) (hζ : ∀ i, ζ i ≠ 0)
    (hχ : ∀ i n, χ (n+Pi.single i 1) = ζ i*χ n)
    (hf : Summable (fun n => f n*χ n)) :
    Summable (fun n => wordDelta l f n * χ n) ∧
    (∑' n, wordDelta l f n * χ n) =
      (l.map (fun i => (ζ i)⁻¹-1)).prod * ∑' n, f n*χ n := by
  induction l with
  | nil => simpa [wordDelta] using hf
  | cons i l ih =>
    have hh := lattice_summation_by_parts i (wordDelta l f) χ (ζ i) (hζ i) (hχ i) ih.1
    refine ⟨hh.1, ?_⟩
    change (∑' n, delta i (wordDelta l f) n * χ n) = _
    rw [hh.2, ih.2]
    simp [mul_assoc]

/-- The source's multi-index form, including the exact product multiplier. -/
theorem mixed_summation_by_parts {m : ℕ} (ν : Fin m → ℕ) (f χ : Lattice m → ℂ)
    (ζ : Fin m → ℂ) (hζ : ∀ i, ζ i ≠ 0)
    (hχ : ∀ i n, χ (n+Pi.single i 1) = ζ i*χ n)
    (hf : Summable (fun n => f n*χ n)) :
    Summable (fun n => mixedDelta ν f n * χ n) ∧
    (∑' n, mixedDelta ν f n * χ n) =
      (∏ i, ((ζ i)⁻¹-1)^(ν i)) * ∑' n, f n*χ n := by
  have hh := word_summation_by_parts (indexWord ν) f χ ζ hζ hχ hf
  rw [wordDelta_indexWord] at hh
  simpa [indexWord, List.map_flatten, List.prod_flatten, List.map_ofFn,
    List.prod_ofFn] using hh

theorem word_weight_bound {m : ℕ} {M c : Fin m → ℝ} {C₀ : ℝ}
    {w : Lattice m → ℂ} (hw : WeightBound M c C₀ w) (l : List (Fin m))
    (hl : ∀ i, l.count i ≤ 2) (n : Lattice m) :
    ‖wordDelta l w n‖ ≤ C₀*(∏ i, (M i^(l.count i))⁻¹)*envelope M c n := by
  rw [wordDelta_eq_mixedDelta]
  exact hw _ hl n

end BourgainBasis
