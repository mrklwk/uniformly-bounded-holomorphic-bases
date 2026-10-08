module
public import BourgainBasis.MixedWords

@[expose] public section

noncomputable section
namespace BourgainBasis

def wordShift {m : ℕ} (l : List (Fin m)) : Lattice m :=
  fun i => (l.count i : ℤ)

def wordSplits {m : ℕ} : List (Fin m) → List (List (Fin m) × List (Fin m))
  | [] => [([],[])]
  | i::l => (wordSplits l).map (fun p => (i::p.1,p.2)) ++
      (wordSplits l).map (fun p => (p.1,i::p.2))

theorem wordShift_cons {m : ℕ} (i : Fin m) (l : List (Fin m)) :
    wordShift (i::l) = wordShift l + Pi.single i 1 := by
  ext j
  by_cases hj : i=j
  · subst j; simp [wordShift]
  · simp [wordShift, hj, Ne.symm hj, Pi.single_eq_of_ne]

theorem wordSplits_length {m : ℕ} (l : List (Fin m)) :
    (wordSplits l).length = 2^l.length := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [wordSplits, ih, pow_succ, Nat.mul_two]

theorem wordSplits_counts {m : ℕ} (l : List (Fin m))
    (p : List (Fin m) × List (Fin m)) (hp : p ∈ wordSplits l) (i : Fin m) :
    p.1.count i + p.2.count i = l.count i := by
  induction l generalizing p with
  | nil => simp [wordSplits] at hp; subst p; rfl
  | cons j l ih =>
    simp only [wordSplits, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
    · have hh := ih q hq
      simp only [List.count_cons]
      omega
    · have hh := ih q hq
      simp only [List.count_cons]
      omega

theorem delta_list_sum {m : ℕ} {α : Type*} (i : Fin m) (l : List α)
    (f : α → Lattice m → ℂ) (n : Lattice m) :
    delta i (fun n => (l.map (fun a => f a n)).sum) n =
      (l.map (fun a => delta i (f a) n)).sum := by
  induction l with
  | nil => simp [delta]
  | cons a l ih => simp only [List.map_cons, List.sum_cons, delta] at *; linear_combination ih

/-- Exact mixed discrete Leibniz rule. Splits retain multiplicity, hence encode all
binomial coefficients without an assumed product-rule estimate. -/
theorem wordDelta_product {m : ℕ} (l : List (Fin m)) (f g : Lattice m → ℂ)
    (n : Lattice m) :
    wordDelta l (fun n => f n*g n) n =
      ((wordSplits l).map (fun p => wordDelta p.1 f n *
        wordDelta p.2 g (n+wordShift p.1))).sum := by
  induction l generalizing n with
  | nil =>
    have hz : wordShift ([] : List (Fin m)) = 0 := by ext i; simp [wordShift]
    simp [wordDelta, wordSplits, hz]
  | cons i l ih =>
    have he : wordDelta l (fun n => f n*g n) =
        fun n => ((wordSplits l).map (fun p => wordDelta p.1 f n *
          wordDelta p.2 g (n+wordShift p.1))).sum := funext ih
    change delta i (wordDelta l (fun n => f n*g n)) n = _
    rw [he, delta_list_sum]
    simp only [wordSplits, List.map_append, List.map_map, List.sum_append]
    rw [← List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    dsimp only [Function.comp_apply]
    rw [delta_product]
    simp only [wordDelta, List.foldr_cons, wordShift_cons]
    unfold delta
    have hs : n + Pi.single i 1 + wordShift p.1 = n + (wordShift p.1 + Pi.single i 1) := by abel
    rw [hs]
    simp only [add_assoc]
    rw [add_comm (Pi.single i 1) (wordShift p.1)]

end BourgainBasis
