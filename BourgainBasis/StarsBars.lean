module
public import BourgainBasis.BasisCombinatorics

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

def degreeIndices (m N : ℕ) := {α : Fin (m+1) → ℕ // ∑ i, α i = N}

instance degreeIndicesFintype (m N : ℕ) : Fintype (degreeIndices m N) :=
  Fintype.ofEquiv (Sym (Fin (m+1)) N) (Sym.equivNatSumOfFintype (Fin (m+1)) N)

def barPrefix {m N : ℕ} (α : degreeIndices m N) (j : Fin m) : ℕ :=
  ∑ k ∈ (Finset.univ : Finset (Fin (m+1))).filter (fun k => k.val ≤ j.val), α.val k

theorem barPrefix_le {m N : ℕ} (α : degreeIndices m N) (j : Fin m) :
    barPrefix α j ≤ N := by
  calc
    _ ≤ ∑ i, α.val i := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = N := α.property

theorem barPrefix_mono {m N : ℕ} (α : degreeIndices m N) {i j : Fin m} (hij : i ≤ j) :
    barPrefix α i ≤ barPrefix α j := by
  apply Finset.sum_le_sum_of_subset
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact hk.trans hij

/-- Zero-based form of the source s_j=j+α₁+...+α_j (one-based j). -/
def barEntry {m N : ℕ} (α : degreeIndices m N) (j : Fin m) : Fin (N+m) :=
  ⟨j.val+barPrefix α j, by have := barPrefix_le α j; have := j.isLt; omega⟩

theorem barEntry_strictMono {m N : ℕ} (α : degreeIndices m N) : StrictMono (barEntry α) := by
  intro i j hij
  change i.val+barPrefix α i < j.val+barPrefix α j
  have hh := barPrefix_mono α (le_of_lt hij)
  exact Nat.add_lt_add_of_lt_of_le hij hh

def barsSubset {m N : ℕ} (α : degreeIndices m N) : Finset (Fin (N+m)) :=
  Finset.univ.image (barEntry α)

theorem barsSubset_card {m N : ℕ} (α : degreeIndices m N) : (barsSubset α).card = m := by
  rw [barsSubset, Finset.card_image_of_injective _ (barEntry_strictMono α).injective]
  simp

theorem barEntry_mem {m N : ℕ} (α : degreeIndices m N) (j : Fin m) :
    barEntry α j ∈ barsSubset α := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-- The sorted enumeration of the image is exactly the prescribed cumulative bars. -/
theorem barEntry_orderEmb {m N : ℕ} (α : degreeIndices m N) :
    barEntry α = (barsSubset α).orderEmbOfFin (barsSubset_card α) :=
  Finset.orderEmbOfFin_unique (barsSubset_card α) (barEntry_mem α) (barEntry_strictMono α)

/-- Inclusive cumulative sums together with the fixed total determine every
coordinate, including the last coordinate and the dimension-zero case. -/
theorem degreeIndices_eq_of_prefix {m N : ℕ} (α β : degreeIndices m N)
    (hp : ∀ j, barPrefix α j = barPrefix β j) : α=β := by
  have hall (j : Fin (m+1)) :
      (∑ k ∈ Finset.univ.filter (fun k : Fin (m+1) => k.val ≤ j.val), α.val k) =
      ∑ k ∈ Finset.univ.filter (fun k : Fin (m+1) => k.val ≤ j.val), β.val k := by
    by_cases hj : j.val < m
    · exact hp ⟨j.val, hj⟩
    · have hf : Finset.univ.filter (fun k : Fin (m+1) => k.val ≤ j.val) = Finset.univ := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        have := j.isLt
        have := k.isLt
        omega
      rw [hf, α.property, β.property]
  have hcoord : ∀ n, ∀ hn : n < m+1, α.val ⟨n,hn⟩ = β.val ⟨n,hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      let j : Fin (m+1) := ⟨n,hn⟩
      let s := Finset.univ.filter (fun k : Fin (m+1) => k.val ≤ j.val)
      have hj : j ∈ s := by simp [s]
      have he : (∑ k ∈ s.erase j, α.val k) = ∑ k ∈ s.erase j, β.val k := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k.val < n := by
          obtain ⟨hkne, hks⟩ := Finset.mem_erase.mp hk
          have hkle : k.val ≤ n := (Finset.mem_filter.mp hks).2
          have hkne' : k.val ≠ n := by
            intro h
            apply hkne
            exact Fin.ext h
          omega
        exact ih k.val hkn k.isLt
      have ha := Finset.sum_erase_add s α.val hj
      have hb := Finset.sum_erase_add s β.val hj
      have hh := hall j
      change (∑ k ∈ s, α.val k) = ∑ k ∈ s, β.val k at hh
      change α.val j = β.val j
      omega
  apply Subtype.ext
  funext j
  exact hcoord j.val j.isLt

theorem barsSubset_injective {m N : ℕ} : Function.Injective (@barsSubset m N) := by
  intro α β he
  have hentry : barEntry α = barEntry β := by
    calc
      barEntry α = (barsSubset β).orderEmbOfFin (barsSubset_card β) :=
        Finset.orderEmbOfFin_unique (barsSubset_card β)
          (fun j => by rw [← he]; exact barEntry_mem α j) (barEntry_strictMono α)
      _ = barEntry β := (barEntry_orderEmb β).symm
  apply degreeIndices_eq_of_prefix α β
  intro j
  have hv := congrArg Fin.val (congrFun hentry j)
  change j.val+barPrefix α j = j.val+barPrefix β j at hv
  omega

/-- The exact source map into m-subsets of N+m slots (zero-based storage only). -/
def starsBarsMap {m N : ℕ} (α : degreeIndices m N) : Set.powersetCard (Fin (N+m)) m :=
  ⟨barsSubset α, barsSubset_card α⟩

theorem starsBarsMap_injective {m N : ℕ} : Function.Injective (@starsBarsMap m N) := by
  intro α β he
  exact barsSubset_injective (congrArg Subtype.val he)

/-- Surjectivity of the prescribed map follows from its proved injectivity and
exact source cardinalities, not from choosing an unrelated abstract bijection. -/
theorem starsBarsMap_bijective (m N : ℕ) : Function.Bijective (@starsBarsMap m N) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨starsBarsMap_injective, ?_⟩
  rw [← Nat.card_eq_fintype_card]
  change Nat.card {α : Fin (m+1) → ℕ // ∑ i, α i=N} = _
  rw [homogeneous_index_card]
  symm
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
  simp

/-- The exact cumulative stars-and-bars equivalence, valid also for m=0 and N=0. -/
def starsBarsEquiv (m N : ℕ) : degreeIndices m N ≃ Set.powersetCard (Fin (N+m)) m :=
  Equiv.ofBijective starsBarsMap (starsBarsMap_bijective m N)

theorem starsBarsEquiv_apply {m N : ℕ} (α : degreeIndices m N) :
    starsBarsEquiv m N α = starsBarsMap α := rfl

/-- Direct compatibility with the increasing subset enumeration used in minors. -/
theorem starsBarsEquiv_sorted {m N : ℕ} (α : degreeIndices m N) (j : Fin m) :
    Set.powersetCard.ofFinEmbEquiv.symm (starsBarsEquiv m N α) j = barEntry α j := by
  change (barsSubset α).orderEmbOfFin (barsSubset_card α) j = barEntry α j
  exact (congrFun (barEntry_orderEmb α) j).symm

/-- Restoring one-based indices recovers exactly the source's bar formula. -/
theorem barEntry_source_position {m N : ℕ} (α : degreeIndices m N) (j : Fin m) :
    (barEntry α j).val+1 = (j.val+1)+barPrefix α j := by
  change (j.val+barPrefix α j)+1 = _
  omega

theorem degreeIndices_card (m N : ℕ) : Fintype.card (degreeIndices m N) = (N+m).choose m := by
  rw [← Nat.card_eq_fintype_card]
  exact homogeneous_index_card N m

end BourgainBasis
