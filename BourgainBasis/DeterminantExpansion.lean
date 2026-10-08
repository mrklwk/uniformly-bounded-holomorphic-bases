module
public import BourgainBasis.BasisFormula

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

theorem phase_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    phase (∑ i ∈ s,f i) = ∏ i ∈ s,phase (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phase]
  | @insert a s ha ih => simp [Finset.sum_insert,Finset.prod_insert,ha,phase_add,ih]

/-- Each term in the exact minor expansion has the common Fourier scale. -/
theorem source_minor_expansion {m N : ℕ} (T : Set.powersetCard (Fin (N+m)) m)
    (α : degreeIndices m N) :
    orderedMinorMatrix m (sourceFourier (N+m)) T (starsBarsEquiv m N α) =
      ((Real.sqrt ((N+m:ℕ):ℝ):ℂ)⁻¹)^m *
        ∑ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ : ℂ) *
          phase (∑ j : Fin m,
            (((Set.powersetCard.ofFinEmbEquiv.symm T) (σ j)).val+1:ℝ) *
              ((barEntry α j).val+1:ℝ) / (N+m:ℝ)) := by
  unfold orderedMinorMatrix
  rw [Matrix.det_apply',Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.submatrix_apply,starsBarsEquiv_sorted,sourceFourier,
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [←phase_finset_sum]
  push_cast
  ring

/-- Stars-and-bars turns every Fourier determinant term into an affine phase. -/
theorem weighted_barEntry_affine {m N : ℕ} (α : degreeIndices m N) (a : Fin m → ℝ) :
    (∑ j : Fin m,a j*((barEntry α j).val+1:ℝ)) =
      (∑ j : Fin m,a j*(j.val+1:ℝ)) +
      ∑ k : Fin (m+1),(∑ j : Fin m,if k.val≤j.val then a j else 0)*(α.val k:ℝ) := by
  simp only [barEntry,barPrefix]
  push_cast
  simp_rw [show ∀ j : Fin m, a j*((j.val:ℝ)+
      (∑ k ∈ Finset.univ.filter (fun k : Fin (m+1) => k.val≤j.val),(α.val k:ℝ))+1) =
      a j*((j.val:ℝ)+1)+a j*(∑ k ∈ Finset.univ.filter
        (fun k : Fin (m+1) => k.val≤j.val),(α.val k:ℝ)) by intro j; ring]
  rw [Finset.sum_add_distrib]
  congr 1
  simp_rw [Finset.mul_sum,Finset.sum_mul,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

def sourcePermutationWeights {m N : ℕ} (T : Set.powersetCard (Fin (N+m)) m)
    (σ : Equiv.Perm (Fin m)) (j : Fin m) : ℝ :=
  (((Set.powersetCard.ofFinEmbEquiv.symm T) (σ j)).val+1:ℝ)/(N+m:ℝ)

def sourcePermutationConstant {m N : ℕ} (T : Set.powersetCard (Fin (N+m)) m)
    (σ : Equiv.Perm (Fin m)) : ℝ := ∑ j,sourcePermutationWeights T σ j*(j.val+1:ℝ)

def sourcePermutationFrequency {m N : ℕ} (T : Set.powersetCard (Fin (N+m)) m)
    (σ : Equiv.Perm (Fin m)) (k : Fin (m+1)) : ℝ :=
  ∑ j : Fin m,if k.val≤j.val then sourcePermutationWeights T σ j else 0

/-- The exact source determinant is a signed sum of affine characters in α. -/
theorem source_minor_affine_expansion {m N : ℕ} (T : Set.powersetCard (Fin (N+m)) m)
    (α : degreeIndices m N) :
    orderedMinorMatrix m (sourceFourier (N+m)) T (starsBarsEquiv m N α) =
      ((Real.sqrt ((N+m:ℕ):ℝ):ℂ)⁻¹)^m *
        ∑ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ : ℂ) *
          phase (sourcePermutationConstant T σ +
            ∑ k,sourcePermutationFrequency T σ k*(α.val k:ℝ)) := by
  rw [source_minor_expansion]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 2
  calc
    _ = ∑ j,sourcePermutationWeights T σ j*((barEntry α j).val+1:ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      unfold sourcePermutationWeights
      ring
    _ = _ := weighted_barEntry_affine α (sourcePermutationWeights T σ)

end BourgainBasis
