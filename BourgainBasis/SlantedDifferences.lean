module
public import BourgainBasis.MixedLeibniz
public import BourgainBasis.PoissonConditioning

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- Complex scalar forward difference, compatible with the real source operator. -/
def scalarDelta (g : ℤ → ℂ) : ℤ → ℂ := fun t => g (t+1)-g t

theorem scalarDelta_real_iterate (g : ℤ → ℝ) (j : ℕ) :
    (scalarDelta^[j]) (fun t => (g t:ℂ)) = fun t => ((deltaOne^[j]) g t:ℂ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih]
    funext t
    simp [scalarDelta,deltaOne]

theorem lattice_sum_step {m : ℕ} (n : Lattice m) (i : Fin m) :
    (∑ j : Fin m, ((n + (Pi.single i 1 : Lattice m)) : Lattice m) j) = (∑ j, n j)+1 := by
  simp [Pi.add_apply,Finset.sum_add_distrib,Pi.single_apply]

/-- Every coordinate differentiation of a slanted factor is the same backward
scalar difference. Iteration records its exact common translation and sign. -/
theorem wordDelta_slanted {m : ℕ} (l : List (Fin m)) (g : ℤ → ℂ)
    (t : ℤ) (n : Lattice m) :
    wordDelta l (fun n => g (t-∑ i,n i)) n =
      (-1:ℂ)^l.length * (scalarDelta^[l.length]) g (t-(∑ i,n i)-(l.length:ℤ)) := by
  induction l generalizing n with
  | nil => simp [wordDelta]
  | cons i l ih =>
    change wordDelta l (fun n => g (t-∑ i,n i)) (n+Pi.single i 1) -
      wordDelta l (fun n => g (t-∑ i,n i)) n = _
    rw [ih,ih,lattice_sum_step]
    simp only [List.length_cons,Function.iterate_succ_apply',scalarDelta,Nat.cast_add,Nat.cast_one,pow_succ]
    rw [show t-((∑ i,n i)+1)-(l.length:ℤ) = t-(∑ i,n i)-((l.length:ℤ)+1) by omega,
      show t-(∑ i,n i)-((l.length:ℤ)+1)+1 = t-(∑ i,n i)-(l.length:ℤ) by omega]
    ring

theorem indexWord_length {m : ℕ} (ν : Fin m → ℕ) :
    (indexWord ν).length = ∑ i,ν i := by
  simp [indexWord,List.length_flatten,List.map_ofFn,List.sum_ofFn]

/-- Source multi-index form: total order controls the last scalar difference. -/
theorem mixedDelta_slanted {m : ℕ} (ν : Fin m → ℕ) (g : ℤ → ℂ)
    (t : ℤ) (n : Lattice m) :
    mixedDelta ν (fun n => g (t-∑ i,n i)) n =
      (-1:ℂ)^(∑ i,ν i) * (scalarDelta^[∑ i,ν i]) g
        (t-(∑ i,n i)-(((∑ i,ν i):ℕ):ℤ)) := by
  rw [←wordDelta_indexWord,wordDelta_slanted,indexWord_length]

/-- The source's real deltaOne operator is used without changing its convention. -/
theorem mixedDelta_slanted_real {m : ℕ} (ν : Fin m → ℕ) (g : ℤ → ℝ)
    (t : ℤ) (n : Lattice m) :
    mixedDelta ν (fun n => (g (t-∑ i,n i):ℂ)) n =
      (-1:ℂ)^(∑ i,ν i) * ((deltaOne^[∑ i,ν i]) g
        (t-(∑ i,n i)-(((∑ i,ν i):ℕ):ℤ)):ℂ) := by
  have h := mixedDelta_slanted ν (fun x => (g x:ℂ)) t n
  simpa only [scalarDelta_real_iterate] using h

/-- The sum of coordinate shifts in a word is exactly its length. -/
theorem sum_wordShift {m : ℕ} (l : List (Fin m)) :
    (∑ i,wordShift l i) = (l.length:ℤ) := by
  induction l with
  | nil => simp [wordShift]
  | cons i l ih =>
    rw [wordShift_cons,lattice_sum_step,ih]
    simp

/-- Every Leibniz split preserves total order, including multiplicity. -/
theorem wordSplits_lengths {m : ℕ} (l : List (Fin m))
    (p : List (Fin m) × List (Fin m)) (hp : p∈wordSplits l) :
    p.1.length+p.2.length=l.length := by
  induction l generalizing p with
  | nil => simp [wordSplits] at hp; subst p; rfl
  | cons i l ih =>
    simp only [wordSplits,List.mem_append,List.mem_map] at hp
    rcases hp with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
    · have h := ih q hq
      simp only [List.length_cons]
      omega
    · have h := ih q hq
      simp only [List.length_cons]
      omega

/-- Full exact slanted Leibniz identity. All summands evaluate the final
scalar difference at the common t−sum(n)−length(l), as required by conditioning.
The split list preserves the binomial multiplicities. -/
theorem wordDelta_slanted_product {m : ℕ} (l : List (Fin m))
    (f : Lattice m → ℂ) (g : ℤ → ℂ) (t : ℤ) (n : Lattice m) :
    wordDelta l (fun n => f n*g (t-∑ i,n i)) n =
      ((wordSplits l).map (fun p => wordDelta p.1 f n *
        ((-1:ℂ)^p.2.length * (scalarDelta^[p.2.length]) g
          (t-(∑ i,n i)-(l.length:ℤ))))).sum := by
  rw [wordDelta_product]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [wordDelta_slanted]
  have hl := wordSplits_lengths l p hp
  have hs : (∑ i,(n+wordShift p.1) i) = (∑ i,n i)+(p.1.length:ℤ) := by
    simp only [Pi.add_apply,Finset.sum_add_distrib,sum_wordShift]
  rw [hs]
  rw [show t-((∑ i,n i)+(p.1.length:ℤ))-(p.2.length:ℤ) =
    t-(∑ i,n i)-(l.length:ℤ) by omega]

/-- Real-profile version of the common-shift formula, connected directly to
both source operators mixedDelta and deltaOne. -/
theorem mixedDelta_slanted_product_real {m : ℕ} (ν : Fin m → ℕ)
    (f : Lattice m → ℂ) (g : ℤ → ℝ) (t : ℤ) (n : Lattice m) :
    mixedDelta ν (fun n => f n*(g (t-∑ i,n i):ℂ)) n =
      ((wordSplits (indexWord ν)).map (fun p => wordDelta p.1 f n *
        ((-1:ℂ)^p.2.length * ((deltaOne^[p.2.length]) g
          (t-(∑ i,n i)-(((∑ i,ν i):ℕ):ℤ)):ℂ)))).sum := by
  have h := wordDelta_slanted_product (indexWord ν) f (fun x => (g x:ℂ)) t n
  simpa only [wordDelta_indexWord,indexWord_length,scalarDelta_real_iterate] using h

/-- A coordinate difference differentiates exactly one factor of a tensor. -/
theorem delta_tensor {m : ℕ} (f : Fin m → ℤ → ℂ) (i : Fin m) (n : Lattice m) :
    delta i (fun n => ∏ j,f j (n j)) n =
      ∏ j,(if j=i then scalarDelta (f j) else f j) (n j) := by
  classical
  have split (h : Fin m → ℤ → ℂ) (x : Lattice m) :
      (∏ j,h j (x j)) = h i (x i) * ∏ j ∈ Finset.univ.erase i,h j (x j) := by
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  rw [delta,split f,split f,split (fun j => if j=i then scalarDelta (f j) else f j)]
  have hs : (∏ j ∈ Finset.univ.erase i,f j (((n+(Pi.single i 1 : Lattice m)):Lattice m) j)) =
      ∏ j ∈ Finset.univ.erase i,f j (n j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j≠i := (Finset.mem_erase.mp hj).1
    simp [Pi.single_eq_of_ne hji]
  have ht : (∏ j ∈ Finset.univ.erase i,(if j=i then scalarDelta (f j) else f j) (n j)) =
      ∏ j ∈ Finset.univ.erase i,f j (n j) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [(Finset.mem_erase.mp hj).1]
  rw [hs,ht]
  simp [scalarDelta,sub_mul]

/-- All coordinate factors differentiate independently, in arbitrary word order. -/
theorem wordDelta_tensor {m : ℕ} (l : List (Fin m)) (f : Fin m → ℤ → ℂ)
    (n : Lattice m) :
    wordDelta l (fun n => ∏ i,f i (n i)) n =
      ∏ i,(scalarDelta^[l.count i]) (f i) (n i) := by
  induction l generalizing n with
  | nil => simp [wordDelta]
  | cons i l ih =>
    have he : wordDelta l (fun n => ∏ j,f j (n j)) =
        fun n => ∏ j,(scalarDelta^[l.count j]) (f j) (n j) := funext ih
    change delta i (wordDelta l (fun n => ∏ j,f j (n j))) n = _
    rw [he,delta_tensor]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : j=i
    · subst j
      simp only [ite_true,List.count_cons_self,Function.iterate_succ_apply']
    · simp [hj,Ne.symm hj]

/-- Complete tensor-slanted identity with scalar differences in every factor.
The common final shift and the binomial multiplicities are both explicit. -/
theorem mixedDelta_tensor_slanted_real {m : ℕ} (ν : Fin m → ℕ)
    (f : Fin m → ℤ → ℝ) (g : ℤ → ℝ) (t : ℤ) (n : Lattice m) :
    mixedDelta ν (fun n => (∏ i,(f i (n i):ℂ))*(g (t-∑ i,n i):ℂ)) n =
      ((wordSplits (indexWord ν)).map (fun p =>
        (∏ i,((deltaOne^[p.1.count i]) (f i) (n i):ℂ)) *
        ((-1:ℂ)^p.2.length * ((deltaOne^[p.2.length]) g
          (t-(∑ i,n i)-(((∑ i,ν i):ℕ):ℤ)):ℂ)))).sum := by
  rw [mixedDelta_slanted_product_real]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rw [wordDelta_tensor p.1 (fun i x => (f i x:ℂ)) n]
  simp only [scalarDelta_real_iterate]

end BourgainBasis
