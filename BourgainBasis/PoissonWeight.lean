module
public import BourgainBasis.PoissonComplete
public import BourgainBasis.MixedCorrelation

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- The final profile's scale dominates the coordinate scales, so its scalar
order can supply exactly the missing coordinate gains. -/
theorem last_scale_word_bound {m : ℕ} (M : Fin m → ℝ) (L : ℝ)
    (hM : ∀ i,0<M i) (hL : 0<L) (hML : ∀ i,M i≤L) (l : List (Fin m)) :
    (L^l.length)⁻¹ ≤ ∏ i,(M i^(l.count i))⁻¹ := by
  have hs : ∑ i,l.count i=l.length := by
    have h := sum_wordShift l
    simp only [wordShift] at h
    exact_mod_cast h
  rw [←hs,←Finset.prod_pow_eq_pow_sum,←Finset.prod_inv_distrib]
  apply Finset.prod_le_prod₀ (fun i _ => by positivity)
  intro i _
  exact (inv_le_inv₀ (pow_pos hL _) (pow_pos (hM i) _)).mpr
    (pow_le_pow_left₀ (hM i).le (hML i) _)

/-- Actual slanted tensor weight built from the source profiles. -/
def poissonWeight {m : ℕ} (μ : Fin m → ℝ) (μlast : ℝ) (t : ℤ) : Lattice m → ℂ :=
  fun n => (∏ i,(profile (μ i) (n i):ℂ))*(profile μlast (t-∑ i,n i):ℂ)

theorem poissonWeight_eq_ofReal {m : ℕ} (μ : Fin m → ℝ) (μlast : ℝ) (t : ℤ) (n : Lattice m) :
    poissonWeight μ μlast t n =
      (((∏ i,profile (μ i) (n i))*profile μlast (t-∑ i,n i):ℝ):ℂ) := by
  simp [poissonWeight,Complex.ofReal_prod]

/-- The manuscript's full mixed-difference hypothesis for the actual Poisson
weight, derived from the proved all-order profile theorem. Uniform in every mean,
integer slice, and lattice point; the constant depends only on dimension. -/
theorem poisson_weight_bound (m : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ (μ : Fin m → ℝ) (μlast : ℝ),
      (∀ i,0≤μ i) → 0≤μlast → (∀ i,μ i≤μlast) → ∀ t : ℤ,
      WeightBound (fun i => Real.sqrt (1+μ i)) μ C (poissonWeight μ μlast t) := by
  have hsmall (k : Fin 3) := poissonProfileEstimate_proved k 4
  choose A hA hAb using hsmall
  have hlarge (k : Fin (2*m+1)) := poissonProfileEstimate_proved k 0
  choose B hB hBb using hlarge
  let CA : ℝ := ∑ k : Fin 3,A k
  let CB : ℝ := ∑ k : Fin (2*m+1),B k
  have hCA : 0<CA := Finset.sum_pos (fun k _ => hA k) Finset.univ_nonempty
  have hCB : 0<CB := Finset.sum_pos (fun k _ => hB k) Finset.univ_nonempty
  have hA_le (k : Fin 3) : A k≤CA :=
    Finset.single_le_sum (fun k _ => (hA k).le) (Finset.mem_univ k)
  have hB_le (k : Fin (2*m+1)) : B k≤CB :=
    Finset.single_le_sum (fun k _ => (hB k).le) (Finset.mem_univ k)
  refine ⟨(2:ℝ)^(2*m)*CA^m*CB,by positivity,?_⟩
  intro μ μlast hμ hlast hμlast t ν hν n
  let M := fun i => Real.sqrt (1+μ i)
  let L := Real.sqrt (1+μlast)
  let E := envelope M μ n
  have hM : ∀ i,0<M i := fun i => Real.sqrt_pos.mpr (by linarith [hμ i])
  have hL : 0<L := Real.sqrt_pos.mpr (by linarith)
  have hML : ∀ i,M i≤L := fun i => Real.sqrt_le_sqrt (by linarith [hμlast i])
  have hE : 0≤E := envelope_nonneg _ _ _
  let l := indexWord ν
  have hlen : l.length≤2*m := by
    rw [indexWord_length]
    calc
      _ ≤ ∑ _ : Fin m,2 := Finset.sum_le_sum (fun i _ => hν i)
      _ = _ := by simp; omega
  have hterm (p : List (Fin m) × List (Fin m)) (hp : p∈wordSplits l) :
      ‖(∏ i,((deltaOne^[p.1.count i]) (profile (μ i)) (n i):ℂ)) *
        ((-1:ℂ)^p.2.length * ((deltaOne^[p.2.length]) (profile μlast)
          (t-(∑ i,n i)-(((∑ i,ν i):ℕ):ℤ)):ℂ))‖ ≤
      (CA^m*CB)*(∏ i,(M i^(ν i))⁻¹)*E := by
    have hc (i : Fin m) : p.1.count i+p.2.count i=ν i := by
      have h := wordSplits_counts l p hp i
      simpa only [l,count_indexWord] using h
    have ha (i : Fin m) : p.1.count i≤2 := by have := hc i; have := hν i; omega
    have hlength := wordSplits_lengths l p hp
    have hb : p.2.length≤2*m := by omega
    have hcoord (i : Fin m) : |(deltaOne^[p.1.count i]) (profile (μ i)) (n i)| ≤
        CA*(M i^(p.1.count i))⁻¹*((1+|(n i:ℝ)-μ i|/M i)^4)⁻¹ := by
      let k : Fin 3 := ⟨p.1.count i,by have := ha i; omega⟩
      apply (hAb k (μ i) (hμ i) (n i)).trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (hA_le k) (by positivity)
    have htensor : (∏ i,|(deltaOne^[p.1.count i]) (profile (μ i)) (n i)|) ≤
        CA^m*(∏ i,(M i^(p.1.count i))⁻¹)*E := by
      calc
        _ ≤ ∏ i,CA*(M i^(p.1.count i))⁻¹*((1+|(n i:ℝ)-μ i|/M i)^4)⁻¹ :=
          Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hcoord i)
        _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]; rfl
    have hfinal : |(deltaOne^[p.2.length]) (profile μlast)
          (t-(∑ i,n i)-(((∑ i,ν i):ℕ):ℤ))| ≤ CB*(∏ i,(M i^(p.2.count i))⁻¹) := by
      let k : Fin (2*m+1) := ⟨p.2.length,by omega⟩
      have h := hBb k μlast hlast (t-(∑ i,n i)-(((∑ i,ν i):ℕ):ℤ))
      simp only [pow_zero,inv_one,mul_one] at h
      apply h.trans
      apply mul_le_mul (hB_le k) (last_scale_word_bound M L hM hL hML p.2)
        (by positivity) hCB.le
    simp only [norm_mul,norm_prod,Complex.norm_real,Real.norm_eq_abs,norm_pow,norm_neg,
      norm_one,one_pow,one_mul]
    apply (mul_le_mul htensor hfinal (abs_nonneg _) (by positivity)).trans_eq
    have hsplit := word_scale_split M l p hp
    simp only [l,count_indexWord] at hsplit
    calc
      _ = (CA^m*CB)*((∏ i,(M i^(p.1.count i))⁻¹)*(∏ i,(M i^(p.2.count i))⁻¹))*E := by ring
      _ = _ := by rw [hsplit]
  unfold poissonWeight
  rw [mixedDelta_tensor_slanted_real]
  -- Bound the exact finite expansion term by term.
  have hlist : ∀ (s : List (List (Fin m) × List (Fin m))),
      (∀ p∈s,p∈wordSplits l) →
      ‖(s.map (fun p => (∏ i,((deltaOne^[p.1.count i]) (profile (μ i)) (n i):ℂ)) *
        ((-1:ℂ)^p.2.length * ((deltaOne^[p.2.length]) (profile μlast)
          (t-(∑ i,n i)-(((∑ i,ν i):ℕ):ℤ)):ℂ)))).sum‖ ≤
      (s.length:ℝ)*((CA^m*CB)*(∏ i,(M i^(ν i))⁻¹)*E) := by
    intro s hs
    induction s with
    | nil => simp
    | cons p s ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      apply (norm_add_le _ _).trans
      have hh := hterm p (hs p (by simp))
      have ht := ih (fun q hq => hs q (by simp [hq]))
      nlinarith
  have h := hlist (wordSplits l) (fun _ h => h)
  apply h.trans
  rw [wordSplits_length]
  have hpow : (2:ℝ)^l.length≤(2:ℝ)^(2*m) := pow_le_pow_right₀ (by norm_num) hlen
  push_cast
  change (2:ℝ)^l.length*((CA^m*CB)*(∏ i,(M i^(ν i))⁻¹)*E) ≤ _
  calc
    _ ≤ (2:ℝ)^(2*m)*((CA^m*CB)*(∏ i,(M i^(ν i))⁻¹)*E) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := by ring

end BourgainBasis
