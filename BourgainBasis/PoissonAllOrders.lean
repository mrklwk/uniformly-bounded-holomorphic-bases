module
public import BourgainBasis.ReciprocalRootScale

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- Scalar specialization of the existing exact word calculus. -/
theorem wordDelta_scalar_real (l : List (Fin 1)) (f : ℤ → ℝ) (n : Lattice 1) :
    wordDelta l (fun n => (f (n 0):ℂ)) n = ((deltaOne^[l.length]) f (n 0):ℂ) := by
  have hc : l.count 0=l.length := List.count_eq_length.mpr (fun a _ => Subsingleton.elim 0 a)
  have h := wordDelta_tensor l (fun _ x => (f x:ℂ)) n
  simpa [scalarDelta_real_iterate,hc] using h

/-- Exact scalar Leibniz identity with multiplicities, inherited from words. -/
theorem scalar_leibniz (j : ℕ) (f g : ℤ → ℝ) (n : ℤ) :
    (deltaOne^[j]) (fun k => f k*g k) n =
      ((wordSplits (List.replicate j (0:Fin 1))).map (fun p =>
        (deltaOne^[p.1.length]) f n *
          (deltaOne^[p.2.length]) g (n+(p.1.length:ℤ)))).sum := by
  have h := wordDelta_product (List.replicate j (0:Fin 1))
    (fun k : Lattice 1 => (f (k 0):ℂ)) (fun k : Lattice 1 => (g (k 0):ℂ))
    (fun _ => n)
  have hshift (l : List (Fin 1)) : wordShift l 0=(l.length:ℤ) := by
    simpa using sum_wordShift l
  have hleft : (fun k : Lattice 1 => (f (k 0):ℂ)*(g (k 0):ℂ)) =
      (fun k : Lattice 1 => ((f (k 0)*g (k 0):ℝ):ℂ)) := by ext k; simp
  rw [hleft,wordDelta_scalar_real (List.replicate j (0:Fin 1)) (fun x => f x*g x),List.length_replicate] at h
  simp only [wordDelta_scalar_real,Pi.add_apply,hshift] at h
  apply Complex.ofReal_injective
  convert h using 1
  exact (List.sum_map_hom _ _ Complex.ofRealHom).symm.trans (by simp [Function.comp_def])

/-- Translated distance envelopes lose at most a shift-dependent factor. -/
theorem profile_weight_shift {μ : ℝ} (hμ : 0≤μ) (n r : ℕ) :
    1+|(n:ℝ)-μ|/Real.sqrt (1+μ) ≤ ((r:ℝ)+1)*
      (1+|((n+r:ℕ):ℝ)-μ|/Real.sqrt (1+μ)) := by
  let M := Real.sqrt (1+μ)
  have hM : 0<M := Real.sqrt_pos.mpr (by positivity)
  have hM₁ : 1≤M := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ)≤1+μ by linarith)
    simpa [M] using h
  have hd : |(n:ℝ)-μ| ≤ |((n+r:ℕ):ℝ)-μ|+(r:ℝ) := by
    have htri := abs_sub (((n+r:ℕ):ℝ)-μ) (r:ℝ)
    have he : ((n+r:ℕ):ℝ)-μ-(r:ℝ)=(n:ℝ)-μ := by push_cast; ring
    rw [he] at htri
    simpa only [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) r)] using htri
  have hdiv := div_le_div_of_nonneg_right hd hM.le
  have hr : (r:ℝ)/M≤r := div_le_self (Nat.cast_nonneg _) hM₁
  have hnon := mul_nonneg (Nat.cast_nonneg (α:=ℝ) r)
    (div_nonneg (abs_nonneg (((n+r:ℕ):ℝ)-μ)) hM.le)
  change 1+|(n:ℝ)-μ|/M ≤ ((r:ℝ)+1)*(1+|((n+r:ℕ):ℝ)-μ|/M)
  rw [add_div] at hdiv
  nlinarith

theorem profile_weight_shift_inverse {μ : ℝ} (hμ : 0≤μ) (n r P : ℕ) :
    ((1+|((n+r:ℕ):ℝ)-μ|/Real.sqrt (1+μ))^P)⁻¹ ≤
      ((r:ℝ)+1)^P*((1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^P)⁻¹ := by
  have hM : 0<Real.sqrt (1+μ) := Real.sqrt_pos.mpr (by positivity)
  have h := pow_le_pow_left₀ (show 0≤1+|(n:ℝ)-μ|/Real.sqrt (1+μ) by positivity)
    (profile_weight_shift hμ n r) P
  rw [mul_pow] at h
  rw [←one_div,←div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa using h

theorem scalar_list_abs_bound {α : Type*} (l : List α) (f : α → ℝ) (B : ℝ)
    (h : ∀ x∈l,|f x|≤B) : |(l.map f).sum|≤(l.length:ℝ)*B := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ |f x|+|(l.map f).sum| := abs_add_le _ _
      _ ≤ B+(l.length:ℝ)*B := add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))
      _ = _ := by ring

/-- Exact recurrence on every nonnegative integer index. -/
theorem profile_delta_recurrence {μ : ℝ} (hμ : 0≤μ) (n : ℕ) :
    deltaOne (profile μ) (n:ℤ) =
      (Real.sqrt (μ/((n:ℝ)+1))-1)*profile μ (n:ℤ) := by
  rw [deltaOne,show (n:ℤ)+1=((n+1:ℕ):ℤ) by push_cast; ring,profile_nat,profile_nat,
    profileNat_succ hμ]
  ring

/-- Leibniz formula applied to the actual profile recurrence, with each
shifted profile difference at a nonnegative index. -/
theorem profile_difference_leibniz {μ : ℝ} (hμ : 0≤μ) (j n : ℕ) :
    (deltaOne^[j+1]) (profile μ) (n:ℤ) =
      ((wordSplits (List.replicate j (0:Fin 1))).map (fun p =>
        (deltaOne^[p.1.length]) (fun k : ℤ => Real.sqrt (μ/((k:ℝ)+1))-1) (n:ℤ) *
          (deltaOne^[p.2.length]) (profile μ) ((n+p.1.length:ℕ):ℤ))).sum := by
  rw [Function.iterate_succ_apply]
  have he := deltaOne_local_congr (deltaOne (profile μ))
    (fun k : ℤ => (Real.sqrt (μ/((k:ℝ)+1))-1)*profile μ k) j (n:ℤ) (by
      intro r _
      have h := profile_delta_recurrence hμ (n+r)
      simpa only [Nat.cast_add,Int.cast_add,Int.cast_natCast] using h)
  rw [he,scalar_leibniz]
  simp only [Nat.cast_add]

/-- Arbitrary-order profile bounds at all nonnegative indices. Constants are
chosen before the mean and index, and every lower-order input is proved inductively. -/
theorem profile_nonnegative_all_orders (j : ℕ) : ∀ R : ℕ,
    ∃ C : ℝ,0<C ∧ ∀ μ : ℝ,0≤μ → ∀ n : ℕ,
      |(deltaOne^[j]) (profile μ) (n:ℤ)| ≤ C * (Real.sqrt (1+μ)^j)⁻¹ *
        ((1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^R)⁻¹ := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro R
    cases j with
    | zero =>
      refine ⟨globalProfileConstant R,globalProfileConstant_pos R,?_⟩
      intro μ hμ n
      simpa using profile_global_decay hμ (n:ℤ) R
    | succ j =>
      let P := R+(2*j+3)
      have hlow (b : Fin (j+1)) := ih b (by exact b.isLt) P
      choose C hC hCb using hlow
      let B : ℝ := ∑ b : Fin (j+1),C b
      let K : ℝ := ∑ a : Fin (j+1),ratioSymbolConstant a
      let H : ℝ := j+1
      have hB : 0<B := Finset.sum_pos (fun b _ => hC b) Finset.univ_nonempty
      have hK : 0<K := Finset.sum_pos (fun a _ => ratioSymbolConstant_pos a) Finset.univ_nonempty
      have hH : 0<H := by dsimp [H]; positivity
      have hbB (b : Fin (j+1)) : C b≤B :=
        Finset.single_le_sum (fun b _ => (hC b).le) (Finset.mem_univ b)
      have haK (a : Fin (j+1)) : ratioSymbolConstant a≤K :=
        Finset.single_le_sum (fun (a : Fin (j+1)) _ => (ratioSymbolConstant_pos (a:ℕ)).le) (Finset.mem_univ a)
      refine ⟨(2:ℝ)^j*K*B*H^P,by positivity,?_⟩
      intro μ hμ n
      let M := Real.sqrt (1+μ)
      let W := 1+|(n:ℝ)-μ|/M
      have hM : 0<M := Real.sqrt_pos.mpr (by positivity)
      have hW : 0<W := by dsimp [W]; positivity
      have hW₁ : 1≤W := by
        dsimp [W]
        linarith [div_nonneg (abs_nonneg ((n:ℝ)-μ)) hM.le]
      rw [profile_difference_leibniz hμ]
      have hterm (p : List (Fin 1) × List (Fin 1))
          (hp : p∈wordSplits (List.replicate j (0:Fin 1))) :
          |(deltaOne^[p.1.length]) (fun k : ℤ => Real.sqrt (μ/((k:ℝ)+1))-1) (n:ℤ) *
            (deltaOne^[p.2.length]) (profile μ) ((n+p.1.length:ℕ):ℤ)| ≤
          (K*B*H^P)*(M^(j+1))⁻¹*(W^R)⁻¹ := by
        have hl := wordSplits_lengths (List.replicate j (0:Fin 1)) p hp
        simp only [List.length_replicate] at hl
        let a : Fin (j+1) := ⟨p.1.length,by omega⟩
        let b : Fin (j+1) := ⟨p.2.length,by omega⟩
        have hsym : |(deltaOne^[p.1.length]) (fun k : ℤ => Real.sqrt (μ/((k:ℝ)+1))-1) (n:ℤ)| ≤
            K*(M^(p.1.length+1))⁻¹*W^(2*j+3) := by
          apply (poisson_ratio_symbol_bound hμ p.1.length n).trans
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right (haK a) (by positivity)
          · exact pow_le_pow_right₀ hW₁ (by omega)
          · positivity
          · positivity
        have hprof : |(deltaOne^[p.2.length]) (profile μ) ((n+p.1.length:ℕ):ℤ)| ≤
            B*(M^p.2.length)⁻¹*(H^P*(W^P)⁻¹) := by
          apply (hCb b μ hμ (n+p.1.length)).trans
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right (hbB b) (by positivity)
          · apply (profile_weight_shift_inverse hμ n p.1.length P).trans
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply pow_le_pow_left₀ (by positivity)
            dsimp [H]
            exact_mod_cast (show p.1.length+1≤j+1 by omega)
          · positivity
          · positivity
        rw [abs_mul]
        apply (mul_le_mul hsym hprof (abs_nonneg _) (by positivity)).trans_eq
        have hpow : M^(p.1.length+1)*M^p.2.length=M^(j+1) := by
          rw [←pow_add]
          congr 1
          omega
        dsimp only [P]
        rw [pow_add]
        have hm₁ : M^(p.1.length+1)≠0 := by positivity
        have hm₂ : M^p.2.length≠0 := by positivity
        have hwR : W^R≠0 := by positivity
        have hwJ : W^(2*j+3)≠0 := by positivity
        rw [←hpow]
        field_simp
        ring
      have hsum := scalar_list_abs_bound (wordSplits (List.replicate j (0:Fin 1))) _
        ((K*B*H^P)*(M^(j+1))⁻¹*(W^R)⁻¹) hterm
      apply hsum.trans_eq
      rw [wordSplits_length,List.length_replicate]
      push_cast
      change (2:ℝ)^j*((K*B*H^P)*(M^(j+1))⁻¹*(W^R)⁻¹) = _
      ring

end BourgainBasis
