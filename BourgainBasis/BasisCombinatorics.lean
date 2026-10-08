module
public import BourgainBasis.CharacterBounds

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- The source indices 1,...,L represented on Fin L, with L sent to zero modulo L. -/
def positiveFourierIndex (L : ℕ) [NeZero L] : Fin L ≃ ZMod L :=
  (ZMod.finEquiv L).toEquiv.trans (Equiv.addRight 1)

theorem positiveFourierIndex_cast (L : ℕ) [NeZero L] (i : Fin L) :
    positiveFourierIndex L i = ((i.val+1:ℕ):ZMod L) := by
  change (ZMod.finEquiv L) i+1 = _
  rw [Nat.cast_add, Nat.cast_one]
  congr 1
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact (ZMod.natCast_zmod_val (n := n+1) i).symm

/-- Primitive character orthogonality at every modulus, including L=1. -/
theorem standard_character_sum (L : ℕ) [NeZero L] (a : ZMod L) :
    (∑ j : ZMod L, ZMod.stdAddChar (a*j)) = if a=0 then (L:ℂ) else 0 := by
  split_ifs with ha
  · simp [ha]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar L ha)

theorem star_standard_character (L : ℕ) [NeZero L] (a : ZMod L) :
    star (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  exact AddChar.starComp_apply (by simpa only [ZMod.ringChar_zmod_n] using (NeZero.pos L)) a

/-- Orthogonality of the unnormalized positive-sign Fourier rows. -/
theorem standard_character_rows (L : ℕ) [NeZero L] (a b : ZMod L) :
    (∑ j : ZMod L, ZMod.stdAddChar (a*j)*star (ZMod.stdAddChar (b*j))) =
      if a=b then (L:ℂ) else 0 := by
  simp_rw [star_standard_character, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul]
  rw [standard_character_sum]
  simp only [sub_eq_zero]

/-- Exact normalized matrix from the source, with source t,s=1,...,L represented
as t.val+1 and s.val+1. The normalization is L^(-1/2). -/
def sourceFourier (L : ℕ) : Matrix (Fin L) (Fin L) ℂ := fun t s =>
  (Real.sqrt (L:ℝ):ℂ)⁻¹ *
    phase ((((t.val+1:ℕ):ℝ)*((s.val+1:ℕ):ℝ))/(L:ℝ))

theorem sourceFourier_character (L : ℕ) [NeZero L] (t s : Fin L) :
    sourceFourier L t s = (Real.sqrt (L:ℝ):ℂ)⁻¹ *
      ZMod.stdAddChar (positiveFourierIndex L t*positiveFourierIndex L s) := by
  unfold sourceFourier
  congr 1
  rw [positiveFourierIndex_cast, positiveFourierIndex_cast, ← Nat.cast_mul]
  have he := ZMod.stdAddChar_coe (N := L) (((t.val+1)*(s.val+1):ℕ):ℤ)
  push_cast at he
  push_cast
  rw [he]
  unfold phase
  congr 1
  push_cast
  ring

theorem fourier_normalization (L : ℕ) [NeZero L] :
    (Real.sqrt (L:ℝ):ℂ)⁻¹ * star ((Real.sqrt (L:ℝ):ℂ)⁻¹) * (L:ℂ) = 1 := by
  have hLp : (0:ℝ)<L := by exact_mod_cast NeZero.pos L
  have hs : (Real.sqrt (L:ℝ):ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hLp).ne'
  have hsq : (Real.sqrt (L:ℝ):ℂ)^2 = (L:ℂ) := by
    exact_mod_cast Real.sq_sqrt hLp.le
  rw [show star ((Real.sqrt (L:ℝ):ℂ)⁻¹) = (Real.sqrt (L:ℝ):ℂ)⁻¹ by
    change (starRingEnd ℂ) _ = _
    rw [map_inv₀, Complex.conj_ofReal]]
  rw [← hsq]
  field_simp

/-- Exact orthonormality for the source's indexing and normalization. -/
theorem sourceFourier_rows (L : ℕ) [NeZero L] (t u : Fin L) :
    (∑ s, sourceFourier L t s*star (sourceFourier L u s)) = if t=u then 1 else 0 := by
  simp_rw [sourceFourier_character, star_mul']
  have hrearr (s : Fin L) :
      ((Real.sqrt (L:ℝ):ℂ)⁻¹*ZMod.stdAddChar (positiveFourierIndex L t*positiveFourierIndex L s))*
        (star ((Real.sqrt (L:ℝ):ℂ)⁻¹)*star (ZMod.stdAddChar (positiveFourierIndex L u*positiveFourierIndex L s))) =
      ((Real.sqrt (L:ℝ):ℂ)⁻¹*star ((Real.sqrt (L:ℝ):ℂ)⁻¹))*
        (ZMod.stdAddChar (positiveFourierIndex L t*positiveFourierIndex L s)*
          star (ZMod.stdAddChar (positiveFourierIndex L u*positiveFourierIndex L s))) := by ring
  simp_rw [hrearr]
  rw [← Finset.mul_sum]
  have hsum := Fintype.sum_equiv (positiveFourierIndex L)
    (fun s => ZMod.stdAddChar (positiveFourierIndex L t*positiveFourierIndex L s)*
      star (ZMod.stdAddChar (positiveFourierIndex L u*positiveFourierIndex L s)))
    (fun j => ZMod.stdAddChar (positiveFourierIndex L t*j)*
      star (ZMod.stdAddChar (positiveFourierIndex L u*j))) (fun _ => rfl)
  rw [hsum, standard_character_rows]
  simp only [Equiv.apply_eq_iff_eq]
  split_ifs
  · exact fourier_normalization L
  · ring

/-- The concrete source Fourier matrix is unitary. In the basis construction use
L=N+m, which is positive whenever the source dimension parameter m is positive. -/
theorem sourceFourier_unitary (L : ℕ) [NeZero L] :
    sourceFourier L ∈ Matrix.unitaryGroup (Fin L) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext t u
  simpa only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using sourceFourier_rows L t u

/-- Direct specialization to the source's L=N+m, including N=0. -/
theorem sourceFourier_degree_unitary (N m : ℕ) (hm : 0 < m) :
    sourceFourier (N+m) ∈ Matrix.unitaryGroup (Fin (N+m)) ℂ := by
  let : NeZero (N+m) := ⟨by omega⟩
  exact sourceFourier_unitary (N+m)

/-- The exact homogeneous-multi-index cardinality from the source. This counting
lemma does not yet identify the prescribed cumulative-sum stars-and-bars map. -/
theorem homogeneous_index_card (N m : ℕ) :
    Nat.card {α : Fin (m+1) → ℕ // ∑ i, α i = N} = (N+m).choose m := by
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin (m+1)) N)]
  rw [Nat.card_eq_fintype_card, Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  rw [show m+1+N-1=N+m by omega]
  have hh := Nat.choose_symm (n := N+m) (k := N) (by omega)
  simpa using hh.symm

end BourgainBasis
