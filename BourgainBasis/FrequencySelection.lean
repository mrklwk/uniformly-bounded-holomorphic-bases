module
public import BourgainBasis.Contracts

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- Algebraic low/high-frequency selection, with no division by a possibly zero
character multiplier. The mixed estimates are used independently per coordinate. -/
theorem frequency_selection {m : ℕ} (s B : ℝ) (y z : Fin m → ℝ)
    (hs : 0 ≤ s) (hB : 0 ≤ B) (hy : ∀ i, 0 ≤ y i) (hz : ∀ i, y i ≤ z i)
    (hb : ∀ ν : Fin m → ℕ, (∀ i, ν i ≤ 2) →
      s*(∏ i, z i^(ν i)) ≤ B*(2:ℝ)^(∑ i, ν i)) :
    s ≤ (16:ℝ)^m*B * ∏ i, ((1+y i)^2)⁻¹ := by
  classical
  let ν : Fin m → ℕ := fun i => if 1 ≤ z i then 2 else 0
  have hν (i) : ν i ≤ 2 := by dsimp [ν]; split <;> omega
  have hp (i) : (1+y i)^2 ≤ 4*z i^(ν i) := by
    dsimp [ν]
    split_ifs with hi
    · nlinarith [hy i, hz i, sq_nonneg (z i-y i)]
    · have hzi : z i < 1 := lt_of_not_ge hi
      simp only [pow_zero, mul_one]
      nlinarith [hy i, hz i]
  have he : (2:ℝ)^(∑ i, ν i) ≤ (4:ℝ)^m := by
    have hh : (∑ i, ν i) ≤ 2*m := by
      calc
        _ ≤ ∑ _i : Fin m, 2 := Finset.sum_le_sum (fun i _ => hν i)
        _ = _ := by simp [Nat.mul_comm]
    have he := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hh
    norm_num [pow_mul] at he ⊢
    exact he
  have hprod : s*(∏ i, (1+y i)^2) ≤ (16:ℝ)^m*B := by
    calc
      _ ≤ s*(∏ i, 4*z i^(ν i)) := mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) (fun i _ => hp i)) hs
      _ = (4:ℝ)^m*(s*∏ i, z i^(ν i)) := by simp [Finset.prod_mul_distrib]; ring
      _ ≤ (4:ℝ)^m*(B*(2:ℝ)^(∑ i, ν i)) := mul_le_mul_of_nonneg_left (hb ν hν) (by positivity)
      _ ≤ (4:ℝ)^m*(B*(4:ℝ)^m) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left he hB) (by positivity)
      _ = _ := by rw [← mul_assoc, mul_comm ((4:ℝ)^m) B, mul_assoc, ← mul_pow]; norm_num; ring
  have hpos : 0 < ∏ i, (1+y i)^2 := Finset.prod_pos (fun i _ => by have := hy i; positivity)
  rw [Finset.prod_inv_distrib, ← div_eq_mul_inv]
  exact (le_div_iff₀ hpos).mpr hprod

end BourgainBasis
