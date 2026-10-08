module
public import BourgainBasis.Contracts

@[expose] public section

noncomputable section
namespace BourgainBasis

/-- Finite sums retain absolute convergence and a uniform ℓ¹ bound. -/
theorem list_sum_norm_bound {α β : Type*} (l : List α) (f : α → β → ℂ) (B : ℝ)
    (hb : ∀ a ∈ l, Summable (fun n => ‖f a n‖) ∧ (∑' n, ‖f a n‖) ≤ B) :
    Summable (fun n => ‖(l.map (fun a => f a n)).sum‖) ∧
    (∑' n, ‖(l.map (fun a => f a n)).sum‖) ≤ (l.length:ℝ)*B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hb a (by simp)
    have ht := ih (fun b h => hb b (by simp [h]))
    have hd := ha.1.add ht.1
    have hle (n : β) : ‖f a n+(l.map (fun a => f a n)).sum‖ ≤
        ‖f a n‖+‖(l.map (fun a => f a n)).sum‖ := norm_add_le _ _
    have hs := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hd
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    refine ⟨hs, ?_⟩
    calc
      _ ≤ ∑' n, (‖f a n‖+‖(l.map (fun a => f a n)).sum‖) := hs.tsum_le_tsum hle hd
      _ = (∑' n, ‖f a n‖)+(∑' n, ‖(l.map (fun a => f a n)).sum‖) := ha.1.tsum_add ht.1
      _ ≤ B+(l.length:ℝ)*B := add_le_add ha.2 ht.2
      _ = _ := by ring

end BourgainBasis
