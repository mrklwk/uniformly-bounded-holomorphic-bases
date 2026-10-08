module
public import BourgainBasis.TorusPacking

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

theorem nat_tensor_hasSum (m : ℕ) (f : Fin m → ℕ → ℝ)
    (hn : ∀ i n, 0 ≤ f i n) (hs : ∀ i, Summable (f i)) :
    HasSum (fun n : Fin m → ℕ => ∏ i, f i (n i)) (∏ i, ∑' k, f i k) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have ht := ih (fun i => f i.succ) (fun i n => hn i.succ n) (fun i => hs i.succ)
    let g : (Fin m → ℕ) → ℝ := fun n => ∏ i, f i.succ (n i)
    have hgs : Summable g := ht.summable
    have ht₀ (n : Fin m → ℕ) : 0 ≤ ∏ i, f i.succ (n i) :=
      Finset.prod_nonneg (fun i _ => hn _ _)
    have hprod : Summable (fun p : ℕ × (Fin m → ℕ) => f 0 p.1 * g p.2) := by
      apply (summable_prod_of_nonneg (fun p => mul_nonneg (hn 0 p.1) (ht₀ p.2))).mpr
      constructor
      · intro x
        exact hgs.mul_left (f 0 x)
      · simpa only [tsum_mul_left] using (hs 0).mul_right (∑' y, g y)
    have hts : (∑' p : ℕ × (Fin m → ℕ), f 0 p.1 * g p.2) =
        (∑' k, f 0 k) * ∏ i : Fin m, ∑' k, f i.succ k := by
      rw [hprod.tsum_prod]
      simp_rw [tsum_mul_left]
      rw [tsum_mul_right]
      rw [show (∑' n, g n) = ∏ i : Fin m, ∑' k, f i.succ k from ht.tsum_eq]
    have hp := hprod.hasSum
    rw [hts] at hp
    apply (Fin.consEquiv (fun _ : Fin (m+1) => ℕ)).hasSum_iff.mp
    simpa [Function.comp_def, Fin.consEquiv, Fin.prod_univ_succ] using hp


/-- The total dyadic rectangular-shell mass is exactly 2^m. -/
theorem dyadic_tensor_hasSum (m : ℕ) :
    HasSum (fun k : Fin m → ℕ => ∏ i, (1/2 : ℝ)^(k i)) (2^m) := by
  have hs : HasSum (fun k : ℕ => (1/2 : ℝ)^k) 2 := by
    convert hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1) using 1; norm_num
  simpa only [hs.tsum_eq, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    nat_tensor_hasSum m (fun _ k => (1/2 : ℝ)^k) (fun _ _ => by positivity)
      (fun _ => hs.summable)

/-- A dimension-free scalar bound after one dyadic shell is counted. -/
theorem dyadic_shell_factor (k : ℕ) (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1) :
    ((2^(k+1)+r)/r) / (1+((2:ℝ)^k-1))^2 ≤ (3/r)*(1/2:ℝ)^k := by
  have ht : (0:ℝ) < 2^k := by positivity
  have ht' : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  rw [show 1+((2:ℝ)^k-1) = 2^k by ring, one_div_pow, pow_succ]
  field_simp
  nlinarith

/-- Actual weighted sum on one anisotropic dyadic shell, independent of all Mi. -/
theorem torus_dyadic_shell {m : ℕ} {α : Type*} (s : Finset α)
    (x : α → Fin m → UnitAddCircle) (M : Fin m → ℝ) (hM : ∀ i, 1 ≤ M i)
    (r ρ : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) (hsepRadius : 2*r < ρ)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ i, ρ ≤ M i*‖x a i-x b i‖)
    (k : Fin m → ℕ)
    (hlow : ∀ a ∈ s, ∀ i, (2:ℝ)^(k i) ≤ 1+M i*‖x a i‖)
    (hupp : ∀ a ∈ s, ∀ i, 1+M i*‖x a i‖ < (2:ℝ)^(k i+1)) :
    (∑ a ∈ s, torusKernel M (x a)) ≤ (3/r)^m * ∏ i, (1/2:ℝ)^(k i) := by
  have hh := torus_shell_packing s x M (fun i => (2:ℝ)^(k i)-1)
    (fun i => (2:ℝ)^(k i+1)) hM
    (fun i => sub_nonneg.mpr (one_le_pow₀ (by norm_num))) (fun _ => by positivity)
    r ρ hr hr' hsepRadius hsep
    (fun a ha i => by linarith [hlow a ha i])
    (fun a ha i => by linarith [hupp a ha i])
  refine hh.trans ?_
  calc
    _ ≤ ∏ i, ((3/r)*(1/2:ℝ)^(k i)) := Finset.prod_le_prod₀
      (fun i _ => by positivity)
      (fun i _ => dyadic_shell_factor (k i) r hr (by linarith))
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The full finite torus product-kernel packing estimate. The constant depends
only on dimension and the chosen separation radius, never on the anisotropic scales. -/
theorem torusKernel_packing {m : ℕ} {α : Type*} (s : Finset α)
    (x : α → Fin m → UnitAddCircle) (M : Fin m → ℝ) (hM : ∀ i, 1 ≤ M i)
    (r ρ : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) (hsepRadius : 2*r < ρ)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ i, ρ ≤ M i*‖x a i-x b i‖) :
    (∑ a ∈ s, torusKernel M (x a)) ≤ (6/r)^m := by
  classical
  have hex (a : α) (i : Fin m) : ∃ k : ℕ,
      (2:ℝ)^k ≤ 1+M i*‖x a i‖ ∧ 1+M i*‖x a i‖ < (2:ℝ)^(k+1) := by
    apply exists_nat_pow_near _ (by norm_num)
    have := hM i
    have := norm_nonneg (x a i)
    nlinarith
  choose k hk using hex
  let keys : Finset (Fin m → ℕ) := s.image k
  have he := Finset.sum_fiberwise_of_maps_to
    (s := s) (t := keys) (g := k) (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    (fun a => torusKernel M (x a))
  rw [← he]
  have hbound (j : Fin m → ℕ) :
      (∑ a ∈ s with k a = j, torusKernel M (x a)) ≤
        (3/r)^m * ∏ i, (1/2:ℝ)^(j i) := by
    apply torus_dyadic_shell _ x M hM r ρ hr hr' hsepRadius
      (fun a ha b hb hab => hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab) j
    · intro a ha i
      rw [← (Finset.mem_filter.mp ha).2]
      exact (hk a i).1
    · intro a ha i
      rw [← (Finset.mem_filter.mp ha).2]
      exact (hk a i).2
  calc
    _ ≤ ∑ j ∈ keys, (3/r)^m * ∏ i, (1/2:ℝ)^(j i) :=
      Finset.sum_le_sum (fun j _ => hbound j)
    _ = (3/r)^m * ∑ j ∈ keys, ∏ i, (1/2:ℝ)^(j i) := by rw [Finset.mul_sum]
    _ ≤ (3/r)^m * 2^m := mul_le_mul_of_nonneg_left
      (by
        rw [← (dyadic_tensor_hasSum m).tsum_eq]
        exact Summable.sum_le_tsum keys (fun _ _ => Finset.prod_nonneg (fun _ _ => by positivity))
          (dyadic_tensor_hasSum m).summable) (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

/-- Infinite families have a genuinely convergent kernel sum, with the same bound.
This is derived from finite packing, not a totalized-tsum statement. -/
theorem torusKernel_packing_summable {m : ℕ} {α : Type*}
    (x : α → Fin m → UnitAddCircle) (M : Fin m → ℝ) (hM : ∀ i, 1 ≤ M i)
    (r ρ : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) (hsepRadius : 2*r < ρ)
    (hsep : ∀ a b, a ≠ b → ∃ i, ρ ≤ M i*‖x a i-x b i‖) :
    Summable (fun a => torusKernel M (x a)) ∧
      (∑' a, torusKernel M (x a)) ≤ (6/r)^m := by
  have hn : ∀ a, 0 ≤ torusKernel M (x a) := fun a => torusKernel_nonneg _ _
  have hb (s : Finset α) : (∑ a ∈ s, torusKernel M (x a)) ≤ (6/r)^m :=
    torusKernel_packing s x M hM r ρ hr hr' hsepRadius (fun a _ b _ => hsep a b)
  exact ⟨summable_of_sum_le hn hb, Real.tsum_le_of_sum_le hn hb⟩

/-- Frequencies of the actual coupled quadratic form 2(I+11ᵀ). -/
def coupledTorusPoint {m : ℕ} (h : Lattice m) (i : Fin m) : UnitAddCircle :=
  ((coupledFrequency h i : ℝ)*Real.sqrt 2 : UnitAddCircle)

/-- The complete packing bound for the concrete frequencies in any translated
anisotropic lattice box, with an explicit constant depending only on dimension. -/
theorem coupled_torusKernel_packing {m : ℕ} (hm : 0 < m) (s : Finset (Lattice m))
    (M : Fin m → ℝ) (hM : ∀ i, 1 ≤ M i)
    (hbox : ∀ a ∈ s, ∀ b ∈ s, ∀ i, |((a i-b i : ℤ):ℝ)| ≤ M i) :
    (∑ a ∈ s, torusKernel M (coupledTorusPoint a)) ≤ (768*(m:ℝ)^2)^m := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hr : 0 < 1/(128*(m:ℝ)^2) := by positivity
  have hr' : 1/(128*(m:ℝ)^2) ≤ (1:ℝ)/2 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith
  have hsepRadius : 2*(1/(128*(m:ℝ)^2)) < 1/(32*(m:ℝ)^2) := by
    field_simp
    norm_num
  have hs : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ i,
      1/(32*(m:ℝ)^2) ≤ M i*‖coupledTorusPoint a i-coupledTorusPoint b i‖ := by
    intro a ha b hb hab
    simpa only [coupledTorusPoint, Int.cast_sub, sub_mul, AddCircle.coe_sub] using
      coupled_box_separation hm a b hab M (fun i => le_trans zero_le_one (hM i))
        (hbox a ha b hb)
  have hp := torusKernel_packing s coupledTorusPoint M hM (1/(128*(m:ℝ)^2))
    (1/(32*(m:ℝ)^2)) hr hr' hsepRadius hs
  convert hp using 1
  congr 1
  field_simp
  ring

end BourgainBasis
