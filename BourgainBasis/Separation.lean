module
public import BourgainBasis.Calibration

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- The arithmetic input, with an explicit universal constant and no Diophantine
hypothesis. The norm is the distance to the nearest integer on the unit circle. -/
theorem sqrt_two_badly_approximable (q : ℤ) (hq : q ≠ 0) :
    1 / (4 * |(q : ℝ)|) ≤ ‖((q : ℝ) * Real.sqrt 2 : UnitAddCircle)‖ := by
  let p : ℤ := round ((q : ℝ) * Real.sqrt 2)
  have hq₁ : (1 : ℝ) ≤ |(q : ℝ)| := by
    exact_mod_cast (show (1 : ℤ) ≤ |q| by have := abs_pos.mpr hq; omega)
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs₀ := Real.sqrt_nonneg (2 : ℝ)
  have hs₁ : Real.sqrt 2 ≤ 3 / 2 := by nlinarith
  have hirr := irrational_sqrt_two.intCast_mul hq
  have hn : p ^ 2 - 2 * q ^ 2 ≠ 0 := by
    intro he
    have he' : (p : ℝ)^2 - 2 * (q : ℝ)^2 = 0 := by exact_mod_cast he
    have hz : ((q : ℝ) * Real.sqrt 2 - p) * ((q : ℝ) * Real.sqrt 2 + p) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hz with h | h
    · exact hirr.ne_int p (by linarith)
    · exact hirr.ne_int (-p) (by push_cast; linarith)
  have hint : (1 : ℝ) ≤ |(p : ℝ)^2 - 2 * (q : ℝ)^2| := by
    exact_mod_cast (show (1 : ℤ) ≤ |p ^ 2 - 2 * q ^ 2| by
      have := abs_pos.mpr hn; omega)
  have hnear : |(q : ℝ) * Real.sqrt 2 - p| ≤ 1 / 2 := abs_sub_round _
  have hp : |(p : ℝ)| ≤ |(q : ℝ)| * Real.sqrt 2 + 1 / 2 := by
    have ht := abs_add_le ((p : ℝ) - (q : ℝ) * Real.sqrt 2)
      ((q : ℝ) * Real.sqrt 2)
    rw [sub_add_cancel, abs_mul, abs_of_nonneg hs₀, abs_sub_comm] at ht
    linarith
  have hplus : |(q : ℝ) * Real.sqrt 2 + p| ≤ 4 * |(q : ℝ)| := by
    have ht := abs_add_le ((q : ℝ) * Real.sqrt 2) (p : ℝ)
    rw [abs_mul, abs_of_nonneg hs₀] at ht
    nlinarith [abs_nonneg (q : ℝ)]
  have hprod : 1 ≤ |(q : ℝ) * Real.sqrt 2 - p| *
      |(q : ℝ) * Real.sqrt 2 + p| := by
    rw [← abs_mul]
    have he : ((q : ℝ) * Real.sqrt 2 - p) * ((q : ℝ) * Real.sqrt 2 + p) =
        -((p : ℝ)^2 - 2 * (q : ℝ)^2) := by nlinarith
    rw [he, abs_neg]
    exact hint
  rw [UnitAddCircle.norm_eq]
  change 1 / (4 * |(q : ℝ)|) ≤ |(q : ℝ) * Real.sqrt 2 - p|
  apply (div_le_iff₀ (by positivity : 0 < 4 * |(q : ℝ)|)).mpr
  nlinarith [abs_nonneg ((q : ℝ) * Real.sqrt 2 - p)]

/-- Quantitative energy-to-separation step. This proves the Diophantine conclusion
from elementary coercivity and row bounds; the actual coupled matrix is instantiated
below, rather than assumed to have a separation property. -/
theorem separation_of_energy {m : ℕ} (hm : 0 < m)
    (k q : Fin m → ℤ) (M : Fin m → ℝ) (lam b H : ℝ)
    (hlam : 0 < lam) (hb : 0 < b) (hH : 0 < H)
    (hM : ∀ i, 0 ≤ M i) (hk : ∀ i, |(k i : ℝ)| ≤ M i)
    (hq : ∀ i, |(q i : ℝ)| ≤ b * H)
    (hE : lam * H^2 ≤ ∑ i, (k i : ℝ) * (q i : ℝ)) :
    ∃ i, lam / (4 * (m : ℝ) * b^2) ≤
      M i * ‖((q i : ℝ) * Real.sqrt 2 : UnitAddCircle)‖ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hex : ∃ i, lam * H^2 / m ≤ (k i : ℝ) * (q i : ℝ) := by
    by_contra! hn
    have hh := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty :
      (Finset.univ : Finset (Fin m)).Nonempty) (fun i _ => hn i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    have he : (m : ℝ) * (lam * H^2 / m) = lam * H^2 := by field_simp
    rw [he] at hh
    linarith
  obtain ⟨i, hi⟩ := hex
  have hqi : q i ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero, mul_zero] at hi
    have : 0 < lam * H^2 / (m : ℝ) := by positivity
    linarith
  have ha : (k i : ℝ) * (q i : ℝ) ≤ M i * (b * H) :=
    (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul (hk i) (hq i) (abs_nonneg _) (hM i))
  have hMi : lam * H / ((m : ℝ) * b) ≤ M i := by
    apply (div_le_iff₀ (by positivity : 0 < (m : ℝ) * b)).mpr
    have hh := (div_le_iff₀ hmR).mp (hi.trans ha)
    have hc : (lam * H) * H ≤ (M i * ((m : ℝ) * b)) * H := by nlinarith
    exact (mul_le_mul_iff_left₀ hH).mp (by simpa [mul_comm] using hc)
  have hn : 1 / (4 * b * H) ≤ ‖((q i : ℝ) * Real.sqrt 2 : UnitAddCircle)‖ := by
    apply le_trans _ (sqrt_two_badly_approximable (q i) hqi)
    apply one_div_le_one_div_of_le (by positivity : 0 < 4 * |(q i : ℝ)|)
    nlinarith [hq i]
  refine ⟨i, ?_⟩
  calc
    lam / (4 * (m : ℝ) * b^2) =
        (lam * H / ((m : ℝ) * b)) * (1 / (4 * b * H)) := by field_simp
    _ ≤ _ := mul_le_mul hMi hn (by positivity) (hM i)

/-- Exactly `2 (I + 11ᵀ) k`, the frequency difference in the multinomial proof. -/
def coupledFrequency {m : ℕ} (k : Fin m → ℤ) (i : Fin m) : ℤ :=
  2 * (k i + ∑ j, k j)

/-- Anisotropic separation for the actual coupled quadratic form in the paper.
There is no assumed cancellation, separation, or coercivity premise. -/
theorem coupled_anisotropic_separation {m : ℕ} (hm : 0 < m)
    (k : Fin m → ℤ) (hk0 : k ≠ 0) (M : Fin m → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hk : ∀ i, |(k i : ℝ)| ≤ M i) :
    ∃ i, 1 / (32 * (m : ℝ)^2) ≤
      M i * ‖((coupledFrequency k i : ℝ) * Real.sqrt 2 : UnitAddCircle)‖ := by
  let H : ℝ := ∑ i, |(k i : ℝ)|
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsingle : ∀ i, |(k i : ℝ)| ≤ H := fun i =>
    Finset.single_le_sum (fun j _ => abs_nonneg (k j : ℝ)) (Finset.mem_univ i)
  have hH : 0 < H := by
    have hex : ∃ i, k i ≠ 0 := by
      by_contra! hn
      apply hk0
      funext i
      exact hn i
    obtain ⟨i, hi⟩ := hex
    have hiR : (k i : ℝ) ≠ 0 := by exact_mod_cast hi
    exact (abs_pos.mpr hiR).trans_le (hsingle i)
  have hsum : |∑ i, (k i : ℝ)| ≤ H := by
    exact Finset.abs_sum_le_sum_abs _ _
  have hrow : ∀ i, |(coupledFrequency k i : ℝ)| ≤ 4 * H := by
    intro i
    simp only [coupledFrequency, Int.cast_mul, Int.cast_ofNat, Int.cast_add, Int.cast_sum,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have ht := abs_add_le (k i : ℝ) (∑ j, (k j : ℝ))
    nlinarith [hsingle i]
  have hcs : H^2 ≤ (m : ℝ) * ∑ i, (k i : ℝ)^2 := by
    simpa [H, sq_abs] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |(k i : ℝ)|))
  have he : (∑ i, (k i : ℝ) * (coupledFrequency k i : ℝ)) =
      2 * (∑ i, (k i : ℝ)^2) + 2 * (∑ i, (k i : ℝ))^2 := by
    simp only [coupledFrequency, Int.cast_mul, Int.cast_ofNat, Int.cast_add, Int.cast_sum]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    simp_rw [show ∀ a b : ℝ, a * (2 * b) = 2 * (a * b) by intros; ring]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  have hE : (2 / (m : ℝ)) * H^2 ≤ ∑ i, (k i : ℝ) * (coupledFrequency k i : ℝ) := by
    rw [he]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hmR).mpr
    nlinarith [mul_nonneg (le_of_lt hmR) (sq_nonneg (∑ i, (k i : ℝ)))]
  obtain ⟨i, hi⟩ := separation_of_energy hm k (coupledFrequency k) M (2 / m) 4 H
    (by positivity) (by norm_num) hH hM hk hrow hE
  refine ⟨i, ?_⟩
  convert hi using 1
  field_simp
  ring

theorem coupledFrequency_sub {m : ℕ} (h h' : Fin m → ℤ) (i : Fin m) :
    coupledFrequency (h - h') i = coupledFrequency h i - coupledFrequency h' i := by
  simp only [coupledFrequency, Pi.sub_apply, Finset.sum_sub_distrib]
  ring

/-- Two points in any translated anisotropic box. The only geometric input is the
coordinate difference bound; the constant is independent of its location and scales. -/
theorem coupled_box_separation {m : ℕ} (hm : 0 < m) (h h' : Fin m → ℤ)
    (hne : h ≠ h') (M : Fin m → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hbox : ∀ i, |((h i - h' i : ℤ) : ℝ)| ≤ M i) :
    ∃ i, 1 / (32 * (m : ℝ)^2) ≤ M i *
      ‖(((coupledFrequency h i - coupledFrequency h' i : ℤ) : ℝ) *
        Real.sqrt 2 : UnitAddCircle)‖ := by
  simpa only [coupledFrequency_sub] using
    coupled_anisotropic_separation hm (h - h') (sub_ne_zero.mpr hne) M hM hbox

end BourgainBasis
