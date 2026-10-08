module
public import BourgainBasis.Calibration

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

def decay4 (M x : ℝ) : ℝ := ((1 + |x| / M)^4)⁻¹

theorem decay4_nonneg (M x : ℝ) : 0 ≤ decay4 M x := by unfold decay4; positivity

/-- The factor 16 is uniform in the positive scale M. -/
theorem decay4_compare {M : ℝ} (hM : 0 < M) (t h : ℝ) (hh : |h| ≤ 2 * |t|) :
    decay4 M t ≤ 16 * decay4 M h := by
  have ha : 0 < 1 + |t| / M := by positivity
  have hb : 0 < 1 + |h| / M := by positivity
  have hc : 1 + |h| / M ≤ 2 * (1 + |t| / M) := by
    have hx := div_le_div_of_nonneg_right hh hM.le
    rw [mul_div_assoc] at hx
    linarith
  have hp := pow_le_pow_left₀ hb.le hc 4
  norm_num [mul_pow] at hp
  unfold decay4
  rw [← one_div, ← one_div, mul_one_div]
  apply (div_le_div_iff₀ (pow_pos ha 4) (pow_pos hb 4)).mpr
  linarith

/-- The pointwise convolution inequality used in the squared-sum correlation.
It is valid for all real centers, including noninteger centers. -/
theorem decay4_correlation_pointwise {M : ℝ} (hM : 0 < M) (x a b : ℝ) :
    decay4 M (x-a) * decay4 M (x-b) ≤
      16 * decay4 M (a-b) * (decay4 M (x-a) + decay4 M (x-b)) := by
  have ht : |a-b| ≤ |x-a| + |x-b| := by
    simpa [abs_sub_comm a x] using abs_sub_le a x b
  have hA := decay4_nonneg M (x-a)
  have hB := decay4_nonneg M (x-b)
  have hH := decay4_nonneg M (a-b)
  rcases le_total |x-a| |x-b| with h | h
  · have hb := decay4_compare hM (x-b) (a-b) (by linarith)
    nlinarith [mul_nonneg hH hB, mul_le_mul_of_nonneg_left hb hA]
  · have ha := decay4_compare hM (x-a) (a-b) (by linarith)
    nlinarith [mul_nonneg hH hA, mul_le_mul_of_nonneg_right ha hB]

/-- Finite lattice correlation estimate, with no summability premise. -/
theorem decay4_correlation_finset {M : ℝ} (hM : 0 < M) (a b : ℝ) (s : Finset ℤ) :
    (∑ n ∈ s, decay4 M ((n : ℝ)-a) * decay4 M ((n : ℝ)-b)) ≤
      16 * decay4 M (a-b) *
        ((∑ n ∈ s, decay4 M ((n : ℝ)-a)) + (∑ n ∈ s, decay4 M ((n : ℝ)-b))) := by
  calc
    _ ≤ ∑ n ∈ s, 16 * decay4 M (a-b) *
        (decay4 M ((n : ℝ)-a) + decay4 M ((n : ℝ)-b)) :=
      Finset.sum_le_sum (fun n _ => decay4_correlation_pointwise hM n a b)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]

/-- Summability for every real center and positive scale; the exceptional point
where the comparison p-series is zero is removed using a finite-set argument. -/
theorem decay4_summable {M : ℝ} (hM : 0 < M) (c : ℝ) :
    Summable (fun n : ℤ => decay4 M ((n : ℝ)-c)) := by
  have hg : Summable (fun n : ℤ => M^4 / |(n : ℝ)-c|^4) := by
    have hh := ((Real.summable_one_div_int_add_rpow (-c) 4).mpr (by norm_num)).mul_left (M^4)
    simpa [Real.rpow_natCast, sub_eq_add_neg, div_eq_mul_inv] using hh
  apply hg.of_norm_bounded_eventually
  have hfin : Set.Finite {n : ℤ | (n : ℝ) = c} := by
    apply Set.Subsingleton.finite
    intro a ha b hb
    exact_mod_cast (ha.trans hb.symm)
  have hev : ∀ᶠ n : ℤ in Filter.cofinite, (n : ℝ) ≠ c :=
    Filter.eventually_cofinite.mpr (by simpa using hfin)
  filter_upwards [hev] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (decay4_nonneg _ _)]
  have ht : 0 < |(n : ℝ)-c| := abs_pos.mpr (sub_ne_zero.mpr hn)
  have he : 1 + |(n : ℝ)-c| / M = (M + |(n : ℝ)-c|) / M := by field_simp
  unfold decay4
  rw [he, div_pow, inv_div]
  gcongr
  linarith

/-- The infinite correlation is absolutely summable and has separation decay.
The remaining lattice-mass estimate is explicitly visible as the two marginal sums. -/
theorem decay4_correlation_tsum {M : ℝ} (hM : 0 < M) (a b : ℝ) :
    Summable (fun n : ℤ => decay4 M ((n : ℝ)-a) * decay4 M ((n : ℝ)-b)) ∧
    (∑' n : ℤ, decay4 M ((n : ℝ)-a) * decay4 M ((n : ℝ)-b)) ≤
      16 * decay4 M (a-b) *
        ((∑' n : ℤ, decay4 M ((n : ℝ)-a)) + (∑' n : ℤ, decay4 M ((n : ℝ)-b))) := by
  have ha := decay4_summable hM a
  have hb := decay4_summable hM b
  have hmajor := (ha.add hb).mul_left (16 * decay4 M (a-b))
  have hprod : Summable (fun n : ℤ => decay4 M ((n : ℝ)-a) * decay4 M ((n : ℝ)-b)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (decay4_nonneg _ _) (decay4_nonneg _ _))
      (fun n => decay4_correlation_pointwise hM n a b) hmajor
  refine ⟨hprod, ?_⟩
  calc
    _ ≤ ∑' n : ℤ, 16 * decay4 M (a-b) *
        (decay4 M ((n : ℝ)-a) + decay4 M ((n : ℝ)-b)) :=
      hprod.tsum_le_tsum (fun n => decay4_correlation_pointwise hM n a b) hmajor
    _ = _ := by rw [tsum_mul_left, ha.tsum_add hb]

end BourgainBasis
