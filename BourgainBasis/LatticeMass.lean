module
public import BourgainBasis.Correlation

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- Telescoping majorant for the fourth-power envelope on the positive half-line. -/
theorem decay4_telescoping_bound {M : ℝ} (hM : 1 ≤ M) (x : ℝ) (hx : 0 ≤ x) :
    decay4 M x ≤ 2 * M^2 * ((M+x)⁻¹ - (M+x+1)⁻¹) := by
  have hM₀ : 0 < M := by linarith
  have ha : 0 < M+x := by positivity
  have hb : 0 < M+x+1 := by positivity
  have hr₀ : 0 ≤ M / (M+x) := by positivity
  have hr₁ : M / (M+x) ≤ 1 := (div_le_one ha).mpr (by linarith)
  have he : decay4 M x = (M / (M+x))^4 := by
    unfold decay4
    rw [abs_of_nonneg hx]
    field_simp
  have hd : (M+x)⁻¹ - (M+x+1)⁻¹ = 1 / ((M+x)*(M+x+1)) := by field_simp; ring
  rw [he, hd]
  calc
    _ ≤ (M / (M+x))^2 := pow_le_pow_of_le_one hr₀ hr₁ (by norm_num)
    _ ≤ _ := by
      rw [div_pow, mul_one_div]
      apply (div_le_div_iff₀ (pow_pos ha 2) (mul_pos ha hb)).mpr
      have hh : M+x+1 ≤ 2*(M+x) := by linarith
      nlinarith [mul_nonneg (sq_nonneg M) (mul_nonneg ha.le (sub_nonneg.mpr hh))]

theorem reciprocal_telescope (M : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, ((M+(n : ℝ))⁻¹ - (M+n+1)⁻¹)) = M⁻¹ - (M+N)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Uniform mass on the nonnegative integers, with explicit scale dependence. -/
theorem decay4_nat_mass {M : ℝ} (hM : 1 ≤ M) :
    (∑' n : ℕ, decay4 M (n : ℝ)) ≤ 2*M := by
  have hM₀ : 0 < M := by linarith
  apply Real.tsum_le_of_sum_range_le (fun n => decay4_nonneg _ _)
  intro N
  calc
    _ ≤ ∑ n ∈ Finset.range N, 2*M^2*((M+(n : ℝ))⁻¹-(M+n+1)⁻¹) :=
      Finset.sum_le_sum (fun n _ => decay4_telescoping_bound hM n (by positivity))
    _ = 2*M^2*(M⁻¹-(M+N)⁻¹) := by rw [← Finset.mul_sum, reciprocal_telescope]
    _ ≤ 2*M^2*M⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : 0 ≤ (M+(N : ℝ))⁻¹ := by positivity
      linarith
    _ = 2*M := by field_simp

/-- Uniform mass on the full integer lattice at center zero. -/
theorem decay4_int_mass {M : ℝ} (hM : 1 ≤ M) :
    (∑' n : ℤ, decay4 M (n : ℝ)) ≤ 4*M := by
  have hM₀ : 0 < M := by linarith
  have hs : Summable (fun n : ℤ => decay4 M (n : ℝ)) := by
    simpa using decay4_summable hM₀ 0
  have heven (x : ℝ) : decay4 M (-x) = decay4 M x := by simp [decay4]
  have hzero : decay4 M 0 = 1 := by simp [decay4]
  have he := tsum_nat_add_neg hs
  simp only [Int.cast_neg, Int.cast_natCast, heven, ← two_mul, tsum_mul_left,
    Int.cast_zero, hzero] at he
  have hb := decay4_nat_mass hM
  linarith

/-- Bounded translations cost only a constant, uniformly in the scale. -/
theorem decay4_shift_bound {M : ℝ} (hM : 0 < M) (x t : ℝ) (ht : |t| ≤ M) :
    decay4 M x ≤ 16 * decay4 M (x+t) := by
  have ha : 0 < 1 + |x|/M := by positivity
  have hb : 0 < 1 + |x+t|/M := by positivity
  have hd : |x+t| ≤ |x|+M := (abs_add_le _ _).trans (by linarith)
  have hc : 1 + |x+t|/M ≤ 2*(1+|x|/M) := by
    have hh := div_le_div_of_nonneg_right hd hM.le
    rw [add_div, div_self hM.ne'] at hh
    have : 0 ≤ |x|/M := by positivity
    linarith
  have hp := pow_le_pow_left₀ hb.le hc 4
  norm_num [mul_pow] at hp
  unfold decay4
  rw [← one_div, ← one_div, mul_one_div]
  apply (div_le_div_iff₀ (pow_pos ha 4) (pow_pos hb 4)).mpr
  linarith

/-- Uniform translated lattice mass. The constant does not depend on the real center. -/
theorem decay4_lattice_mass {M : ℝ} (hM : 1 ≤ M) (c : ℝ) :
    (∑' n : ℤ, decay4 M ((n : ℝ)-c)) ≤ 64*M := by
  have hM₀ : 0 < M := by linarith
  let p : ℤ := round c
  have hshift : |c-(p : ℝ)| ≤ M := (abs_sub_round c).trans (by linarith)
  have hb (n : ℤ) : decay4 M ((n : ℝ)-c) ≤ 16*decay4 M ((n : ℝ)-p) := by
    have h := decay4_shift_bound hM₀ ((n : ℝ)-c) (c-p) hshift
    simpa only [sub_add_sub_cancel] using h
  have hs := decay4_summable hM₀ (p : ℝ)
  have he : (∑' n : ℤ, decay4 M ((n : ℝ)-p)) = ∑' n : ℤ, decay4 M (n : ℝ) := by
    simpa [sub_eq_add_neg] using
      (Equiv.addRight (-p)).tsum_eq (fun n : ℤ => decay4 M (n : ℝ))
  calc
    _ ≤ ∑' n : ℤ, 16*decay4 M ((n : ℝ)-p) :=
      (decay4_summable hM₀ c).tsum_le_tsum hb (hs.mul_left 16)
    _ = 16 * ∑' n : ℤ, decay4 M (n : ℝ) := by rw [tsum_mul_left, he]
    _ ≤ 16*(4*M) := mul_le_mul_of_nonneg_left (decay4_int_mass hM) (by norm_num)
    _ = _ := by ring

/-- The full scalar convolution estimate used in the source, now with no residual
marginal sums or unproved analytic premises. -/
theorem decay4_convolution_bound {M : ℝ} (hM : 1 ≤ M) (a b : ℝ) :
    (∑' n : ℤ, decay4 M ((n : ℝ)-a) * decay4 M ((n : ℝ)-b)) ≤
      2048*M*decay4 M (a-b) := by
  have hM₀ : 0 < M := by linarith
  calc
    _ ≤ 16*decay4 M (a-b)*
        ((∑' n : ℤ, decay4 M ((n : ℝ)-a))+(∑' n : ℤ, decay4 M ((n : ℝ)-b))) :=
      (decay4_correlation_tsum hM₀ a b).2
    _ ≤ 16*decay4 M (a-b)*(64*M+64*M) :=
      mul_le_mul_of_nonneg_left (add_le_add (decay4_lattice_mass hM a)
        (decay4_lattice_mass hM b)) (mul_nonneg (by norm_num) (decay4_nonneg _ _))
    _ = _ := by ring

end BourgainBasis
