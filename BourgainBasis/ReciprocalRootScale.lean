module
public import BourgainBasis.ReciprocalRootDifferences
public import BourgainBasis.PoissonGlobalSecond

@[expose] public section

noncomputable section
namespace BourgainBasis

/-- Uniform geometry relating the local denominator to the Poisson scale.
No central/tail split is needed. -/
theorem poisson_scale_denominator {μ : ℝ} (hμ : 0≤μ) (n : ℕ) :
    Real.sqrt (1+μ) ≤ Real.sqrt ((n:ℝ)+1) *
      (1+|(n:ℝ)-μ|/Real.sqrt (1+μ)) := by
  let M := Real.sqrt (1+μ)
  let s := Real.sqrt ((n:ℝ)+1)
  let D := |(n:ℝ)-μ|
  have hM : 0<M := Real.sqrt_pos.mpr (by positivity)
  have hs : 1≤ s := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ)≤(n:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) n])
    simpa only [Real.sqrt_one] using h
  have hM₂ : M^2=1+μ := Real.sq_sqrt (by positivity)
  have hs₂ : s^2=(n:ℝ)+1 := Real.sq_sqrt (by positivity)
  have hD : 0≤D := abs_nonneg _
  have hgap : M≤ s+D/M := by
    have he : μ-(n:ℝ)≤D := by dsimp [D]; simpa only [neg_sub] using neg_le_abs ((n:ℝ)-μ)
    by_cases h : M≤ s
    · have : 0≤D/M := by positivity
      linarith
    have hm : 0≤ s*(M-s) := mul_nonneg (by linarith) (by linarith)
    have he : s+D/M=(s*M+D)/M := by field_simp
    rw [he]
    apply (le_div_iff₀ hM).mpr
    nlinarith
  change M≤ s*(1+D/M)
  have hprod := mul_nonneg (show 0≤ s-1 by linarith) (show 0≤D/M by positivity)
  nlinarith

/-- Arbitrary positive-order ratio differences have the required symbol gain
M^(-a-1), at the cost of only a polynomial distance factor. -/
theorem reciprocal_root_difference_scaled {μ : ℝ} (hμ : 0≤μ) (a n : ℕ) (ha : 1≤a) :
    |(deltaOne^[a]) (fun k : ℤ => Real.sqrt (μ/((k:ℝ)+1))) (n:ℤ)| ≤
      risingBound (1/2) a * ((Real.sqrt (1+μ))^(a+1))⁻¹ *
        (1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^(2*a+1) := by
  let M := Real.sqrt (1+μ)
  let s := Real.sqrt ((n:ℝ)+1)
  let W := 1+|(n:ℝ)-μ|/M
  have hM : 0<M := Real.sqrt_pos.mpr (by positivity)
  have hs : 0<s := Real.sqrt_pos.mpr (by positivity)
  have hM₁ : 1≤M := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ)≤1+μ by linarith)
    simpa [M] using h
  have hW : 0<W := by dsimp [W]; positivity
  have hroot : Real.sqrt μ≤M := Real.sqrt_le_sqrt (by linarith)
  have hgeom : M≤ s*W := poisson_scale_denominator hμ n
  have hden : ((n:ℝ)+1)^((a:ℝ)+(1/2:ℝ)) = s^(2*a+1) := by
    rw [Real.rpow_add (by positivity),Real.rpow_natCast,←Real.sqrt_eq_rpow]
    change ((n:ℝ)+1)^a*s=s^(2*a+1)
    rw [pow_add,pow_mul,Real.sq_sqrt (by positivity : 0≤(n:ℝ)+1),pow_one]
  have hnum : Real.sqrt μ*M^(a+1) ≤ s^(2*a+1)*W^(2*a+1) := by
    calc
      _ ≤ M*M^(a+1) := mul_le_mul_of_nonneg_right hroot (by positivity)
      _ = M^(a+2) := by rw [pow_succ,pow_succ]; ring
      _ ≤ M^(2*a+1) := pow_le_pow_right₀ hM₁ (by omega)
      _ ≤ (s*W)^(2*a+1) := pow_le_pow_left₀ hM.le hgeom _
      _ = _ := mul_pow _ _ _
  have hfrac : Real.sqrt μ/s^(2*a+1) ≤ W^(2*a+1)/M^(a+1) := by
    apply (div_le_div_iff₀ (pow_pos hs _) (pow_pos hM _)).mpr
    nlinarith
  have h := reciprocal_root_difference_bound_div hμ a n
  rw [hden] at h
  apply h.trans
  change (risingBound (1/2) a*Real.sqrt μ)/s^(2*a+1) ≤
    risingBound (1/2) a*(M^(a+1))⁻¹*W^(2*a+1)
  calc
    _ = risingBound (1/2) a*(Real.sqrt μ/s^(2*a+1)) := by ring
    _ ≤ risingBound (1/2) a*(W^(2*a+1)/M^(a+1)) :=
      mul_le_mul_of_nonneg_left hfrac (risingBound_nonneg (by norm_num) a)
    _ = _ := by ring

/-- Positive-order differences annihilate a subtracted constant. -/
theorem deltaOne_iterate_sub_const_pos (f : ℤ → ℝ) (c : ℝ) (a : ℕ) (ha : 0<a) :
    (deltaOne^[a]) (fun n => f n-c) = (deltaOne^[a]) f := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
  rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
  have he : deltaOne (fun n => f n-c) = deltaOne f := by
    funext n
    simp [deltaOne]
  rw [he]

def ratioSymbolConstant (a : ℕ) : ℝ := if a=0 then 64 else risingBound (1/2) a

theorem ratioSymbolConstant_pos (a : ℕ) : 0<ratioSymbolConstant a := by
  unfold ratioSymbolConstant
  split_ifs
  · norm_num
  · exact risingBound_pos (by norm_num) a

/-- The complete arbitrary-order symbol bound for r−1. This supplies the
M^(-a-1) factor required by induction through Δb=(r−1)b, for every a≥0. -/
theorem poisson_ratio_symbol_bound {μ : ℝ} (hμ : 0≤μ) (a n : ℕ) :
    |(deltaOne^[a]) (fun k : ℤ => Real.sqrt (μ/((k:ℝ)+1))-1) (n:ℤ)| ≤
      ratioSymbolConstant a * ((Real.sqrt (1+μ))^(a+1))⁻¹ *
        (1+|(n:ℝ)-μ|/Real.sqrt (1+μ))^(2*a+3) := by
  by_cases ha : a=0
  · subst a
    simp only [Function.iterate_zero_apply,ratioSymbolConstant,ite_true,zero_add,
      pow_one]
    calc
      _ ≤ |μ/((n:ℝ)+1)-1| := sqrt_sub_one_bound (by positivity)
      _ ≤ _ := by simpa only [div_eq_mul_inv] using global_recurrence_ratio hμ n
  rw [deltaOne_iterate_sub_const_pos _ 1 a (by omega)]
  have h := reciprocal_root_difference_scaled hμ a n (by omega)
  apply h.trans
  simp only [ratioSymbolConstant,ite_eq_right ha]
  have hM : 0<Real.sqrt (1+μ) := Real.sqrt_pos.mpr (by positivity)
  have hW : 1≤1+|(n:ℝ)-μ|/Real.sqrt (1+μ) := by
    linarith [div_nonneg (abs_nonneg ((n:ℝ)-μ)) hM.le]
  apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hW (by omega))
  exact mul_nonneg (risingBound_nonneg (by norm_num) a) (by positivity)

end BourgainBasis
