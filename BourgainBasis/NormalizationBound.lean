module
public import BourgainBasis.Contracts
public import BourgainBasis.PoissonConditioning

@[expose] public section

noncomputable section
namespace BourgainBasis

/-- The degree-dependent normalization cancels the Fourier-minor scale, leaving
exactly a dimension-only sqrt(m!) factor with the corrected sphere normalization. -/
theorem determinant_normalization_bound (N m : ℕ) (hm : 0 < m) :
    (m.factorial:ℝ) * ((Real.sqrt (N+m:ℝ))^m)⁻¹ *
      Real.sqrt ((N+m).choose m:ℝ) ≤ Real.sqrt (m.factorial:ℝ) := by
  have hL : (0:ℝ) < (N+m:ℕ) := by exact_mod_cast (show 0 < N+m by omega)
  have hF : (0:ℝ) < m.factorial := by positivity
  have hS : 0 < Real.sqrt (N+m:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hL)
  have hchoose := Nat.choose_le_pow_div (α := ℝ) m (N+m)
  have hmul : ((N+m).choose m:ℝ)*(m.factorial:ℝ) ≤ (N+m:ℝ)^m := by
    exact_mod_cast (le_div_iff₀ hF).mp hchoose
  have hsL : (Real.sqrt (N+m:ℝ))^2=(N+m:ℝ) := Real.sq_sqrt (by positivity)
  have hsC : (Real.sqrt ((N+m).choose m:ℝ))^2=((N+m).choose m:ℝ) := Real.sq_sqrt (by positivity)
  have hsF : (Real.sqrt (m.factorial:ℝ))^2=(m.factorial:ℝ) := Real.sq_sqrt hF.le
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [mul_pow, mul_pow, inv_pow, ← pow_mul, Nat.mul_comm m 2, pow_mul, hsL, hsC, hsF]
  rw [← div_eq_mul_inv]
  have hP : 0 < (N+m:ℝ)^m := by positivity
  apply (mul_le_mul_iff_right₀ hP).mp
  field_simp
  nlinarith only [hmul]

/-- Choosing a largest probability bounds the remaining Poisson scale uniformly. -/
theorem largest_probability_scale {m N : ℕ} (p : Fin (m+1) → ℝ)
    (hp : ∑ i,p i=1) (hmax : ∀ i,p i≤p (Fin.last m)) :
    (N:ℝ)+1 ≤ (m+1:ℝ)*(1+(N:ℝ)*p (Fin.last m)) := by
  have hs : (1:ℝ) ≤ (m+1:ℝ)*p (Fin.last m) := by
    calc
      _ = ∑ i,p i := hp.symm
      _ ≤ ∑ _ : Fin (m+1),p (Fin.last m) := Finset.sum_le_sum (fun i _ => hmax i)
      _ = _ := by simp [nsmul_eq_mul]
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hs hN]

/-- The degree contribution in conditioning is absorbed by the largest-coordinate scale. -/
theorem largest_probability_sqrt_ratio {m N : ℕ} (p : Fin (m+1) → ℝ)
    (hp₀ : ∀ i,0≤p i) (hp : ∑ i,p i=1) (hmax : ∀ i,p i≤p (Fin.last m)) :
    Real.sqrt ((N:ℝ)+1) / Real.sqrt (1+(N:ℝ)*p (Fin.last m)) ≤ Real.sqrt (m+1:ℝ) := by
  have hL : 0 < 1+(N:ℝ)*p (Fin.last m) := by
    have := hp₀ (Fin.last m)
    positivity
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hL)).mpr
  rw [←Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt (largest_probability_scale p hp hmax)

/-- No degree dependence remains in the normalization after eliminating a largest coordinate. -/
theorem conditioning_uniform_factor {m N : ℕ} (p : Fin (m+1) → ℝ)
    (hp₀ : ∀ i,0≤p i) (hp : ∑ i,p i=1) (hmax : ∀ i,p i≤p (Fin.last m)) :
    (Real.sqrt (poisson (N:ℝ) N) *
      Real.sqrt (Real.sqrt (1+(N:ℝ)*p (Fin.last m))))⁻¹ ≤
      Real.sqrt (Real.exp 1 * Real.sqrt (m+1:ℝ)) := by
  let L := Real.sqrt (1+(N:ℝ)*p (Fin.last m))
  have hLp : 0 < L := by
    apply Real.sqrt_pos.mpr
    have := hp₀ (Fin.last m)
    positivity
  have hπ : 0 < poisson (N:ℝ) N :=
    lt_of_lt_of_le (by positivity) (poisson_at_mean_lower N)
  have hratio := largest_probability_sqrt_ratio (N := N) p hp₀ hp hmax
  have hlower := poisson_at_mean_lower N
  have hpos : 0 < Real.sqrt ((N:ℝ)+1) := by positivity
  have hmul : Real.exp (-1) ≤ poisson (N:ℝ) N * Real.sqrt ((N:ℝ)+1) :=
    (div_le_iff₀ hpos).mp hlower
  have hratio' : Real.sqrt ((N:ℝ)+1) ≤ Real.sqrt (m+1:ℝ)*L :=
    (div_le_iff₀ hLp).mp hratio
  have hexp : Real.exp 1 * Real.exp (-1) = 1 := by rw [←Real.exp_add]; norm_num
  have hprod : 1 ≤ (Real.exp 1*Real.sqrt (m+1:ℝ))*(poisson (N:ℝ) N*L) := by
    have h := mul_le_mul_of_nonneg_left hratio' hπ.le
    have hh := mul_le_mul_of_nonneg_left (hmul.trans h) (Real.exp_pos 1).le
    rw [hexp] at hh
    nlinarith only [hh]
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [inv_pow,mul_pow,Real.sq_sqrt hπ.le,Real.sq_sqrt hLp.le,
    Real.sq_sqrt (by positivity)]
  exact (inv_le_iff_one_le_mul₀ (mul_pos hπ hLp)).mpr hprod

end BourgainBasis
