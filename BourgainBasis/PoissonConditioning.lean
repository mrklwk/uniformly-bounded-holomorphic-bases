module
public import BourgainBasis.PoissonGlobalSecond

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- Exact Poisson conditioning product, with no positivity restriction on the
individual probabilities. Algebraically it holds for arbitrary real p with sum 1,
so in particular includes vanishing coordinates and N=0. -/
theorem poisson_multinomial_product {d : ℕ} (p : Fin d → ℝ) (α : Fin d → ℕ)
    (N : ℕ) (hp : ∑ i, p i = 1) (hα : ∑ i, α i = N) :
    (∏ i, poisson ((N:ℝ)*p i) (α i)) = poisson (N:ℝ) N *
      ((N.factorial:ℝ)/(∏ i, (α i).factorial:ℝ) * ∏ i, (p i)^(α i)) := by
  have he : (∏ i, Real.exp (-((N:ℝ)*p i))) = Real.exp (-(N:ℝ)) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_neg_distrib,←Finset.mul_sum,hp,mul_one]
  have hpow : (∏ i, ((N:ℝ)*p i)^(α i)) = (N:ℝ)^N * ∏ i, (p i)^(α i) := by
    simp only [mul_pow,Finset.prod_mul_distrib]
    rw [Finset.prod_pow_eq_pow_sum,hα]
  have hf : (N.factorial:ℝ)≠0 := by positivity
  simp only [poisson,Finset.prod_div_distrib,Finset.prod_mul_distrib]
  rw [he,hpow]
  field_simp

/-- Natural-parameter conditioning in its probabilistic domain, including
N=0 and coordinates with p_i=0; no conditional event is postulated. -/
theorem poisson_conditioning {d : ℕ} (p : Fin d → ℝ) (α : Fin d → ℕ)
    (N : ℕ) (_hp₀ : ∀ i, 0≤p i) (hp : ∑ i, p i = 1) (hα : ∑ i, α i = N) :
    (∏ i, poisson ((N:ℝ)*p i) (α i)) / poisson (N:ℝ) N =
      (N.factorial:ℝ)/(∏ i, (α i).factorial:ℝ) * ∏ i, (p i)^(α i) := by
  have hpos : 0<poisson (N:ℝ) N := by
    cases N with
    | zero => norm_num [poisson]
    | succ k => unfold poisson; positivity
  rw [poisson_multinomial_product p α N hp hα]
  field_simp

/-- An elementary upper Stirling bound follows from the installed monotone
Stirling sequence. The constant is explicit and uniform for n≥1. -/
theorem log_factorial_upper (n : ℕ) (hn : 0<n) :
    Real.log (n.factorial:ℝ) ≤
      1 + Real.log (n:ℝ)/2 + (n:ℝ)*Real.log (n:ℝ) - n := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have h := Stirling.log_stirlingSeq'_antitone (Nat.zero_le (n-1))
  change Real.log (Stirling.stirlingSeq ((n-1)+1)) ≤ Real.log (Stirling.stirlingSeq (0+1)) at h
  rw [show n-1+1=n by omega,Stirling.log_stirlingSeq_formula,
    Stirling.log_stirlingSeq_formula] at h
  norm_num only [Nat.factorial_one,Nat.cast_one,Real.log_one,mul_one,one_mul,one_div] at h
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (ne_of_gt hnR),
    Real.log_div (ne_of_gt hnR) (by positivity),Real.log_exp,
    Real.log_inv,Real.log_exp] at h
  linarith

/-- The Poisson mass at its integer mean has a uniform inverse-square-root
lower bound, with N=0 included explicitly. -/
theorem poisson_at_mean_lower (N : ℕ) :
    Real.exp (-1) / Real.sqrt ((N:ℝ)+1) ≤ poisson (N:ℝ) N := by
  cases N with
  | zero =>
    norm_num only [Nat.cast_zero,zero_add,Real.sqrt_one,div_one,poisson,neg_zero,
      Real.exp_zero,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one]
    exact Real.exp_le_one_iff.mpr (by norm_num)
  | succ k =>
    let n := k+1
    have hn : 0<n := by dsimp [n]; omega
    have hnR : (0:ℝ)<n := by exact_mod_cast hn
    have hf := log_factorial_upper n hn
    have hl : Real.log (n:ℝ) ≤ Real.log ((n:ℝ)+1) := Real.log_le_log hnR (by linarith)
    change Real.exp (-1)/Real.sqrt ((n:ℝ)+1) ≤ poisson (n:ℝ) n
    apply (Real.log_le_log_iff (by positivity) (by unfold poisson; positivity)).mp
    rw [Real.log_div (by positivity) (by positivity),Real.log_exp,
      Real.log_sqrt (by positivity)]
    unfold poisson
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),Real.log_exp,Real.log_pow]
    linarith

end BourgainBasis
