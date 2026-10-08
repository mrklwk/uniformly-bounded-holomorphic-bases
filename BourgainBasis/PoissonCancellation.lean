module
public import BourgainBasis.PoissonSlice
public import BourgainBasis.CoupledCancellation
public import BourgainBasis.NormalizationBound

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- Exact agreement of the eliminated phase with the degree-index quadratic. -/
theorem coupledPhase_degreeLattice {m N : ℕ} (ξ : Fin m → ℝ)
    (α : degreeIndices m N) :
    coupledQuadraticPhase N ξ (degreeLattice α) =
      Real.sqrt 2*(∑ i,(α.val i:ℝ)^2)+∑ i,ξ i*(α.val i.castSucc:ℝ) := by
  have hlast : (N:ℝ)-(∑ i : Fin m,(α.val i.castSucc:ℝ))=(α.val (Fin.last m):ℝ) := by
    have h := α.property
    rw [Fin.sum_univ_castSucc] at h
    have hz : (∑ i : Fin m,(α.val i.castSucc:ℝ))+(α.val (Fin.last m):ℝ)=N := by exact_mod_cast h
    linarith
  unfold coupledQuadraticPhase
  simp only [degreeLattice,Int.cast_natCast,hlast]
  rw [Fin.sum_univ_castSucc (fun i => (α.val i:ℝ)^2)]

/-- Finite multinomial quadratic cancellation with exact conditioning
normalization. No cancellation/profile estimate remains as an assumed premise.
The chosen constant depends only on m, uniformly in degree and all probabilities. -/
theorem multinomial_quadratic_cancellation_normalized (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ,0<C ∧ ∀ (N : ℕ) (p : Fin (m+1) → ℝ),
      (∀ i,0≤p i) → (∑ i,p i=1) → (∀ i : Fin m,p i.castSucc≤p (Fin.last m)) →
      ∀ ξ : Fin m → ℝ,
      ‖∑ α : degreeIndices m N,
        (Real.sqrt ((N.factorial:ℝ)/(∏ i,(α.val i).factorial:ℝ) *
          ∏ i,(p i)^(α.val i)):ℂ) *
        phase (Real.sqrt 2*(∑ i,(α.val i:ℝ)^2)+∑ i,ξ i*(α.val i.castSucc:ℝ))‖ ≤
      (C*Real.sqrt (∏ i : Fin m,Real.sqrt (1+(N:ℝ)*p i.castSucc))) /
        (Real.sqrt (∏ i,Real.sqrt (1+(N:ℝ)*p i))*Real.sqrt (poisson (N:ℝ) N)) := by
  obtain ⟨CW,hCW,hweight⟩ := poisson_weight_bound m
  let K := Real.sqrt ((16:ℝ)^m*165888^m*(786432*(m:ℝ)^2)^m)
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K*CW,mul_pos hK hCW,?_⟩
  intro N p hp₀ hp hlast ξ
  let μ := fun i : Fin m => (N:ℝ)*p i.castSucc
  let μlast := (N:ℝ)*p (Fin.last m)
  let M := fun i : Fin m => Real.sqrt (1+μ i)
  let Z := Real.sqrt (∏ i,Real.sqrt (1+(N:ℝ)*p i))*Real.sqrt (poisson (N:ℝ) N)
  have hμ : ∀ i,0≤μ i := fun i => mul_nonneg (Nat.cast_nonneg _) (hp₀ _)
  have hμlast : 0≤μlast := mul_nonneg (Nat.cast_nonneg _) (hp₀ _)
  have hmax : ∀ i,μ i≤μlast := fun i => mul_le_mul_of_nonneg_left (hlast i) (Nat.cast_nonneg _)
  have hM : ∀ i,1≤M i := by
    intro i
    have h := Real.sqrt_le_sqrt (show (1:ℝ)≤1+μ i by linarith [hμ i])
    simpa [M] using h
  have hw := hweight μ μlast hμ hμlast hmax (N:ℤ)
  have hc := (coupled_quadratic_cancellation hm M μ ξ N CW
    (poissonWeight μ μlast N) hM hCW.le hw).2
  have hs := poissonWeight_tsum_conditioning (N:=N) p hp₀ hp (fun n => phase (coupledQuadraticPhase N ξ n))
  simp only [coupledPhase_degreeLattice] at hs
  change (∑' n,poissonWeight μ μlast N n*phase (coupledQuadraticPhase N ξ n)) =
    (Z:ℂ)*_ at hs
  rw [hs,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (profile_conditioning_normalization_pos (N:=N) p hp₀)] at hc
  have hZ : 0<Z := profile_conditioning_normalization_pos (N:=N) p hp₀
  apply (le_div_iff₀ hZ).mpr
  change _ ≤ K*CW*Real.sqrt (∏ i,M i)
  simpa only [Z,K,mul_comm] using hc

/-- Degree-uniform finite multinomial cancellation for an eliminated largest
coordinate. The normalization and all analytic inputs are proved. -/
theorem multinomial_quadratic_cancellation (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ,0<C ∧ ∀ (N : ℕ) (p : Fin (m+1) → ℝ),
      (∀ i,0≤p i) → (∑ i,p i=1) → (∀ i : Fin m,p i.castSucc≤p (Fin.last m)) →
      ∀ ξ : Fin m → ℝ,
      ‖∑ α : degreeIndices m N,
        (Real.sqrt ((N.factorial:ℝ)/(∏ i,(α.val i).factorial:ℝ) *
          ∏ i,(p i)^(α.val i)):ℂ) *
        phase (Real.sqrt 2*(∑ i,(α.val i:ℝ)^2)+∑ i,ξ i*(α.val i.castSucc:ℝ))‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := multinomial_quadratic_cancellation_normalized m hm
  let D := Real.sqrt (Real.exp 1*Real.sqrt (m+1:ℝ))
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro N p hp₀ hp hlast ξ
  have hmax : ∀ i,p i≤p (Fin.last m) := by
    intro i
    exact Fin.lastCases (le_refl _) hlast i
  have hP : 0<∏ i : Fin m,Real.sqrt (1+(N:ℝ)*p i.castSucc) := by
    apply Finset.prod_pos
    intro i _
    apply Real.sqrt_pos.mpr
    have h := mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) (hp₀ i.castSucc)
    linarith
  have hπ : 0<poisson (N:ℝ) N := lt_of_lt_of_le (by positivity) (poisson_at_mean_lower N)
  have hL : 0<Real.sqrt (1+(N:ℝ)*p (Fin.last m)) := by
    apply Real.sqrt_pos.mpr
    have h := mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) (hp₀ (Fin.last m))
    linarith
  apply (hbound N p hp₀ hp hlast ξ).trans
  calc
    _ = C*(Real.sqrt (poisson (N:ℝ) N)*
        Real.sqrt (Real.sqrt (1+(N:ℝ)*p (Fin.last m))))⁻¹ := by
      rw [Fin.prod_univ_castSucc (fun i => Real.sqrt (1+(N:ℝ)*p i)),Real.sqrt_mul hP.le]
      have hsP : Real.sqrt (∏ i : Fin m,Real.sqrt (1+(N:ℝ)*p i.castSucc))≠0 :=
        ne_of_gt (Real.sqrt_pos.mpr hP)
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (conditioning_uniform_factor (N:=N) p hp₀ hp hmax) hC.le

/-- A full linear frequency differs from the eliminated frequency only by a
constant phase, because the total degree is exactly N. -/
theorem degree_linear_frequency_split {m N : ℕ} (θ : Fin (m+1) → ℝ)
    (α : degreeIndices m N) :
    (∑ i,θ i*(α.val i:ℝ)) = θ (Fin.last m)*(N:ℝ) +
      ∑ i : Fin m,(θ i.castSucc-θ (Fin.last m))*(α.val i.castSucc:ℝ) := by
  have hn : (N:ℝ)=(∑ i : Fin m,(α.val i.castSucc:ℝ))+(α.val (Fin.last m):ℝ) := by
    have h := α.property
    rw [Fin.sum_univ_castSucc] at h
    exact_mod_cast h.symm
  rw [Fin.sum_univ_castSucc,hn]
  simp only [sub_mul,Finset.sum_sub_distrib,←Finset.mul_sum]
  ring

/-- Full-coordinate linear frequencies, with the same degree-uniform constant.
Largest-coordinate relabeling is a separate finite permutation step. -/
theorem multinomial_quadratic_cancellation_full_frequency (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ,0<C ∧ ∀ (N : ℕ) (p : Fin (m+1) → ℝ),
      (∀ i,0≤p i) → (∑ i,p i=1) → (∀ i : Fin m,p i.castSucc≤p (Fin.last m)) →
      ∀ θ : Fin (m+1) → ℝ,
      ‖∑ α : degreeIndices m N,
        (Real.sqrt ((N.factorial:ℝ)/(∏ i,(α.val i).factorial:ℝ) *
          ∏ i,(p i)^(α.val i)):ℂ) *
        phase (Real.sqrt 2*(∑ i,(α.val i:ℝ)^2)+∑ i,θ i*(α.val i:ℝ))‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := multinomial_quadratic_cancellation m hm
  refine ⟨C,hC,?_⟩
  intro N p hp₀ hp hlast θ
  let ξ : Fin m → ℝ := fun i => θ i.castSucc-θ (Fin.last m)
  have he :
      (∑ α : degreeIndices m N,
        (Real.sqrt ((N.factorial:ℝ)/(∏ i,(α.val i).factorial:ℝ) * ∏ i,(p i)^(α.val i)):ℂ) *
        phase (Real.sqrt 2*(∑ i,(α.val i:ℝ)^2)+∑ i,θ i*(α.val i:ℝ))) =
      phase (θ (Fin.last m)*(N:ℝ)) *
      (∑ α : degreeIndices m N,
        (Real.sqrt ((N.factorial:ℝ)/(∏ i,(α.val i).factorial:ℝ) * ∏ i,(p i)^(α.val i)):ℂ) *
        phase (Real.sqrt 2*(∑ i,(α.val i:ℝ)^2)+∑ i,ξ i*(α.val i.castSucc:ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    rw [degree_linear_frequency_split]
    have hphase : Real.sqrt 2*(∑ i,(α.val i:ℝ)^2) +
        (θ (Fin.last m)*(N:ℝ)+∑ i : Fin m,(θ i.castSucc-θ (Fin.last m))*(α.val i.castSucc:ℝ)) =
        θ (Fin.last m)*(N:ℝ) +
        (Real.sqrt 2*(∑ i,(α.val i:ℝ)^2)+∑ i,ξ i*(α.val i.castSucc:ℝ)) := by dsimp [ξ]; ring
    rw [hphase,phase_add]
    ring
  rw [he,norm_mul,norm_phase,one_mul]
  exact hbound N p hp₀ hp hlast ξ

end BourgainBasis
