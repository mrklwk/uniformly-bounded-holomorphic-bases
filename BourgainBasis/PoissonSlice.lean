module
public import BourgainBasis.PoissonWeight
public import BourgainBasis.StarsBars

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- The first m coordinates of a degree-N multi-index, viewed on the integer lattice. -/
def degreeLattice {m N : ℕ} (α : degreeIndices m N) : Lattice m :=
  fun i => (α.val i.castSucc:ℤ)

theorem degreeLattice_last {m N : ℕ} (α : degreeIndices m N) :
    (α.val (Fin.last m):ℤ) = (N:ℤ)-∑ i,degreeLattice α i := by
  have h := α.property
  rw [Fin.sum_univ_castSucc] at h
  have hz : (∑ i,degreeLattice α i)+(α.val (Fin.last m):ℤ)=N := by
    dsimp only [degreeLattice]
    exact_mod_cast h
  omega

theorem degreeLattice_injective {m N : ℕ} : Function.Injective (@degreeLattice m N) := by
  intro α β h
  apply Subtype.ext
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have ha := degreeLattice_last α
    have hb := degreeLattice_last β
    rw [h] at ha
    exact_mod_cast (show (α.val (Fin.last m):ℤ)=(β.val (Fin.last m):ℤ) by omega)
  · have hh := congrFun h j
    dsimp only [degreeLattice] at hh
    exact_mod_cast hh

/-- Exact range of the first-coordinate projection: the nonnegative simplex. -/
theorem degreeLattice_range {m N : ℕ} (n : Lattice m) :
    n∈Set.range (@degreeLattice m N) ↔ (∀ i,0≤n i) ∧ (∑ i,n i)≤(N:ℤ) := by
  constructor
  · rintro ⟨α,rfl⟩
    refine ⟨fun i => by unfold degreeLattice; positivity,?_⟩
    have h := degreeLattice_last α
    have hn : (0:ℤ)≤α.val (Fin.last m) := by positivity
    omega
  · rintro ⟨hn,hs⟩
    let a : Fin (m+1) → ℕ := Fin.snoc (fun i => (n i).toNat) ((N:ℤ)-∑ i,n i).toNat
    have ha : ∑ i,a i=N := by
      have hz : (∑ i,(a i:ℤ))=(N:ℤ) := by
        rw [Fin.sum_univ_castSucc]
        simp only [a,Fin.snoc_castSucc,Fin.snoc_last,Int.toNat_of_nonneg (by omega : 0≤(N:ℤ)-∑ i,n i)]
        have he : (∑ i,((n i).toNat:ℤ))=∑ i,n i := by
          apply Finset.sum_congr rfl
          intro i _
          exact Int.toNat_of_nonneg (hn i)
        rw [he]
        omega
      exact_mod_cast hz
    refine ⟨⟨a,ha⟩,?_⟩
    funext i
    simp only [degreeLattice,a,Fin.snoc_castSucc]
    exact Int.toNat_of_nonneg (hn i)

/-- The actual zero-extended profile product vanishes off the nonnegative simplex. -/
theorem poissonWeight_zero_off_simplex {m N : ℕ} (μ : Fin m → ℝ) (μlast : ℝ)
    (n : Lattice m) (hn : ¬((∀ i,0≤n i) ∧ (∑ i,n i)≤(N:ℤ))) :
    poissonWeight μ μlast N n=0 := by
  by_cases hc : ∀ i,0≤n i
  · have hsum : ¬(∑ i,n i)≤(N:ℤ) := fun h => hn ⟨hc,h⟩
    have hs : (N:ℤ)-∑ i,n i<0 := by omega
    have hz : profile μlast ((N:ℤ)-∑ i,n i)=0 := by
      rw [profile,ite_eq_right (by omega : ¬0≤(N:ℤ)-∑ i,n i)]
    simp [poissonWeight,hz]
  · push Not at hc
    obtain ⟨i,hi⟩ := hc
    have hprod : (∏ j,(profile (μ j) (n j):ℂ))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [profile,show ¬0≤n i by omega]
    simp [poissonWeight,hprod]

/-- Exact infinite-to-finite bridge, valid with any additional lattice factor.
No finite-support hypothesis is assumed: support comes from the profiles. -/
theorem poissonWeight_tsum_slice {m N : ℕ} (μ : Fin m → ℝ) (μlast : ℝ)
    (f : Lattice m → ℂ) :
    (∑' n,poissonWeight μ μlast N n*f n) =
      ∑ α : degreeIndices m N,poissonWeight μ μlast N (degreeLattice α)*f (degreeLattice α) := by
  have hs : Function.support (fun n => poissonWeight μ μlast N n*f n) ⊆
      Set.range (@degreeLattice m N) := by
    intro n hn
    apply (degreeLattice_range n).mpr
    by_contra h
    have hz := poissonWeight_zero_off_simplex μ μlast n h
    simp [Function.mem_support,hz] at hn
  have h := degreeLattice_injective.tsum_eq hs
  rw [tsum_fintype] at h
  exact h.symm

/-- At the projected lattice point the slanted product is the complete product
of all m+1 natural-index profiles. -/
theorem poissonWeight_degree_product {m N : ℕ} (μ : Fin (m+1) → ℝ)
    (α : degreeIndices m N) :
    poissonWeight (fun i => μ i.castSucc) (μ (Fin.last m)) N (degreeLattice α) =
      ((∏ i,profileNat (μ i) (α.val i):ℝ):ℂ) := by
  rw [poissonWeight_eq_ofReal,←degreeLattice_last α]
  simp only [degreeLattice,profile_nat]
  rw [Fin.prod_univ_castSucc]

/-- The product of normalized profiles factors through the exact Poisson
conditioning identity, including zero coordinates and zero degree. -/
theorem profile_product_conditioning {m N : ℕ} (p : Fin (m+1) → ℝ)
    (hp₀ : ∀ i,0≤p i) (hp : ∑ i,p i=1) (α : degreeIndices m N) :
    (∏ i,profileNat ((N:ℝ)*p i) (α.val i)) =
      Real.sqrt (∏ i,Real.sqrt (1+(N:ℝ)*p i)) * Real.sqrt (poisson (N:ℝ) N) *
        Real.sqrt ((N.factorial:ℝ)/(∏ i,(α.val i).factorial:ℝ) * ∏ i,(p i)^(α.val i)) := by
  have hμ (i) : 0≤(N:ℝ)*p i := mul_nonneg (Nat.cast_nonneg _) (hp₀ i)
  have hpP : 0≤poisson (N:ℝ) N := poisson_nonneg (Nat.cast_nonneg _) N
  simp only [profileNat,Finset.prod_mul_distrib]
  rw [←Real.sqrt_prod _ (fun i _ => Real.sqrt_nonneg _),
    ←Real.sqrt_prod _ (fun i _ => poisson_nonneg (hμ i) _),
    poisson_multinomial_product p α.val N hp α.property,Real.sqrt_mul hpP]
  ring

/-- Absolute convergence comes from the proved finite simplex support, even
when the additional factor has no boundedness hypothesis. -/
theorem poissonWeight_slice_summable {m N : ℕ} (μ : Fin m → ℝ) (μlast : ℝ)
    (f : Lattice m → ℂ) : Summable (fun n => ‖poissonWeight μ μlast N n*f n‖) := by
  apply summable_of_hasFiniteSupport
  apply (Set.finite_range (@degreeLattice m N)).subset
  intro n hn
  apply (degreeLattice_range n).mpr
  by_contra h
  have hz := poissonWeight_zero_off_simplex μ μlast n h
  simp [Function.mem_support,hz] at hn

/-- The entire normalized lattice slice is the finite multinomial square-root
sum, with its exact scalar normalization factored out. -/
theorem poissonWeight_tsum_conditioning {m N : ℕ} (p : Fin (m+1) → ℝ)
    (hp₀ : ∀ i,0≤p i) (hp : ∑ i,p i=1) (f : Lattice m → ℂ) :
    (∑' n,poissonWeight (fun i => (N:ℝ)*p i.castSucc)
      ((N:ℝ)*p (Fin.last m)) N n*f n) =
    ((Real.sqrt (∏ i,Real.sqrt (1+(N:ℝ)*p i))*Real.sqrt (poisson (N:ℝ) N):ℝ):ℂ) *
      ∑ α : degreeIndices m N,
        (Real.sqrt ((N.factorial:ℝ)/(∏ i,(α.val i).factorial:ℝ) *
          ∏ i,(p i)^(α.val i)):ℂ)*f (degreeLattice α) := by
  rw [poissonWeight_tsum_slice,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [poissonWeight_degree_product (fun i => (N:ℝ)*p i),
    profile_product_conditioning p hp₀ hp α]
  push_cast
  ring

/-- The conditioning normalization is strictly positive, including N=0 and
zero probabilities, so subsequent division introduces no missing boundary. -/
theorem profile_conditioning_normalization_pos {m N : ℕ} (p : Fin (m+1) → ℝ)
    (hp₀ : ∀ i,0≤p i) :
    0<Real.sqrt (∏ i,Real.sqrt (1+(N:ℝ)*p i))*Real.sqrt (poisson (N:ℝ) N) := by
  have hprod : 0<∏ i,Real.sqrt (1+(N:ℝ)*p i) := by
    apply Finset.prod_pos
    intro i _
    apply Real.sqrt_pos.mpr
    have h := mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) (hp₀ i)
    linarith
  have hπ : 0<poisson (N:ℝ) N :=
    lt_of_lt_of_le (by positivity) (poisson_at_mean_lower N)
  exact mul_pos (Real.sqrt_pos.mpr hprod) (Real.sqrt_pos.mpr hπ)

end BourgainBasis
