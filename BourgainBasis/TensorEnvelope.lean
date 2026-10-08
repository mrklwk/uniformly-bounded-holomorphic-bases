module
public import BourgainBasis.LatticeMass

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- Absolute summability and factorization of a nonnegative finite tensor product,
including the empty product in dimension zero. -/
theorem tensor_hasSum (m : ℕ) (f : Fin m → ℤ → ℝ)
    (hn : ∀ i n, 0 ≤ f i n) (hs : ∀ i, Summable (f i)) :
    HasSum (fun n : Fin m → ℤ => ∏ i, f i (n i)) (∏ i, ∑' k, f i k) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have ht := ih (fun i => f i.succ) (fun i n => hn i.succ n) (fun i => hs i.succ)
    let g : (Fin m → ℤ) → ℝ := fun n => ∏ i, f i.succ (n i)
    have hgs : Summable g := ht.summable
    have ht₀ (n : Fin m → ℤ) : 0 ≤ ∏ i, f i.succ (n i) :=
      Finset.prod_nonneg (fun i _ => hn _ _)
    have hprod : Summable (fun p : ℤ × (Fin m → ℤ) => f 0 p.1 * g p.2) := by
      apply (summable_prod_of_nonneg (fun p => mul_nonneg (hn 0 p.1) (ht₀ p.2))).mpr
      constructor
      · intro x
        exact hgs.mul_left (f 0 x)
      · simpa only [tsum_mul_left] using (hs 0).mul_right (∑' y, g y)
    have hts : (∑' p : ℤ × (Fin m → ℤ), f 0 p.1 * g p.2) =
        (∑' k, f 0 k) * ∏ i : Fin m, ∑' k, f i.succ k := by
      rw [hprod.tsum_prod]
      simp_rw [tsum_mul_left]
      rw [tsum_mul_right]
      rw [show (∑' n, g n) = ∏ i : Fin m, ∑' k, f i.succ k from ht.tsum_eq]
    have hp := hprod.hasSum
    rw [hts] at hp
    apply (Fin.consEquiv (fun _ : Fin (m+1) => ℤ)).hasSum_iff.mp
    simpa [Function.comp_def, Fin.consEquiv, Fin.prod_univ_succ] using hp

/-- The full anisotropic envelope is summable in every finite dimension. -/
theorem envelope_hasSum {m : ℕ} (M c : Fin m → ℝ) (hM : ∀ i, 0 < M i) :
    HasSum (envelope M c) (∏ i, ∑' n : ℤ, decay4 (M i) ((n : ℝ)-c i)) := by
  exact tensor_hasSum m (fun i n => decay4 (M i) ((n : ℝ)-c i))
    (fun i n => decay4_nonneg _ _) (fun i => decay4_summable (hM i) (c i))

/-- Dimension-dependent constant only; every center and coordinate scale is uniform. -/
theorem envelope_mass {m : ℕ} (M c : Fin m → ℝ) (hM : ∀ i, 1 ≤ M i) :
    (∑' n : Lattice m, envelope M c n) ≤ 64^m * ∏ i, M i := by
  rw [(envelope_hasSum M c (fun i => by linarith [hM i])).tsum_eq]
  calc
    _ ≤ ∏ i, 64*M i := Finset.prod_le_prod₀
      (fun i _ => tsum_nonneg (fun n => decay4_nonneg _ _))
      (fun i _ => decay4_lattice_mass (hM i) (c i))
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

theorem envelope_correlation_hasSum {m : ℕ} (M a b : Fin m → ℝ)
    (hM : ∀ i, 0 < M i) :
    HasSum (fun n : Lattice m => envelope M a n * envelope M b n)
      (∏ i, ∑' n : ℤ, decay4 (M i) ((n : ℝ)-a i) * decay4 (M i) ((n : ℝ)-b i)) := by
  have h := tensor_hasSum m
    (fun i n => decay4 (M i) ((n : ℝ)-a i) * decay4 (M i) ((n : ℝ)-b i))
    (fun i n => mul_nonneg (decay4_nonneg _ _) (decay4_nonneg _ _))
    (fun i => (decay4_correlation_tsum (hM i) (a i) (b i)).1)
  simpa only [envelope, decay4, Finset.prod_mul_distrib] using h

/-- Full anisotropic convolution: no common-scale or bounded-eccentricity assumption. -/
theorem envelope_convolution_bound {m : ℕ} (M a b : Fin m → ℝ)
    (hM : ∀ i, 1 ≤ M i) :
    (∑' n : Lattice m, envelope M a n * envelope M b n) ≤
      2048^m * (∏ i, M i) * ∏ i, decay4 (M i) (a i-b i) := by
  rw [(envelope_correlation_hasSum M a b (fun i => by linarith [hM i])).tsum_eq]
  calc
    _ ≤ ∏ i, 2048*M i*decay4 (M i) (a i-b i) := Finset.prod_le_prod₀
      (fun i _ => tsum_nonneg (fun n => mul_nonneg (decay4_nonneg _ _) (decay4_nonneg _ _)))
      (fun i _ => decay4_convolution_bound (hM i) (a i) (b i))
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]

theorem mixedDelta_zero {m : ℕ} (w : Lattice m → ℂ) :
    mixedDelta (fun _ => 0) w = w := by
  have h (k : ℕ) : List.foldr (fun f g => f ∘ g) id
      (List.replicate k (id : (Lattice m → ℂ) → (Lattice m → ℂ))) = id := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, ih]
  simpa [mixedDelta, List.ofFn_const] using congrFun (h m) w

/-- Actual absolute convergence derived from the source's weight hypotheses. -/
theorem weight_norm_summable {m : ℕ} (M c : Fin m → ℝ) (C₀ : ℝ)
    (w : Lattice m → ℂ) (hM : ∀ i, 1 ≤ M i) (hw : WeightBound M c C₀ w) :
    Summable (fun n => ‖w n‖) := by
  have he := (envelope_hasSum M c (fun i => by linarith [hM i])).summable.mul_left C₀
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ he
  intro n
  have h := hw (fun _ => 0) (by simp) n
  simpa only [mixedDelta_zero, pow_zero, inv_one, Finset.prod_const_one, mul_one] using h

theorem norm_phase (t : ℝ) : ‖phase t‖ = 1 := by
  simp [phase, Complex.norm_exp]

/-- In particular the quadratic sum in the target is genuinely absolutely convergent,
for any real phase function, not merely assigned a totalized tsum value. -/
theorem weighted_phase_summable {m : ℕ} (M c : Fin m → ℝ) (C₀ : ℝ)
    (w : Lattice m → ℂ) (hM : ∀ i, 1 ≤ M i) (hw : WeightBound M c C₀ w)
    (q : Lattice m → ℝ) : Summable (fun n => w n * phase (q n)) := by
  apply Summable.of_norm
  simpa only [norm_mul, norm_phase, mul_one] using weight_norm_summable M c C₀ w hM hw

end BourgainBasis
