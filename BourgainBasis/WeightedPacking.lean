module
public import BourgainBasis.TorusKernel
public import BourgainBasis.TensorEnvelope

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- Coordinate box index for the partition into half-open boxes of widths Mi. -/
def scaleBoxIndex {m : ℕ} (M : Fin m → ℝ) (h : Lattice m) : Lattice m :=
  fun i => ⌊(h i : ℝ)/M i⌋

/-- Equal box indices imply exactly the coordinate diameter bound required by
concrete coupled-frequency packing. No bounded-eccentricity assumption is used. -/
theorem scaleBoxIndex_diameter {m : ℕ} (M : Fin m → ℝ) (hM : ∀ i, 0 < M i)
    (a b : Lattice m) (hab : scaleBoxIndex M a = scaleBoxIndex M b) (i : Fin m) :
    |((a i-b i : ℤ):ℝ)| ≤ M i := by
  have hh := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun hab i)
  change |(a i:ℝ)/M i-(b i:ℝ)/M i| < 1 at hh
  rw [← sub_div, abs_div, abs_of_pos (hM i)] at hh
  have hh' := (div_lt_one (hM i)).mp hh
  simpa only [Int.cast_sub] using hh'.le

/-- Within a scale box the fourth-power envelope is bounded by the envelope of
the integer box index, up to the explicit constant 16 in each coordinate. -/
theorem decay4_floor_bound {M : ℝ} (hM : 0 < M) (x : ℝ) :
    decay4 M x ≤ 16*decay4 1 (⌊x/M⌋ : ℝ) := by
  have ht : |(⌊x/M⌋ : ℝ)-x/M| ≤ (1:ℝ) := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
    have hh := Int.lt_floor_add_one (x/M)
    linarith
  have hh := decay4_shift_bound (by norm_num : (0:ℝ)<1) (x/M)
    ((⌊x/M⌋ : ℝ)-x/M) ht
  have he : decay4 M x = decay4 1 (x/M) := by
    simp only [decay4, abs_div, abs_of_pos hM, div_one]
  rw [he]
  simpa only [add_sub_cancel] using hh

theorem envelope_scaleBox_bound {m : ℕ} (M : Fin m → ℝ) (hM : ∀ i, 0 < M i)
    (h : Lattice m) :
    envelope M 0 h ≤ 16^m * envelope (fun _ => 1) 0 (scaleBoxIndex M h) := by
  change (∏ i, decay4 (M i) ((h i:ℝ)-0)) ≤
    16^m * ∏ i, decay4 1 (((scaleBoxIndex M h i):ℝ)-0)
  simp only [sub_zero]
  calc
    _ ≤ ∏ i, 16*decay4 1 ((scaleBoxIndex M h i):ℝ) :=
      Finset.prod_le_prod₀ (fun i _ => decay4_nonneg _ _)
        (fun i _ => decay4_floor_bound (hM i) (h i))
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- Complete weighted packing on every finite lattice set. The bound is independent
of the scale vector and uses the actual coupled frequencies, not a packing premise. -/
theorem weighted_coupled_packing_finset {m : ℕ} (hm : 0 < m) (s : Finset (Lattice m))
    (M : Fin m → ℝ) (hM : ∀ i, 1 ≤ M i) :
    (∑ h ∈ s, envelope M 0 h * torusKernel M (coupledTorusPoint h)) ≤
      (786432*(m:ℝ)^2)^m := by
  classical
  have hMp : ∀ i, 0 < M i := fun i => lt_of_lt_of_le zero_lt_one (hM i)
  let keys := s.image (scaleBoxIndex M)
  have he := Finset.sum_fiberwise_of_maps_to
    (s := s) (t := keys) (g := scaleBoxIndex M)
    (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    (fun h => envelope M 0 h * torusKernel M (coupledTorusPoint h))
  rw [← he]
  have hunit (k : Lattice m) : 0 ≤ envelope (fun _ => 1) 0 k :=
    Finset.prod_nonneg (fun _ _ => inv_nonneg.mpr (pow_nonneg (by positivity) _))
  have hbound (k : Lattice m) :
      (∑ h ∈ s with scaleBoxIndex M h = k,
        envelope M 0 h * torusKernel M (coupledTorusPoint h)) ≤
      (16^m * (768*(m:ℝ)^2)^m) * envelope (fun _ => 1) 0 k := by
    let t := s.filter (fun h => scaleBoxIndex M h = k)
    have hp := coupled_torusKernel_packing hm t M hM (by
      intro a ha b hb i
      apply scaleBoxIndex_diameter M hMp a b
      exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    calc
      _ ≤ ∑ h ∈ t, (16^m * envelope (fun _ => 1) 0 k) *
          torusKernel M (coupledTorusPoint h) := by
        apply Finset.sum_le_sum
        intro h hh
        apply mul_le_mul_of_nonneg_right _ (torusKernel_nonneg _ _)
        have hb := envelope_scaleBox_bound M hMp h
        rwa [(Finset.mem_filter.mp hh).2] at hb
      _ = (16^m * envelope (fun _ => 1) 0 k) *
          (∑ h ∈ t, torusKernel M (coupledTorusPoint h)) := by rw [Finset.mul_sum]
      _ ≤ (16^m * envelope (fun _ => 1) 0 k) * (768*(m:ℝ)^2)^m :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg (by positivity) (hunit k))
      _ = _ := by ring
  have hs := (envelope_hasSum (fun _ : Fin m => (1:ℝ)) 0 (fun _ => by norm_num)).summable
  have hmass : (∑ k ∈ keys, envelope (fun _ => (1:ℝ)) 0 k) ≤ (64:ℝ)^m := by
    apply (Summable.sum_le_tsum keys (fun k _ => hunit k) hs).trans
    simpa using envelope_mass (fun _ : Fin m => (1:ℝ)) 0 (fun _ => le_rfl)
  calc
    _ ≤ ∑ k ∈ keys, (16^m * (768*(m:ℝ)^2)^m) * envelope (fun _ => 1) 0 k :=
      Finset.sum_le_sum (fun k _ => hbound k)
    _ = (16^m * (768*(m:ℝ)^2)^m) * ∑ k ∈ keys, envelope (fun _ => 1) 0 k :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (16^m * (768*(m:ℝ)^2)^m) * 64^m :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by rw [← mul_pow, ← mul_pow]; congr 1; ring

/-- Genuine summability and a scale-uniform bound for the full weighted kernel sum. -/
theorem weighted_coupled_packing {m : ℕ} (hm : 0 < m)
    (M : Fin m → ℝ) (hM : ∀ i, 1 ≤ M i) :
    Summable (fun h : Lattice m => envelope M 0 h * torusKernel M (coupledTorusPoint h)) ∧
    (∑' h : Lattice m, envelope M 0 h * torusKernel M (coupledTorusPoint h)) ≤
      (786432*(m:ℝ)^2)^m := by
  have hn (h : Lattice m) : 0 ≤ envelope M 0 h * torusKernel M (coupledTorusPoint h) := by
    apply mul_nonneg _ (torusKernel_nonneg _ _)
    change 0 ≤ ∏ i, decay4 (M i) ((h i:ℝ)-0)
    exact Finset.prod_nonneg (fun i _ => decay4_nonneg _ _)
  have hb := fun s => weighted_coupled_packing_finset hm s M hM
  exact ⟨summable_of_sum_le hn hb, Real.tsum_le_of_sum_le hn hb⟩

end BourgainBasis
