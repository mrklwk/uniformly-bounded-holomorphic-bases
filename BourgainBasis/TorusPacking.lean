module
public import BourgainBasis.Separation
public import BourgainBasis.LatticeMass

@[expose] public section

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgainBasis

/-- Product kernel on the unit torus, using the distance to zero in each coordinate. -/
def torusKernel {m : ℕ} (M : Fin m → ℝ) (x : Fin m → UnitAddCircle) : ℝ :=
  ∏ i, ((1 + M i * ‖x i‖)^2)⁻¹

/-- A closed anisotropic box. Its radius is measured after multiplying coordinate i
by M i. Closed boxes are convenient since their Haar volumes are explicit. -/
def torusBox {m : ℕ} (M : Fin m → ℝ) (r : ℝ) (x : Fin m → UnitAddCircle) :
    Set (Fin m → UnitAddCircle) :=
  Set.univ.pi (fun i => Metric.closedBall (x i) (r / M i))

theorem mem_torusBox {m : ℕ} (M : Fin m → ℝ) (r : ℝ)
    (x y : Fin m → UnitAddCircle) :
    y ∈ torusBox M r x ↔ ∀ i, ‖y i - x i‖ ≤ r / M i := by
  simp [torusBox, Metric.mem_closedBall, dist_eq_norm]

/-- Separation gives genuinely disjoint boxes, including all boundary points when
2r < rho. No packing or cardinality bound is assumed. -/
theorem torusBox_disjoint {m : ℕ} (M : Fin m → ℝ) (hM : ∀ i, 0 < M i)
    (r ρ : ℝ) (hr : 2*r < ρ) (x y : Fin m → UnitAddCircle)
    (hsep : ∃ i, ρ ≤ M i * ‖x i - y i‖) :
    Disjoint (torusBox M r x) (torusBox M r y) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  rw [mem_torusBox] at hz hz'
  obtain ⟨i, hi⟩ := hsep
  have hn : ‖x i - y i‖ ≤ ‖z i - x i‖ + ‖z i - y i‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using dist_triangle (x i) (z i) (y i)
  have hb := mul_le_mul_of_nonneg_left (hn.trans (add_le_add (hz i) (hz' i))) (hM i).le
  have he : M i * (r / M i + r / M i) = 2*r := by field_simp [(hM i).ne']; ring
  rw [he] at hb
  linarith

theorem torusBox_measurable {m : ℕ} (M : Fin m → ℝ) (r : ℝ)
    (x : Fin m → UnitAddCircle) : MeasurableSet (torusBox M r x) := by
  exact MeasurableSet.univ_pi (fun _ => measurableSet_closedBall)

/-- Exact Haar volume, including radii so large that a coordinate covers its circle.
The `min` is essential for large radii and prevents a false Euclidean volume formula. -/
theorem torusBox_volume {m : ℕ} (M : Fin m → ℝ) (r : ℝ)
    (x : Fin m → UnitAddCircle) :
    volume (torusBox M r x) = ∏ i, ENNReal.ofReal (min 1 (2*(r/M i))) := by
  change Measure.pi (fun _ : Fin m => (volume : Measure UnitAddCircle))
    (Set.univ.pi (fun i => Metric.closedBall (x i) (r / M i))) = _
  rw [Measure.pi_pi]
  simp_rw [AddCircle.volume_closedBall]

/-- Exact small-box volume, with all scale assumptions explicit. -/
theorem torusBox_volume_small {m : ℕ} (M : Fin m → ℝ) (hM : ∀ i, 1 ≤ M i)
    (r : ℝ) (_hr : 0 ≤ r) (hr' : r ≤ 1/2) (x : Fin m → UnitAddCircle) :
    volume (torusBox M r x) = ∏ i, ENNReal.ofReal (2*r/M i) := by
  rw [torusBox_volume]
  apply Finset.prod_congr rfl
  intro i _
  have hMi : 0 < M i := by linarith [hM i]
  have hh : 2*(r/M i) ≤ 1 := by
    rw [← mul_div_assoc]
    exact (div_le_one hMi).mpr (by linarith [hM i])
  rw [min_eq_right hh]
  congr 1
  ring

/-- Coordinate kernel stability on a box. This is the local comparison used when
integrating the kernel over disjoint boxes. -/
theorem torus_coordinate_kernel_compare (M r : ℝ) (hM : 0 ≤ M) (hr : 0 ≤ r)
    (x y : UnitAddCircle) (hxy : M * ‖y-x‖ ≤ r) :
    ((1+M*‖x‖)^2)⁻¹ ≤ (1+r)^2 * ((1+M*‖y‖)^2)⁻¹ := by
  have hn : ‖y‖ ≤ ‖x‖ + ‖y-x‖ := by
    have hh := norm_add_le x (y-x)
    simpa only [add_sub_cancel, add_comm] using hh
  have ha : 0 < 1+M*‖x‖ := by positivity
  have hb : 0 < 1+M*‖y‖ := by positivity
  have hc : 1+M*‖y‖ ≤ (1+r)*(1+M*‖x‖) := by
    nlinarith [mul_le_mul_of_nonneg_left hn hM, mul_nonneg hr (mul_nonneg hM (norm_nonneg x))]
  have hp := pow_le_pow_left₀ hb.le hc 2
  rw [mul_pow] at hp
  rw [← one_div, ← one_div, mul_one_div]
  apply (div_le_div_iff₀ (pow_pos ha 2) (pow_pos hb 2)).mpr
  simpa only [one_mul] using hp

theorem torusKernel_nonneg {m : ℕ} (M : Fin m → ℝ) (x : Fin m → UnitAddCircle) :
    0 ≤ torusKernel M x := by
  unfold torusKernel
  exact Finset.prod_nonneg (fun _ _ => inv_nonneg.mpr (sq_nonneg _))

theorem torusKernel_box_compare {m : ℕ} (M : Fin m → ℝ) (hM : ∀ i, 0 < M i)
    (r : ℝ) (hr : 0 ≤ r) (x y : Fin m → UnitAddCircle) (hy : y ∈ torusBox M r x) :
    torusKernel M x ≤ ((1+r)^2)^m * torusKernel M y := by
  rw [mem_torusBox] at hy
  have h (i : Fin m) := torus_coordinate_kernel_compare (M i) r (hM i).le hr
    (x i) (y i) (by simpa only [mul_comm] using (le_div_iff₀ (hM i)).mp (hy i))
  unfold torusKernel
  calc
    _ ≤ ∏ i, ((1+r)^2 * ((1+M i*‖y i‖)^2)⁻¹) :=
      Finset.prod_le_prod₀ (fun _ _ => inv_nonneg.mpr (sq_nonneg _)) (fun i _ => h i)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- A box around a point in a larger box is contained in the coordinatewise enlarged
box. This permits localized counting instead of only global torus cardinality. -/
theorem torusBox_subset_enlarged {m : ℕ} (M R : Fin m → ℝ) (_hM : ∀ i, 0 < M i)
    (r : ℝ) (x z : Fin m → UnitAddCircle)
    (hx : ∀ i, ‖x i-z i‖ ≤ R i / M i) :
    torusBox M r x ⊆ Set.univ.pi
      (fun i => Metric.closedBall (z i) ((R i+r)/M i)) := by
  intro y hy
  rw [mem_torusBox] at hy
  intro i _
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc
    ‖y i-z i‖ ≤ ‖y i-x i‖ + ‖x i-z i‖ := by
      simpa only [dist_eq_norm] using dist_triangle (y i) (x i) (z i)
    _ ≤ r/M i + R i/M i := add_le_add (hy i) (hx i)
    _ = _ := by ring

/-- Finite, localized anisotropic packing inequality with exact Haar volumes.
Both sides are explicit, and no packing estimate is a premise. In particular the
bound remains valid when the enlarged box wraps around a coordinate circle. -/
theorem torus_local_packing_volume {m : ℕ} {α : Type*} (s : Finset α)
    (x : α → Fin m → UnitAddCircle) (M R : Fin m → ℝ)
    (hM : ∀ i, 1 ≤ M i) (r ρ : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1/2)
    (hsepRadius : 2*r < ρ) (z : Fin m → UnitAddCircle)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ i, ρ ≤ M i*‖x a i-x b i‖)
    (hloc : ∀ a ∈ s, ∀ i, ‖x a i-z i‖ ≤ R i/M i) :
    (s.card : ENNReal) * (∏ i, ENNReal.ofReal (2*r/M i)) ≤
      ∏ i, ENNReal.ofReal (min 1 (2*((R i+r)/M i))) := by
  have hMp : ∀ i, 0 < M i := fun i => lt_of_lt_of_le zero_lt_one (hM i)
  have hd : Set.PairwiseDisjoint (↑s) (fun a => torusBox M r (x a)) := by
    intro a ha b hb hab
    exact torusBox_disjoint M hMp r ρ hsepRadius (x a) (x b) (hsep a ha b hb hab)
  have hsub : (⋃ a ∈ s, torusBox M r (x a)) ⊆ Set.univ.pi
      (fun i => Metric.closedBall (z i) ((R i+r)/M i)) := by
    intro y hy
    obtain ⟨a, ha, hy⟩ := Set.mem_iUnion₂.mp hy
    exact torusBox_subset_enlarged M R hMp r (x a) z (hloc a ha) hy
  have hv := measure_mono (μ := (volume : Measure (Fin m → UnitAddCircle))) hsub
  rw [measure_biUnion_finset hd (fun a _ => torusBox_measurable M r (x a))] at hv
  simp_rw [torusBox_volume_small M hM r hr hr'] at hv
  simp only [Finset.sum_const, nsmul_eq_mul] at hv
  change _ ≤ Measure.pi (fun _ : Fin m => (volume : Measure UnitAddCircle))
    (Set.univ.pi (fun i => Metric.closedBall (z i) ((R i+r)/M i))) at hv
  rw [Measure.pi_pi] at hv
  simpa only [AddCircle.volume_closedBall] using hv

/-- Scale-uniform local counting. The scales M cancel exactly; the estimate is
valid in dimension zero, for empty sets, and for boxes wrapping around the torus. -/
theorem torus_local_packing {m : ℕ} {α : Type*} (s : Finset α)
    (x : α → Fin m → UnitAddCircle) (M R : Fin m → ℝ)
    (hM : ∀ i, 1 ≤ M i) (hR : ∀ i, 0 ≤ R i)
    (r ρ : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2)
    (hsepRadius : 2*r < ρ) (z : Fin m → UnitAddCircle)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ i, ρ ≤ M i*‖x a i-x b i‖)
    (hloc : ∀ a ∈ s, ∀ i, ‖x a i-z i‖ ≤ R i/M i) :
    (s.card : ℝ) ≤ ∏ i, (R i+r)/r := by
  have hMp : ∀ i, 0 < M i := fun i => lt_of_lt_of_le zero_lt_one (hM i)
  have hv := torus_local_packing_volume s x M R hM r ρ hr.le hr' hsepRadius z hsep hloc
  have hu : (s.card : ENNReal) * (∏ i, ENNReal.ofReal (2*r/M i)) ≤
      ∏ i, ENNReal.ofReal (2*((R i+r)/M i)) := by
    exact hv.trans (Finset.prod_le_prod (fun i _ => ENNReal.ofReal_le_ofReal (min_le_right _ _)))
  have hfin : (∏ i, ENNReal.ofReal (2*((R i+r)/M i))) ≠ ⊤ := by
    exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)
  have ht := ENNReal.toReal_mono hfin hu
  have hn (i : Fin m) : 0 ≤ 2*r/M i := by have := hMp i; positivity
  have hn' (i : Fin m) : 0 ≤ 2*((R i+r)/M i) := by have := hMp i; have := hR i; positivity
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_prod,
    ENNReal.toReal_ofReal (hn _), ENNReal.toReal_ofReal (hn' _)] at ht
  have he : (∏ i, 2*((R i+r)/M i)) =
      (∏ i, (R i+r)/r) * (∏ i, 2*r/M i) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    field_simp
  rw [he] at ht
  have hP : 0 < ∏ i, 2*r/M i := Finset.prod_pos (fun i _ => by have := hMp i; positivity)
  exact (mul_le_mul_iff_left₀ hP).mp (by simpa only [mul_comm] using ht)

/-- Weighted rectangular-shell packing bound. The lower and upper coordinate
radii can be chosen independently, as required for anisotropic dyadic shells. -/
theorem torus_shell_packing {m : ℕ} {α : Type*} (s : Finset α)
    (x : α → Fin m → UnitAddCircle) (M L R : Fin m → ℝ)
    (hM : ∀ i, 1 ≤ M i) (hL : ∀ i, 0 ≤ L i) (hR : ∀ i, 0 ≤ R i)
    (r ρ : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) (hsepRadius : 2*r < ρ)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ i, ρ ≤ M i*‖x a i-x b i‖)
    (hlow : ∀ a ∈ s, ∀ i, L i ≤ M i*‖x a i‖)
    (hupp : ∀ a ∈ s, ∀ i, M i*‖x a i‖ ≤ R i) :
    (∑ a ∈ s, torusKernel M (x a)) ≤ ∏ i, ((R i+r)/r) / (1+L i)^2 := by
  have hMp : ∀ i, 0 < M i := fun i => lt_of_lt_of_le zero_lt_one (hM i)
  have hcount := torus_local_packing s x M R hM hR r ρ hr hr' hsepRadius 0 hsep
    (fun a ha i => by simpa only [Pi.zero_apply, sub_zero] using
      (le_div_iff₀ (hMp i)).mpr (by simpa only [mul_comm] using hupp a ha i))
  have hpoint : ∀ a ∈ s, torusKernel M (x a) ≤ ∏ i, ((1+L i)^2)⁻¹ := by
    intro a ha
    apply Finset.prod_le_prod₀ (fun i _ => inv_nonneg.mpr (sq_nonneg _))
    intro i _
    have hl : 0 < 1+L i := by linarith [hL i]
    exact inv_anti₀ (pow_pos hl 2) (pow_le_pow_left₀ hl.le (by linarith [hlow a ha i]) 2)
  calc
    _ ≤ ∑ _a ∈ s, (∏ i, ((1+L i)^2)⁻¹) := Finset.sum_le_sum hpoint
    _ = (s.card : ℝ) * (∏ i, ((1+L i)^2)⁻¹) := by simp
    _ ≤ (∏ i, (R i+r)/r) * (∏ i, ((1+L i)^2)⁻¹) :=
      mul_le_mul_of_nonneg_right hcount (Finset.prod_nonneg (fun _ _ => inv_nonneg.mpr (sq_nonneg _)))
    _ = _ := by rw [← Finset.prod_mul_distrib]; simp only [div_eq_mul_inv]

end BourgainBasis
