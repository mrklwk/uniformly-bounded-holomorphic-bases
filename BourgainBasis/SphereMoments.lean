module
public import BourgainBasis.BasisFormula

@[expose] public section

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgainBasis

theorem continuous_homogeneousMonomial {m N : ℕ} (α : degreeIndices m N) :
    Continuous (homogeneousMonomial α) := by
  unfold homogeneousMonomial
  fun_prop

/-- Genuine integrability on the actual normalized sphere measure. -/
theorem sphere_monomial_pair_integrable {m N : ℕ} (α β : degreeIndices m N) :
    Integrable (fun z : ComplexUnitSphere m => homogeneousMonomial α z.val *
      star (homogeneousMonomial β z.val)) (normalizedSphere m) := by
  let := normalizedSphere_probability m
  let : CompactSpace (ComplexUnitSphere m) := isCompact_iff_compactSpace.mp (isCompact_sphere (0:ComplexEuclidean m) 1)
  apply Continuous.integrable_of_hasCompactSupport
  · exact ((continuous_homogeneousMonomial α).comp continuous_subtype_val).mul
      (((continuous_homogeneousMonomial β).comp continuous_subtype_val).star)
  · exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)

theorem degree_zero_coordinate {m : ℕ} (α : degreeIndices m 0) (i : Fin (m+1)) : α.val i=0 := by
  have hh : α.val i ≤ ∑ j, α.val j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [α.property] at hh
  omega

theorem degree_zero_monomial {m : ℕ} (α : degreeIndices m 0) (z : ComplexEuclidean m) :
    homogeneousMonomial α z = 1 := by
  simp [homogeneousMonomial, degree_zero_coordinate]

/-- Exact degree-zero sphere moment; the normalization is the actual probability
measure from SphereModel, with no postulated moment identities. -/
theorem sphere_moment_degree_zero {m : ℕ} (α β : degreeIndices m 0) :
    (∫ z : ComplexUnitSphere m, homogeneousMonomial α z.val *
      star (homogeneousMonomial β z.val) ∂normalizedSphere m) = 1 := by
  let := normalizedSphere_probability m
  simp only [degree_zero_monomial, star_one, mul_one]
  simp

/-- The actual polar radial factor for the Gaussian-weighted degree-N moment. -/
def gaussianRadialMoment (m N : ℕ) : ℂ :=
  ∫ r : Set.Ioi (0:ℝ), ((r:ℝ):ℂ)^(2*N)*(Real.exp (-(r:ℝ)^2):ℂ)
    ∂Measure.volumeIoiPow (Module.finrank ℝ (ComplexEuclidean m)-1)

/-- The exact polar-coordinate reduction of the actual Gaussian monomial moment.
Neither the angular moment nor the radial factor is replaced by an assumption. -/
theorem gaussian_monomial_polar {m N : ℕ} (α β : degreeIndices m N) :
    (∫ x : ComplexEuclidean m, homogeneousMonomial α x*star (homogeneousMonomial β x)*
      (Real.exp (-‖x‖^2):ℂ)) =
    (∫ z : ComplexUnitSphere m, homogeneousMonomial α z.val*star (homogeneousMonomial β z.val)
      ∂(volume : Measure (ComplexEuclidean m)).toSphere) * gaussianRadialMoment m N := by
  let E := ComplexEuclidean m
  let μ : Measure E := volume
  let f : E → ℂ := fun x => homogeneousMonomial α x*star (homogeneousMonomial β x)*
    (Real.exp (-‖x‖^2):ℂ)
  have hp := μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
    (Homeomorph.measurableEmbedding _)
    (fun p : ComplexUnitSphere m × Set.Ioi (0:ℝ) => f ((homeomorphUnitSphereProd E).symm p).val)
  have he : (∫ x : E, f x ∂μ) =
      ∫ p : ComplexUnitSphere m × Set.Ioi (0:ℝ), f ((homeomorphUnitSphereProd E).symm p).val
        ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E-1)) := by
    calc
      _ = ∫ x : ({(0:E)}ᶜ : Set E), f x.val ∂μ.comap Subtype.val := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl,
          restrict_compl_singleton]
      _ = _ := by simpa only [Homeomorph.symm_apply_apply] using hp
  change (∫ x : E, f x ∂μ) = _
  rw [he]
  have hpoint (p : ComplexUnitSphere m × Set.Ioi (0:ℝ)) :
      f ((homeomorphUnitSphereProd E).symm p).val =
      (homogeneousMonomial α p.1.val*star (homogeneousMonomial β p.1.val))*
        (((p.2:ℝ):ℂ)^(2*N)*(Real.exp (-(p.2:ℝ)^2):ℂ)) := by
    have hz : ‖p.1.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using p.1.property
    have hr : 0 < (p.2:ℝ) := p.2.property
    dsimp [f]
    rw [homeomorphUnitSphereProd_symm_apply_coe]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hz, mul_one]
    rw [homogeneousMonomial_smul α (p.2:ℝ) p.1.val,
      homogeneousMonomial_smul β (p.2:ℝ) p.1.val]
    rw [map_mul]
    have hs : (starRingEnd ℂ) (((p.2:ℝ):ℂ)^N) = ((p.2:ℝ):ℂ)^N := by
      rw [map_pow, Complex.conj_ofReal]
    rw [hs, mul_comm 2 N, pow_mul]
    ring
  simp_rw [hpoint]
  exact integral_prod_mul
    (fun z : ComplexUnitSphere m => homogeneousMonomial α z.val*star (homogeneousMonomial β z.val))
    (fun r : Set.Ioi (0:ℝ) => ((r:ℝ):ℂ)^(2*N)*(Real.exp (-(r:ℝ)^2):ℂ))

/-- The Euclidean norm controls the actual homogeneous monomial at every point. -/
theorem homogeneousMonomial_norm_le {m N : ℕ} (α : degreeIndices m N) (x : ComplexEuclidean m) :
    ‖homogeneousMonomial α x‖ ≤ ‖x‖^N := by
  unfold homogeneousMonomial
  rw [norm_prod]
  simp_rw [norm_pow]
  calc
    _ ≤ ∏ i, ‖x‖^(α.val i) := Finset.prod_le_prod₀ (fun _ _ => by positivity)
      (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le x i) _)
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, α.property]

/-- All radial polynomial Gaussian majorants needed here are integrable with
respect to the actual ambient Haar volume, in every complex dimension. -/
theorem gaussian_radial_majorant_integrable (m N : ℕ) :
    Integrable (fun x : ComplexEuclidean m => ‖x‖^(2*N)*Real.exp (-‖x‖^2)) := by
  apply (integrable_fun_norm_addHaar (volume : Measure (ComplexEuclidean m))
    (f := fun y : ℝ => y^(2*N)*Real.exp (-y^2))).mpr
  have hg := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1:ℝ)) (by norm_num)
    (s := ((Module.finrank ℝ (ComplexEuclidean m)-1+2*N:ℕ):ℝ)) (by
      have := Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (ComplexEuclidean m)-1+2*N); linarith)
  simp only [Real.rpow_natCast, neg_one_mul] at hg
  convert hg using 1
  funext y
  simp only [pow_add, smul_eq_mul, mul_assoc]

/-- Genuine ambient Gaussian integrability, so the polar reduction cannot be
satisfied vacuously by a nonintegrable totalized integral. -/
theorem gaussian_monomial_pair_integrable {m N : ℕ} (α β : degreeIndices m N) :
    Integrable (fun x : ComplexEuclidean m => homogeneousMonomial α x*star (homogeneousMonomial β x)*
      (Real.exp (-‖x‖^2):ℂ)) := by
  have hc : Continuous (fun x : ComplexEuclidean m =>
      homogeneousMonomial α x*star (homogeneousMonomial β x)*(Real.exp (-‖x‖^2):ℂ)) :=
    ((continuous_homogeneousMonomial α).mul (continuous_homogeneousMonomial β).star).mul (by fun_prop)
  apply (gaussian_radial_majorant_integrable m N).mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  calc
    _ ≤ ‖x‖^N*‖x‖^N := mul_le_mul (homogeneousMonomial_norm_le α x)
      (homogeneousMonomial_norm_le β x) (norm_nonneg _) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem complexEuclidean_real_dimension (m : ℕ) :
    Module.finrank ℝ (ComplexEuclidean m) = 2*(m+1) := by
  rw [finrank_real_of_complex]
  simp [ComplexEuclidean]

/-- The exact one-dimensional Gaussian radial factor from the Gamma integral. -/
theorem gaussian_odd_radial_integral (k : ℕ) :
    (∫ r : ℝ in Set.Ioi 0, r^(2*k+1)*Real.exp (-r^2)) = (k.factorial:ℝ)/2 := by
  have hg := integral_rpow_mul_exp_neg_rpow (p := (2:ℝ))
    (q := ((2*k+1:ℕ):ℝ)) (by norm_num) (by
      have := Nat.cast_nonneg (α := ℝ) (2*k+1); linarith)
  have hs : (((2*k+1:ℕ):ℝ)+1)/2 = (k:ℝ)+1 := by push_cast; ring
  rw [hs, Real.Gamma_nat_eq_factorial] at hg
  have hp : (2:ℝ) = ((2:ℕ):ℝ) := rfl
  rw [hp] at hg
  simp only [Real.rpow_natCast] at hg
  convert hg using 1
  ring

/-- Exact evaluation of the actual radial measure from HaarToSphere. -/
theorem gaussianRadialMoment_eq (m N : ℕ) :
    gaussianRadialMoment m N = (((N+m).factorial:ℝ)/2:ℂ) := by
  let d := Module.finrank ℝ (ComplexEuclidean m)-1
  have hd : d+2*N=2*(N+m)+1 := by dsimp [d]; rw [complexEuclidean_real_dimension]; omega
  calc
    _ = ∫ r : Set.Ioi (0:ℝ), (r:ℝ)^d •
        (((r:ℝ):ℂ)^(2*N)*(Real.exp (-(r:ℝ)^2):ℂ)) ∂volume.comap Subtype.val := by
      unfold gaussianRadialMoment Measure.volumeIoiPow
      rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards [] with r
      rw [ENNReal.toReal_ofReal (pow_nonneg r.property.le _)]
    _ = ∫ r : ℝ in Set.Ioi 0, ((r^(d+2*N)*Real.exp (-r^2):ℝ):ℂ) := by
      rw [← integral_subtype_comap measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards [] with r
      simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow, pow_add]
      ring
    _ = Complex.ofReal (∫ r : ℝ in Set.Ioi 0, r^(d+2*N)*Real.exp (-r^2)) := integral_ofReal
    _ = _ := by rw [hd, gaussian_odd_radial_integral]; push_cast; rfl

/-- Exact conversion from Haar-induced surface measure to the stipulated
probability measure; no alternate normalization is substituted. -/
theorem normalized_sphere_moment_eq_raw {m N : ℕ} (α β : degreeIndices m N) :
    (∫ z : ComplexUnitSphere m, homogeneousMonomial α z.val*star (homogeneousMonomial β z.val)
      ∂normalizedSphere m) =
    (((volume : Measure (ComplexEuclidean m)).toSphere Set.univ).toReal)⁻¹ •
      (∫ z : ComplexUnitSphere m, homogeneousMonomial α z.val*star (homogeneousMonomial β z.val)
        ∂(volume : Measure (ComplexEuclidean m)).toSphere) := by
  unfold normalizedSphere
  rw [integral_smul_measure, ENNReal.toReal_inv]

/-- The actual Gaussian integral determines the angular moment with the exact
factorial radial constant, rather than an unspecified dimension constant. -/
theorem gaussian_monomial_polar_factorial {m N : ℕ} (α β : degreeIndices m N) :
    (∫ x : ComplexEuclidean m, homogeneousMonomial α x*star (homogeneousMonomial β x)*
      (Real.exp (-‖x‖^2):ℂ)) =
    (∫ z : ComplexUnitSphere m, homogeneousMonomial α z.val*star (homogeneousMonomial β z.val)
      ∂(volume : Measure (ComplexEuclidean m)).toSphere) * (((N+m).factorial:ℝ)/2:ℂ) := by
  rw [gaussian_monomial_polar, gaussianRadialMoment_eq]

end BourgainBasis
