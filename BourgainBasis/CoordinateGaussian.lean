module
public import BourgainBasis.GaussianOffDiagonal
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory MeasureTheory.Measure
namespace BourgainBasis

def coordinateVolume (m : ℕ) : Measure (ComplexEuclidean m) :=
  (volume : Measure (Fin (m+1) → ℂ)).map (WithLp.toLp 2)

instance coordinateVolume_isAddHaar (m : ℕ) : IsAddHaarMeasure (coordinateVolume m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m+1) => ℂ)).symm.isAddHaarMeasure_map volume

def coordinateVolumeFactor (m : ℕ) : ℝ≥0 := addHaarScalarFactor (coordinateVolume m) volume

theorem coordinateVolumeFactor_pos (m : ℕ) : 0 < coordinateVolumeFactor m :=
  addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem coordinateVolume_eq (m : ℕ) : coordinateVolume m = coordinateVolumeFactor m • volume :=
  isAddLeftInvariant_eq_smul _ _

theorem gaussian_product_integrand {m N : ℕ} (α β : degreeIndices m N)
    (x : Fin (m+1) → ℂ) :
    homogeneousMonomial α (WithLp.toLp 2 x)*star (homogeneousMonomial β (WithLp.toLp 2 x))*
      (Real.exp (-‖(WithLp.toLp 2 x : ComplexEuclidean m)‖^2):ℂ) =
      ∏ i,x i^(α.val i)*star (x i^(β.val i))*(Real.exp (-‖x i‖^2):ℂ) := by
  rw [EuclideanSpace.norm_sq_eq,←Finset.sum_neg_distrib,Real.exp_sum,Complex.ofReal_prod]
  simp only [homogeneousMonomial,star_prod,Finset.prod_mul_distrib]

theorem gaussian_coordinate_integral {m N : ℕ} (α β : degreeIndices m N) :
    (∫ x : ComplexEuclidean m,homogeneousMonomial α x*star (homogeneousMonomial β x)*
      (Real.exp (-‖x‖^2):ℂ) ∂coordinateVolume m) =
      ∏ i,if α.val i=β.val i then (Real.pi:ℂ)*((α.val i).factorial:ℂ) else 0 := by
  unfold coordinateVolume
  erw [(MeasurableEquiv.toLp 2 (Fin (m+1) → ℂ)).measurableEmbedding.integral_map]
  simp only [MeasurableEquiv.coe_toLp]
  simp_rw [gaussian_product_integrand]
  rw [integral_fintype_prod_volume_eq_prod (fun i (z:ℂ) => z^(α.val i)*star (z^(β.val i))*(Real.exp (-‖z‖^2):ℂ))]
  simp only [complex_gaussian_moment]

theorem gaussian_coordinate_polar {m N : ℕ} (α β : degreeIndices m N) :
    (∏ i,if α.val i=β.val i then (Real.pi:ℂ)*((α.val i).factorial:ℂ) else 0) =
      (coordinateVolumeFactor m:ℝ) •
        ((∫ z : ComplexUnitSphere m,homogeneousMonomial α z.val*star (homogeneousMonomial β z.val)
          ∂(volume : Measure (ComplexEuclidean m)).toSphere) * (((N+m).factorial:ℝ)/2:ℂ)) := by
  rw [←gaussian_coordinate_integral,coordinateVolume_eq,integral_smul_nnreal_measure,
    gaussian_monomial_polar_factorial]
  rfl

end BourgainBasis
