module
public import BourgainBasis.Contracts

@[expose] public section

noncomputable section
open MeasureTheory
namespace BourgainBasis

abbrev ComplexEuclidean (m : ℕ) := EuclideanSpace ℂ (Fin (m+1))
abbrev ComplexUnitSphere (m : ℕ) := Metric.sphere (0 : ComplexEuclidean m) 1

/-- Actual surface measure induced by additive Haar volume on complex Euclidean
space, normalized to total mass one. No moment identities are postulated. -/
def normalizedSphere (m : ℕ) : Measure (ComplexUnitSphere m) :=
  let σ := (volume : Measure (ComplexEuclidean m)).toSphere
  (σ Set.univ)⁻¹ • σ

theorem normalizedSphere_probability (m : ℕ) : IsProbabilityMeasure (normalizedSphere m) := by
  let σ := (volume : Measure (ComplexEuclidean m)).toSphere
  have hσ : σ ≠ 0 := Measure.toSphere_ne_zero _
  let : NeZero σ := ⟨hσ⟩
  change IsProbabilityMeasure ((σ Set.univ)⁻¹ • σ)
  infer_instance

theorem normalizedSphere_mass (m : ℕ) : normalizedSphere m Set.univ = 1 := by
  let := normalizedSphere_probability m
  exact measure_univ

end BourgainBasis
