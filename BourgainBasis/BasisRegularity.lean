module
public import BourgainBasis.BasisFormula

@[expose] public section

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgainBasis

theorem homogeneousMonomial_continuous {m N : ℕ} (α : degreeIndices m N) :
    Continuous (homogeneousMonomial α) := by
  exact continuous_finsetProd _ (fun i _ => (PiLp.continuous_apply 2 (fun _ : Fin (m+1) => ℂ) i).pow _)

theorem normalizedMonomial_continuous {m N : ℕ} (α : degreeIndices m N) :
    Continuous (normalizedMonomial α) :=
  continuous_const.mul (homogeneousMonomial_continuous α)

theorem sourceBasisFunction_continuous {m N : ℕ} (T : Set.powersetCard (Fin (N+m)) m) :
    Continuous (sourceBasisFunction T) :=
  continuous_finsetSum _ (fun α _ => continuous_const.mul (normalizedMonomial_continuous α))

/-- The actual sphere Gram integrals in the main contract are genuinely integrable. -/
theorem sourceBasisFunction_gram_integrable {m N : ℕ}
    (T U : Set.powersetCard (Fin (N+m)) m) :
    Integrable (fun z : ComplexUnitSphere m => sourceBasisFunction T z.val *
      star (sourceBasisFunction U z.val)) (normalizedSphere m) := by
  let := normalizedSphere_probability m
  have hc : Continuous (fun z : ComplexUnitSphere m => sourceBasisFunction T z.val *
      star (sourceBasisFunction U z.val)) :=
    ((sourceBasisFunction_continuous T).comp continuous_subtype_val).mul
      (((sourceBasisFunction_continuous U).comp continuous_subtype_val).star)
  have hcompact : IsCompact (Set.univ : Set (ComplexUnitSphere m)) := isCompact_univ
  simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact hcompact

end BourgainBasis
