module
public import Mathlib
public import BourgainBasis.Main

@[expose] public section

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace BourgainStatement

/-- Nonnegative exponent vectors with total degree N. -/
abbrev Degree (m N : ℕ) := {α : Fin (m+1) → ℕ // ∑ i, α i = N}

/-- Enumeration of all degree-N exponent vectors by multisets of coordinates. -/
instance degreeFintype (m N : ℕ) : Fintype (Degree m N) :=
  Fintype.ofEquiv (Sym (Fin (m+1)) N) (Sym.equivNatSumOfFintype (Fin (m+1)) N)

/-- d = m+1 complex coordinates. -/
abbrev E (m : ℕ) := EuclideanSpace ℂ (Fin (m+1))

/-- Manuscript e(t) = exp(2πit). -/
def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * t * Complex.I)

/-- Manuscript 1-based bar s_j(α) = j + α_1 + ... + α_j, j = 1..m
(here j0 = j-1 is zero-based and α_r is stored at index r-1). -/
def bar {m : ℕ} (α : Fin (m+1) → ℕ) (j0 : Fin m) : ℕ :=
  (j0.val + 1) + ∑ k : Fin (m+1) with k.val < j0.val + 1, α k

/-- U_{T,S(α)} = det( L^{-1/2} e(t_i s_j / L) ), rows t_1<...<t_m of T ⊆ {1..L}
(stored zero-based), columns the manuscript bars of α. -/
def minor {m N : ℕ} (T : Finset (Fin (N+m))) (hT : T.card = m)
    (α : Fin (m+1) → ℕ) : ℂ :=
  Matrix.det (fun i j : Fin m =>
    ((Real.sqrt ((N+m : ℕ) : ℝ) : ℂ))⁻¹ *
      e ((((T.orderEmbOfFin hT i).val + 1 : ℕ) : ℝ) * ((bar α j : ℕ) : ℝ) / ((N+m : ℕ) : ℝ)))

/-- Φ_T(z) = Σ_{|α|=N} U_{T,S(α)} e(√2 Σ α_r²) √((N+m)!/(m! ∏ α_r!)) z^α. -/
def Φ {m N : ℕ} (T : Finset (Fin (N+m))) (hT : T.card = m) (z : E m) : ℂ :=
  ∑ α : Degree m N,
    minor T hT α.val * e (Real.sqrt 2 * ∑ r, ((α.val r : ℕ) : ℝ)^2) *
      (Real.sqrt (((N+m).factorial : ℝ) / ((m.factorial : ℝ) * ∏ r, ((α.val r).factorial : ℝ))) : ℂ) *
      ∏ r, (z r)^(α.val r)

/-- Normalized surface measure: Haar volume pushed to the sphere, mass one. -/
def σ (m : ℕ) : Measure (Metric.sphere (0 : E m) 1) :=
  ((volume : Measure (E m)).toSphere Set.univ)⁻¹ • (volume : Measure (E m)).toSphere

example (m N : ℕ) : Degree m N = {α : Fin (m+1) → ℕ // ∑ i, α i = N} := rfl

/-- Monomials z^α, |α| = N. -/
def mono (m N : ℕ) : Degree m N → (E m → ℂ) :=
  fun α z => ∏ r, (z r)^(α.val r)

theorem bar_eq {m N : ℕ} (α : BourgainBasis.degreeIndices m N) (j : Fin m) :
    bar α.val j = (BourgainBasis.barEntry α j).val + 1 := by
  rw [BourgainBasis.barEntry_source_position]
  unfold bar BourgainBasis.barPrefix
  congr 2

theorem minor_eq {m N : ℕ} (T : Set.powersetCard (Fin (N+m)) m)
    (α : BourgainBasis.degreeIndices m N) :
    minor T.val T.prop α.val =
      BourgainBasis.orderedMinorMatrix m (BourgainBasis.sourceFourier (N+m)) T
        (BourgainBasis.starsBarsEquiv m N α) := by
  unfold minor BourgainBasis.orderedMinorMatrix
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, BourgainBasis.starsBarsEquiv_sorted,
    BourgainBasis.sourceFourier, BourgainBasis.phase, bar_eq, e]
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  congr 2
  push_cast
  ring

theorem Φ_eq {m N : ℕ} (T : Set.powersetCard (Fin (N+m)) m) :
    Φ T.val T.prop = BourgainBasis.sourceBasisFunction T := by
  funext z
  unfold Φ BourgainBasis.sourceBasisFunction BourgainBasis.basisCoefficient
    BourgainBasis.normalizedMonomial BourgainBasis.monomialNormalization
    BourgainBasis.homogeneousMonomial
  apply Finset.sum_congr rfl
  intro α _
  rw [minor_eq T α]
  simp only [e, BourgainBasis.phase]
  push_cast
  ring_nf

/-- Manuscript Theorem 1.1, for d = m+1 ≥ 2, constant chosen before N. -/
theorem manuscript_main (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (∀ (T U : Finset (Fin (N+m))) (hT : T.card = m) (hU : U.card = m),
        (∫ z, Φ T hT z.val * star (Φ U hU z.val) ∂σ m) = if T = U then 1 else 0) ∧
      Submodule.span ℂ (Set.range (fun T : {T : Finset (Fin (N+m)) // T.card = m} => Φ T.val T.prop)) =
        Submodule.span ℂ (Set.range (mono m N)) ∧
      (∀ (T : Finset (Fin (N+m))) (hT : T.card = m) (z : E m), ‖z‖ ≤ 1 → ‖Φ T hT z‖ ≤ C) := by
  obtain ⟨C, hC, h⟩ := BourgainBasis.uniformly_bounded_homogeneous_basis m hm
  refine ⟨C, hC, fun N => ⟨?_, ?_, ?_⟩⟩
  · intro T U hT hU
    have := (h N).1 ⟨T, hT⟩ ⟨U, hU⟩
    rw [Φ_eq ⟨T, hT⟩, Φ_eq ⟨U, hU⟩]
    refine this.trans ?_
    by_cases hTU : T = U
    · subst hTU; simp
    · have h2 : ¬ ((⟨T, hT⟩ : Set.powersetCard (Fin (N+m)) m) = ⟨U, hU⟩) := fun h2 => hTU (congrArg Subtype.val h2)
      simp only [hTU, h2, ↓reduceIte]
  · have := (h N).2.1
    have hr : Set.range (fun T : {T : Finset (Fin (N+m)) // T.card = m} => Φ T.val T.prop) =
        Set.range (BourgainBasis.sourceBasisFunction (m:=m) (N:=N)) := by
      ext f
      constructor
      · rintro ⟨T, rfl⟩; exact ⟨⟨T.val, T.prop⟩, (Φ_eq ⟨T.val, T.prop⟩).symm⟩
      · rintro ⟨T, rfl⟩; exact ⟨⟨T.val, T.prop⟩, Φ_eq T⟩
    rw [hr]
    exact this
  · intro T hT z hz
    rw [Φ_eq ⟨T, hT⟩]
    exact (h N).2.2 ⟨T, hT⟩ z hz

-- Sanity facts about the objects in the statement.
example (m : ℕ) : (volume : Measure (E m)).IsAddHaarMeasure := inferInstance
example (m : ℕ) : σ m = BourgainBasis.normalizedSphere m := rfl
example (m : ℕ) : IsProbabilityMeasure (σ m) := BourgainBasis.normalizedSphere_probability m
example (m : ℕ) (z : E m) : ‖z‖ = Real.sqrt (∑ i, ‖z i‖^2) := EuclideanSpace.norm_eq z

/-- Non-vacuity: degree one, d = 2, the family is nonempty and each element is nonzero. -/
example (m N : ℕ) : 0 < Fintype.card (Set.powersetCard (Fin (N+m)) m) := by
  rw [Fintype.card_congr (BourgainBasis.starsBarsEquiv m N).symm, BourgainBasis.degreeIndices_card]
  exact Nat.choose_pos (by omega)

end BourgainStatement

#print axioms BourgainStatement.manuscript_main
