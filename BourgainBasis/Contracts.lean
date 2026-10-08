module
public import Mathlib

@[expose] public section

/-! Exact analytic target for the explicit basis construction.
These are propositions, not asserted theorems. No target is assumed as an axiom.
The explicit polynomial-basis contract is defined in BasisFormula and proved in Main.
-/
noncomputable section
open scoped BigOperators
namespace BourgainBasis

abbrev Lattice (m : ℕ) := Fin m → ℤ

def delta {m : ℕ} (i : Fin m) (w : Lattice m → ℂ) (n : Lattice m) : ℂ :=
  w (n + Pi.single i 1) - w n

def mixedDelta {m : ℕ} (ν : Fin m → ℕ) (w : Lattice m → ℂ) : Lattice m → ℂ :=
  ((List.ofFn fun i : Fin m => (delta i)^[ν i]).foldr (· ∘ ·) id) w

def quadratic {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (n : Lattice m) : ℝ :=
  ∑ i, ∑ j, (n i : ℝ) * (A i j : ℝ) * (n j : ℝ)

def positiveDefinite {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  ∀ x : Fin m → ℝ, x ≠ 0 → 0 < ∑ i, ∑ j, x i * (A i j : ℝ) * x j

def phase (t : ℝ) : ℂ := Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

def envelope {m : ℕ} (M c : Fin m → ℝ) (n : Lattice m) : ℝ :=
  ∏ i, ((1 + |(n i : ℝ) - c i| / M i) ^ (4 : ℕ))⁻¹

def WeightBound {m : ℕ} (M c : Fin m → ℝ) (C₀ : ℝ)
    (w : Lattice m → ℂ) : Prop :=
  ∀ ν : Fin m → ℕ, (∀ i, ν i ≤ 2) → ∀ n,
    ‖mixedDelta ν w n‖ ≤ C₀ * (∏ i, (M i ^ ν i)⁻¹) * envelope M c n

/-- Unproved Proposition `prop:quadratic`. Summability is part of the obligation,
so a totalized `tsum` cannot make a divergent sum satisfy the contract vacuously. -/
def QuadraticCancellation : Prop :=
  ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℤ),
    (∀ i j, A i j = A j i) → positiveDefinite A →
    ∃ C : ℝ, 0 < C ∧ ∀ (M c ξ : Fin m → ℝ) (C₀ : ℝ) (w : Lattice m → ℂ),
      (∀ i, 1 ≤ M i) → 0 < C₀ → WeightBound M c C₀ w →
      Summable (fun n => w n * phase (Real.sqrt 2 * quadratic A n +
        ∑ i, ξ i * (n i : ℝ))) ∧
      ‖∑' n, w n * phase (Real.sqrt 2 * quadratic A n + ∑ i, ξ i * (n i : ℝ))‖
        ≤ C * C₀ * Real.sqrt (∏ i, M i)

def poisson (μ : ℝ) (n : ℕ) : ℝ := Real.exp (-μ) * μ ^ n / (n.factorial : ℝ)
def profileNat (μ : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (1 + μ)) * Real.sqrt (poisson μ n)
def profile (μ : ℝ) (n : ℤ) : ℝ := if 0 ≤ n then profileNat μ n.toNat else 0
def deltaOne (f : ℤ → ℝ) (n : ℤ) : ℝ := f (n + 1) - f n

/-- Unproved Lemma `lem:profile`, including the zero-extension boundary. -/
def PoissonProfileEstimate : Prop :=
  ∀ j R : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ μ : ℝ, 0 ≤ μ → ∀ n : ℤ,
    |(deltaOne^[j]) (profile μ) n| ≤ C * (Real.sqrt (1 + μ) ^ j)⁻¹ *
      ((1 + |(n : ℝ) - μ| / Real.sqrt (1 + μ)) ^ R)⁻¹

end BourgainBasis
