module
public import BourgainBasis.DifferenceAlgebra

@[expose] public section

noncomputable section
namespace BourgainBasis

theorem lattice_summation_by_parts {m : ℕ} (i : Fin m)
    (f χ : Lattice m → ℂ) (ζ : ℂ) (hζ : ζ ≠ 0)
    (hχ : ∀ n, χ (n + Pi.single i 1) = ζ * χ n)
    (hf : Summable (fun n => f n * χ n)) :
    Summable (fun n => delta i f n * χ n) ∧
    (∑' n, delta i f n * χ n) = (ζ⁻¹-1) * ∑' n, f n * χ n := by
  have hs : Summable (fun n : Lattice m => f (n+Pi.single i 1) * χ (n+Pi.single i 1)) :=
    (Equiv.summable_iff (f := fun n : Lattice m => f n * χ n)
      (Equiv.addRight (Pi.single i (1:ℤ)))).mpr hf
  have he : (fun n => delta i f n * χ n) =
      (fun n => ζ⁻¹ * (f (n+Pi.single i 1) * χ (n+Pi.single i 1)) - f n * χ n) := by
    funext n
    rw [hχ]
    unfold delta
    field_simp
  rw [he]
  refine ⟨(hs.mul_left ζ⁻¹).sub hf, ?_⟩
  rw [((hs.mul_left ζ⁻¹).tsum_sub hf), tsum_mul_left]
  have ht := (Equiv.addRight (Pi.single i (1:ℤ))).tsum_eq (fun n => f n*χ n)
  change (∑' n : Lattice m, f (n+Pi.single i 1)*χ (n+Pi.single i 1)) = ∑' n, f n*χ n at ht
  rw [ht]
  ring

theorem lattice_summation_by_parts_iterate {m : ℕ} (i : Fin m)
    (f χ : Lattice m → ℂ) (ζ : ℂ) (hζ : ζ ≠ 0)
    (hχ : ∀ n, χ (n + Pi.single i 1) = ζ * χ n)
    (hf : Summable (fun n => f n * χ n)) (k : ℕ) :
    Summable (fun n => ((delta i)^[k]) f n * χ n) ∧
    (∑' n, ((delta i)^[k]) f n * χ n) = (ζ⁻¹-1)^k * ∑' n, f n * χ n := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hh := lattice_summation_by_parts i (((delta i)^[k]) f) χ ζ hζ hχ ih.1
    refine ⟨hh.1, ?_⟩
    rw [hh.2, ih.2, pow_succ]
    ring

end BourgainBasis
