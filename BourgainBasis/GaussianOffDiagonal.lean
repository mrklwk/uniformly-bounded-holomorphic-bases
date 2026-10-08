module
public import BourgainBasis.ComplexGaussian
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgainBasis

theorem complex_gaussian_rotation (a b : ℕ) (c : Circle) :
    (∫ z : ℂ,z^a*star (z^b)*(Real.exp (-‖z‖^2):ℂ)) =
    ((c:ℂ)^a*star ((c:ℂ)^b))*(∫ z : ℂ,z^a*star (z^b)*(Real.exp (-‖z‖^2):ℂ)) := by
  let f : ℂ → ℂ := fun z => z^a*star (z^b)*(Real.exp (-‖z‖^2):ℂ)
  have h := (rotation c).measurePreserving.integral_comp (rotation c).toHomeomorph.measurableEmbedding f
  have he : (fun z => f (rotation c z)) = fun z => ((c:ℂ)^a*star ((c:ℂ)^b))*f z := by
    funext z
    simp only [f,rotation_apply,mul_pow,star_mul,norm_mul,Circle.norm_coe,one_mul]
    ring
  rw [he,integral_const_mul] at h
  exact h.symm

theorem complex_gaussian_off_diagonal (a b : ℕ) (hab : a≠b) :
    (∫ z : ℂ,z^a*star (z^b)*(Real.exp (-‖z‖^2):ℂ)) = 0 := by
  let n := a+b+1
  have hn : n≠0 := by dsimp [n]; omega
  let ζ := Complex.exp (2*Real.pi*Complex.I/(n:ℂ))
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn
  have hnorm : ‖ζ‖=1 := hζ.norm'_eq_one hn
  let c : Circle := ⟨ζ,by simpa [Submonoid.unitSphere] using hnorm⟩
  let J : ℂ := ∫ z : ℂ,z^a*star (z^b)*(Real.exp (-‖z‖^2):ℂ)
  have h := complex_gaussian_rotation a b c
  change J=(ζ^a*star (ζ^b))*J at h
  by_contra hJ
  change J≠0 at hJ
  have hcoef : ζ^a*star (ζ^b)=1 := (mul_right_cancel₀ hJ (by simpa using h.symm))
  have hunit : star (ζ^b)*ζ^b=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,norm_pow,hnorm]
    norm_num
  have hp : ζ^a=ζ^b := by
    calc
      _ = ζ^a*(star (ζ^b)*ζ^b) := by rw [hunit,mul_one]
      _ = _ := by rw [←mul_assoc,hcoef,one_mul]
  exact hab (hζ.pow_inj (by dsimp [n]; omega) (by dsimp [n]; omega) hp)

theorem complex_gaussian_moment (a b : ℕ) :
    (∫ z : ℂ,z^a*star (z^b)*(Real.exp (-‖z‖^2):ℂ)) =
      if a=b then (Real.pi:ℂ)*(a.factorial:ℂ) else 0 := by
  split_ifs with h
  · subst b; exact complex_gaussian_diagonal a
  · exact complex_gaussian_off_diagonal a b h

end BourgainBasis
