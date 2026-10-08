module
public import BourgainBasis.CoordinateGaussian
public import BourgainBasis.BasisRegularity

@[expose] public section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory
namespace BourgainBasis

local instance sphereDegreeDecidableEq (m N : ℕ) : DecidableEq (degreeIndices m N) := Classical.decEq _

def sphereArea (m : ℕ) : ℝ := ((volume : Measure (ComplexEuclidean m)).toSphere Set.univ).toReal

theorem gaussian_area_identity (m : ℕ) :
    (Real.pi:ℂ)^(m+1) = (coordinateVolumeFactor m:ℝ) * (sphereArea m:ℂ) * ((m.factorial:ℂ)/2) := by
  let α : degreeIndices m 0 := ⟨fun _ => 0,by simp⟩
  have h := gaussian_coordinate_polar α α
  simp only [degree_zero_monomial,star_one,mul_one,integral_const] at h
  simp only [α,ite_true,Nat.factorial_zero,Nat.cast_one,mul_one,Nat.zero_add] at h
  change (∏ i : Fin (m+1),(Real.pi:ℂ)) =
    (coordinateVolumeFactor m:ℝ) • ((sphereArea m) • (1:ℂ) * ((m.factorial:ℂ)/2)) at h
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Complex.real_smul,mul_one,mul_assoc] using h

theorem sphereArea_ne_zero (m : ℕ) : sphereArea m≠0 := by
  intro h
  have he := gaussian_area_identity m
  rw [h,Complex.ofReal_zero,mul_zero,zero_mul] at he
  exact (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) he

/-- Exact moments for the stipulated probability surface measure, including degree zero. -/
theorem sphere_monomial_moment {m N : ℕ} (α β : degreeIndices m N) :
    (∫ z : ComplexUnitSphere m,homogeneousMonomial α z.val*star (homogeneousMonomial β z.val)
      ∂normalizedSphere m) =
      if α=β then ((m.factorial:ℂ)*(∏ i,((α.val i).factorial:ℂ)))/((N+m).factorial:ℂ) else 0 := by
  let J : ℂ := ∫ z : ComplexUnitSphere m,homogeneousMonomial α z.val*star (homogeneousMonomial β z.val)
    ∂(volume : Measure (ComplexEuclidean m)).toSphere
  let c : ℂ := ((coordinateVolumeFactor m:ℝ):ℂ)
  have hc : c≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by exact_mod_cast coordinateVolumeFactor_pos m))
  have hF : ((N+m).factorial:ℂ)≠0 := by exact_mod_cast (Nat.factorial_ne_zero (N+m))
  have hS : (sphereArea m:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (sphereArea_ne_zero m)
  have h := gaussian_coordinate_polar α β
  change (∏ i,if α.val i=β.val i then (Real.pi:ℂ)*((α.val i).factorial:ℂ) else 0) =
    c*(J*(((N+m).factorial:ℂ)/2)) at h
  rw [normalized_sphere_moment_eq_raw]
  change (sphereArea m)⁻¹ • J = _
  rw [Complex.real_smul,Complex.ofReal_inv]
  by_cases hab : α=β
  · subst β
    simp only [ite_true,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
    have h0 := gaussian_area_identity m
    change (Real.pi:ℂ)^(m+1)=c*(sphereArea m:ℂ)*((m.factorial:ℂ)/2) at h0
    rw [h0] at h
    simp only [ite_true]
    have hrel : (sphereArea m:ℂ)*(m.factorial:ℂ)*(∏ i,((α.val i).factorial:ℂ)) = J*((N+m).factorial:ℂ) := by
      apply mul_left_cancel₀ hc
      linear_combination 2*h
    field_simp
    exact hrel.symm
  · have hi : ∃ i,α.val i≠β.val i := by
      by_contra h'
      push Not at h'
      exact hab (Subtype.ext (funext h'))
    obtain ⟨i,hi⟩ := hi
    have hp : (∏ j,if α.val j=β.val j then (Real.pi:ℂ)*((α.val j).factorial:ℂ) else 0)=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [hp] at h
    have hJ : J=0 := by
      have hh : c*(J*(((N+m).factorial:ℂ)/2))=0 := h.symm
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hc)).resolve_right (div_ne_zero hF (by norm_num))
    simp [hab,hJ]

theorem normalizedMonomial_gram {m N : ℕ} (α β : degreeIndices m N) :
    (∫ z : ComplexUnitSphere m,normalizedMonomial α z.val*star (normalizedMonomial β z.val)
      ∂normalizedSphere m) = if α=β then 1 else 0 := by
  have he : (fun z : ComplexUnitSphere m => normalizedMonomial α z.val*star (normalizedMonomial β z.val)) =
      fun z => ((monomialNormalization α:ℂ)*(monomialNormalization β:ℂ))*
        (homogeneousMonomial α z.val*star (homogeneousMonomial β z.val)) := by
    funext z
    simp only [normalizedMonomial,star_mul,Complex.star_def,Complex.conj_ofReal]
    ring
  rw [he,integral_const_mul,sphere_monomial_moment]
  by_cases hab : α=β
  · subst β
    simp only [ite_true]
    have hsq : (monomialNormalization α)^2 =
        ((N+m).factorial:ℝ)/((m.factorial:ℝ)*∏ i,((α.val i).factorial:ℝ)) := by
      unfold monomialNormalization
      simpa using Real.sq_sqrt (show (0:ℝ) ≤ ((N+m).factorial:ℝ)/((m.factorial:ℝ)*∏ i,((α.val i).factorial:ℝ)) by positivity)
    have hsqC := congrArg Complex.ofReal hsq
    push_cast at hsqC
    rw [←pow_two,hsqC]
    have hF : ((N+m).factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (N+m)
    have hm : (m.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero m
    have hP : (∏ i,((α.val i).factorial:ℂ))≠0 := Finset.prod_ne_zero_iff.mpr
      (fun i _ => by exact_mod_cast Nat.factorial_ne_zero (α.val i))
    field_simp
  · simp [hab]

end BourgainBasis
