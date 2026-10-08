module
public import BourgainBasis.DeterminantExpansion
public import BourgainBasis.CoordinatePermutation

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

def coordinateProbability {m : ℕ} (z : ComplexEuclidean m) (i : Fin (m+1)) : ℝ := ‖z i‖^2
def coordinatePhase {m : ℕ} (z : ComplexEuclidean m) (i : Fin (m+1)) : ℝ := (z i).arg/(2*Real.pi)

theorem coordinateProbability_sum {m : ℕ} (z : ComplexEuclidean m) (hz : ‖z‖=1) :
    ∑ i,coordinateProbability z i=1 := by
  change (∑ i,‖z i‖^2)=1
  rw [←EuclideanSpace.norm_sq_eq,hz]
  norm_num

theorem complex_polar_phase (z : ℂ) : (‖z‖:ℂ)*phase (z.arg/(2*Real.pi))=z := by
  have he : 2*Real.pi*(z.arg/(2*Real.pi))=z.arg := by field_simp
  simpa only [phase,he] using Complex.norm_mul_exp_arg_mul_I z

theorem phase_nat_mul (t : ℝ) (n : ℕ) : phase (t*n)=phase t^n := by
  induction n with
  | zero => simp [phase]
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,mul_add,mul_one,phase_add,ih,pow_succ]

theorem homogeneousMonomial_polar {m N : ℕ} (α : degreeIndices m N) (z : ComplexEuclidean m) :
    homogeneousMonomial α z =
      ((∏ i,‖z i‖^(α.val i):ℝ):ℂ)*phase (∑ i,coordinatePhase z i*(α.val i:ℝ)) := by
  rw [phase_finset_sum]
  simp only [phase_nat_mul,Complex.ofReal_prod,Complex.ofReal_pow,←Finset.prod_mul_distrib,←mul_pow]
  unfold homogeneousMonomial coordinatePhase
  simp only [complex_polar_phase]

theorem monomialNormalization_factor {m N : ℕ} (α : degreeIndices m N) :
    monomialNormalization α = Real.sqrt ((N+m).choose m:ℝ)*
      Real.sqrt ((N.factorial:ℝ)/(∏ i,(α.val i).factorial:ℝ)) := by
  unfold monomialNormalization
  rw [←Real.sqrt_mul (by positivity)]
  congr 1
  have hf : (0:ℝ) < m.factorial := by positivity
  have hprod : (0:ℝ) < ∏ i,((α.val i).factorial:ℝ) := by
    exact_mod_cast (Finset.prod_pos (fun i _ => Nat.factorial_pos (α.val i)))
  have he : ((N+m).choose m:ℝ)*(m.factorial:ℝ)*(N.factorial:ℝ)=((N+m).factorial:ℝ) := by
    exact_mod_cast (show (N+m).choose m*m.factorial*N.factorial=(N+m).factorial by
      simpa using (Nat.choose_mul_factorial_mul_factorial (show m≤N+m by omega)))
  field_simp
  push_cast
  rw [←he]
  ring

theorem multinomial_amplitude {m N : ℕ} (α : degreeIndices m N) (z : ComplexEuclidean m) :
    Real.sqrt ((N.factorial:ℝ)/(∏ i,(α.val i).factorial:ℝ)) * (∏ i,‖z i‖^(α.val i)) =
      Real.sqrt ((N.factorial:ℝ)/(∏ i,(α.val i).factorial:ℝ) *
        ∏ i,(coordinateProbability z i)^(α.val i)) := by
  rw [Real.sqrt_mul (by positivity)]
  congr 1
  unfold coordinateProbability
  simp_rw [←pow_mul, Nat.mul_comm 2, pow_mul]
  rw [Finset.prod_pow,Real.sqrt_sq (Finset.prod_nonneg (fun i _ => by positivity))]

theorem normalizedMonomial_polar {m N : ℕ} (α : degreeIndices m N) (z : ComplexEuclidean m) :
    normalizedMonomial α z = (Real.sqrt ((N+m).choose m:ℝ):ℂ)*
      (Real.sqrt ((N.factorial:ℝ)/(∏ i,(α.val i).factorial:ℝ) *
        ∏ i,(coordinateProbability z i)^(α.val i)):ℂ)*
      phase (∑ i,coordinatePhase z i*(α.val i:ℝ)) := by
  unfold normalizedMonomial
  rw [homogeneousMonomial_polar,monomialNormalization_factor]
  rw [Complex.ofReal_mul]
  have h := congrArg Complex.ofReal (multinomial_amplitude α z)
  rw [Complex.ofReal_mul] at h
  rw [mul_assoc,←mul_assoc (Real.sqrt ((N.factorial:ℝ)/(∏ i,(α.val i).factorial:ℝ)):ℂ),h]
  ring

end BourgainBasis
