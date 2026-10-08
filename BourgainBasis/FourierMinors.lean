module
public import BourgainBasis.BasisCombinatorics

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

/-- Minor matrix indexed by m-element subsets, using their increasing enumerations. -/
def orderedMinorMatrix {I J : Type*} [LinearOrder I] [LinearOrder J]
    (m : ℕ) (A : Matrix I J ℂ) : Matrix (Set.powersetCard I m) (Set.powersetCard J m) ℂ :=
  fun S T => (A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm S)
    (Set.powersetCard.ofFinEmbEquiv.symm T)).det

/-- The exterior basis uses exactly the same increasing subset convention. -/
def exteriorCoordinateBasis (I : Type*) [LinearOrder I] [Fintype I] (m : ℕ) :=
  (Pi.basisFun ℂ I).exteriorPower m

/-- Actual determinant minors are the coordinates of the exterior power map. -/
theorem orderedMinorMatrix_toMatrix {I J : Type*} [LinearOrder I] [LinearOrder J]
    [Fintype I] [Fintype J] (m : ℕ) (A : Matrix I J ℂ) :
    orderedMinorMatrix m A =
      LinearMap.toMatrix (exteriorCoordinateBasis J m) (exteriorCoordinateBasis I m)
        (exteriorPower.map m (Matrix.toLin (Pi.basisFun ℂ J) (Pi.basisFun ℂ I) A)) := by
  classical
  ext S T
  rw [LinearMap.toMatrix_apply]
  change _ = ((Pi.basisFun ℂ I).exteriorPower m).repr
    ((exteriorPower.map m (Matrix.toLin (Pi.basisFun ℂ J) (Pi.basisFun ℂ I) A))
      ((Pi.basisFun ℂ J).exteriorPower m T)) S
  rw [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family,
    exteriorPower.basis_repr_apply, exteriorPower.ιMulti_family,
    exteriorPower.ιMultiDual_apply_ιMulti]
  have hc (i : I) (j : J) :
      (Pi.basisFun ℂ I).coord i ((Matrix.toLin (Pi.basisFun ℂ J) (Pi.basisFun ℂ I) A)
        ((Pi.basisFun ℂ J) j)) = A i j := by
    rw [Module.Basis.coord_apply, ← LinearMap.toMatrix_apply, LinearMap.toMatrix_toLin]
  simp only [Function.comp_apply, hc]
  exact (Matrix.det_transpose _).symm

/-- Rectangular Cauchy-Binet as an equality of actual ordered-minor matrices,
derived from functoriality of exterior powers rather than assumed. -/
theorem orderedMinorMatrix_mul {I J K : Type*}
    [LinearOrder I] [LinearOrder J] [LinearOrder K]
    [Fintype I] [Fintype J] [Fintype K] (m : ℕ) (A : Matrix I J ℂ) (B : Matrix J K ℂ) :
    orderedMinorMatrix m (A*B) = orderedMinorMatrix m A * orderedMinorMatrix m B := by
  classical
  simp_rw [orderedMinorMatrix_toMatrix]
  rw [Matrix.toLin_mul (Pi.basisFun ℂ K) (Pi.basisFun ℂ J) (Pi.basisFun ℂ I),
    exteriorPower.map_comp, LinearMap.toMatrix_comp (exteriorCoordinateBasis K m)
      (exteriorCoordinateBasis J m) (exteriorCoordinateBasis I m)]

theorem orderedMinorMatrix_one {I : Type*} [LinearOrder I] [Fintype I] (m : ℕ) :
    orderedMinorMatrix m (1 : Matrix I I ℂ) = 1 := by
  classical
  rw [orderedMinorMatrix_toMatrix, Matrix.toLin_one, exteriorPower.map_id,
    LinearMap.toMatrix_id]

/-- Conjugate transpose commutes with the actual minor matrix. -/
theorem orderedMinorMatrix_star {I : Type*} [LinearOrder I] [Fintype I]
    (m : ℕ) (A : Matrix I I ℂ) :
    orderedMinorMatrix m (star A) = star (orderedMinorMatrix m A) := by
  classical
  ext S T
  change ((star A).submatrix (Set.powersetCard.ofFinEmbEquiv.symm S)
    (Set.powersetCard.ofFinEmbEquiv.symm T)).det =
    star ((A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm T)
      (Set.powersetCard.ofFinEmbEquiv.symm S)).det)
  rw [← Matrix.det_conjTranspose]
  rfl

/-- Unitarity of determinant minors, proved from actual Cauchy-Binet and adjoints. -/
theorem orderedMinorMatrix_unitary {I : Type*} [LinearOrder I] [Fintype I]
    (m : ℕ) (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    orderedMinorMatrix m A ∈ Matrix.unitaryGroup (Set.powersetCard I m) ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
  rw [← orderedMinorMatrix_star, ← orderedMinorMatrix_mul, hA, orderedMinorMatrix_one]

/-- The exact Fourier-minor matrix U(T,S)=det(F_TS) from the source is unitary,
with L=N+m and subsets of cardinality m. The degree-zero case is included. -/
theorem sourceFourierMinors_unitary (N m : ℕ) (hm : 0 < m) :
    orderedMinorMatrix m (sourceFourier (N+m)) ∈
      Matrix.unitaryGroup (Set.powersetCard (Fin (N+m)) m) ℂ :=
  orderedMinorMatrix_unitary m _ (sourceFourier_degree_unitary N m hm)

/-- Explicit row orthogonality for the actual ordered Fourier determinants. -/
theorem sourceFourierMinors_rows (N m : ℕ) (hm : 0 < m)
    (T U : Set.powersetCard (Fin (N+m)) m) :
    (∑ S, orderedMinorMatrix m (sourceFourier (N+m)) T S *
      star (orderedMinorMatrix m (sourceFourier (N+m)) U S)) = if T=U then 1 else 0 := by
  classical
  have h := Matrix.mem_unitaryGroup_iff.mp (sourceFourierMinors_unitary N m hm)
  have hh := congrArg (fun A => A T U) h
  simpa only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using hh

end BourgainBasis
