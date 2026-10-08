module
public import BourgainBasis.PoissonCancellation

@[expose] public section

noncomputable section
open scoped BigOperators
namespace BourgainBasis

def degreePermute {m N : ℕ} (e : Equiv.Perm (Fin (m+1))) :
    degreeIndices m N ≃ degreeIndices m N where
  toFun α := ⟨fun i => α.val (e i), by rw [Equiv.sum_comp e]; exact α.property⟩
  invFun α := ⟨fun i => α.val (e.symm i), by rw [Equiv.sum_comp e.symm]; exact α.property⟩
  left_inv α := by apply Subtype.ext; funext i; simp
  right_inv α := by apply Subtype.ext; funext i; simp

def multinomialSum {m N : ℕ} (p θ : Fin (m+1) → ℝ) : ℂ :=
  ∑ α : degreeIndices m N,
    (Real.sqrt ((N.factorial:ℝ)/(∏ i,(α.val i).factorial:ℝ) * ∏ i,(p i)^(α.val i)):ℂ) *
      phase (Real.sqrt 2*(∑ i,(α.val i:ℝ)^2)+∑ i,θ i*(α.val i:ℝ))

theorem multinomialSum_permute {m N : ℕ} (e : Equiv.Perm (Fin (m+1)))
    (p θ : Fin (m+1) → ℝ) :
    multinomialSum (N:=N) (p ∘ e) (θ ∘ e) = multinomialSum (N:=N) p θ := by
  unfold multinomialSum
  rw [←(degreePermute (N:=N) e).sum_comp]
  apply Finset.sum_congr rfl
  intro α _
  change (Real.sqrt ((N.factorial:ℝ)/(∏ i,((α.val (e i)).factorial:ℝ)) * ∏ i,(p (e i))^(α.val (e i))):ℂ) *
    phase (Real.sqrt 2*(∑ i,(α.val (e i):ℝ)^2)+∑ i,θ (e i)*(α.val (e i):ℝ)) = _
  rw [Equiv.prod_comp e (fun i => ((α.val i).factorial:ℝ)),
    Equiv.prod_comp e (fun i => p i^(α.val i)),Equiv.sum_comp e (fun i => (α.val i:ℝ)^2),
    Equiv.sum_comp e (fun i => θ i*(α.val i:ℝ))]

/-- Coordinate symmetry removes the largest-last-coordinate restriction. -/
theorem multinomial_cancellation (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ,0<C ∧ ∀ (N : ℕ) (p : Fin (m+1) → ℝ),
      (∀ i,0≤p i) → (∑ i,p i=1) → ∀ θ : Fin (m+1) → ℝ,
      ‖multinomialSum (N:=N) p θ‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := multinomial_quadratic_cancellation_full_frequency m hm
  refine ⟨C,hC,?_⟩
  intro N p hp₀ hp θ
  obtain ⟨k,_,hk⟩ := Finset.exists_max_image Finset.univ p Finset.univ_nonempty
  let e := Equiv.swap (Fin.last m) k
  have hsum : ∑ i,p (e i)=1 := by rw [Equiv.sum_comp e]; exact hp
  have hlast : ∀ i : Fin m,p (e i.castSucc)≤p (e (Fin.last m)) := by
    intro i
    simpa [e] using hk (e i.castSucc) (Finset.mem_univ _)
  have h := hbound N (p ∘ e) (fun i => hp₀ (e i)) hsum hlast (θ ∘ e)
  change ‖multinomialSum (N:=N) (p ∘ e) (θ ∘ e)‖ ≤ C at h
  rwa [multinomialSum_permute] at h

end BourgainBasis
