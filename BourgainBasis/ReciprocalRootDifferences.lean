module
public import BourgainBasis.SlantedDifferences

@[expose] public section

noncomputable section
namespace BourgainBasis

/-- Unit forward difference on a real argument. -/
def realDelta (f : ℝ → ℝ) : ℝ → ℝ := fun x => f (x+1)-f x

/-- Rising product, kept recursive to follow the derivative induction exactly. -/
def risingBound (p : ℝ) : ℕ → ℝ
  | 0 => 1
  | a+1 => p*risingBound (p+1) a

theorem risingBound_nonneg {p : ℝ} (hp : 0≤p) (a : ℕ) : 0≤risingBound p a := by
  induction a generalizing p with
  | zero => norm_num [risingBound]
  | succ a ih => exact mul_nonneg hp (ih (by linarith))

theorem risingBound_pos {p : ℝ} (hp : 0<p) (a : ℕ) : 0<risingBound p a := by
  induction a generalizing p with
  | zero => norm_num [risingBound]
  | succ a ih => exact mul_pos hp (ih (by linarith))

theorem realDelta_iterate_const_mul (f : ℝ → ℝ) (c : ℝ) (a : ℕ) :
    (realDelta^[a]) (fun x => c*f x) = fun x => c*((realDelta^[a]) f x) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih]
    funext x
    simp [realDelta,mul_sub]

/-- Derivatives commute with every finite difference on the positive half-line. -/
theorem realDelta_iterate_hasDerivAt (f g : ℝ → ℝ)
    (hf : ∀ x,0<x → HasDerivAt f (g x) x) (a : ℕ) (x : ℝ) (hx : 0<x) :
    HasDerivAt ((realDelta^[a]) f) ((realDelta^[a]) g x) x := by
  induction a generalizing x with
  | zero => exact hf x hx
  | succ a ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    have hs := (ih (x+1) (by linarith)).comp x ((hasDerivAt_id x).add_const 1)
    have ht := hs.sub (ih x hx)
    convert ht using 1 <;> simp [realDelta,Function.comp_def]
    funext y
    rfl

/-- Arbitrary-order reciprocal-power finite differences, proved by derivative
commutation and the mean value inequality. No assumed finite-difference bound. -/
theorem reciprocal_power_difference_bound (a : ℕ) (p x : ℝ) (hp : 0<p) (hx : 0<x) :
    |(realDelta^[a]) (fun y => y^(-p)) x| ≤ risingBound p a * x^(-p-(a:ℝ)) := by
  induction a generalizing p x with
  | zero => simp [risingBound,abs_of_nonneg (Real.rpow_nonneg hx.le _)]
  | succ a ih =>
    let F := (realDelta^[a]) (fun y : ℝ => y^(-p))
    let G := fun y : ℝ => (-p)*((realDelta^[a]) (fun z : ℝ => z^(-(p+1))) y)
    have hder (y : ℝ) (hy : 0<y) : HasDerivAt F (G y) y := by
      have hf (z : ℝ) (hz : 0<z) :
          HasDerivAt (fun u : ℝ => u^(-p)) ((-p)*z^(-(p+1))) z := by
        have he : -(p+1) = -p-1 := by ring
        rw [he]
        exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hz))
      have h := realDelta_iterate_hasDerivAt _ _ hf a y hy
      rw [realDelta_iterate_const_mul] at h
      exact h
    have hbound (y : ℝ) (hy : y∈Set.Ico x (x+1)) :
        ‖G y‖ ≤ risingBound p (a+1)*x^(-p-((a+1:ℕ):ℝ)) := by
      have hy₀ : 0<y := lt_of_lt_of_le hx hy.1
      have hpow : y^(-(p+1)-(a:ℝ)) ≤ x^(-(p+1)-(a:ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hx hy.1 (by linarith [Nat.cast_nonneg (α:=ℝ) a])
      dsimp [G]
      rw [abs_mul,abs_neg,abs_of_pos hp]
      calc
        _ ≤ p*(risingBound (p+1) a*y^(-(p+1)-(a:ℝ))) :=
          mul_le_mul_of_nonneg_left (ih (p+1) y (by linarith) hy₀) hp.le
        _ ≤ p*(risingBound (p+1) a*x^(-(p+1)-(a:ℝ))) := by
          gcongr
          exact risingBound_nonneg (by linarith) a
        _ = _ := by
          simp only [risingBound,Nat.cast_add,Nat.cast_one]
          rw [show -(p+1)-(a:ℝ) = -p-((a:ℝ)+1) by ring]
          ring
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun y (hy : y∈Set.Icc x (x+1)) => (hder y (lt_of_lt_of_le hx hy.1)).hasDerivWithinAt)
      hbound (x+1) (by constructor <;> linarith)
    rw [Function.iterate_succ_apply',realDelta]
    simpa [F,Real.norm_eq_abs] using h

/-- Sampling a real function along an integer translate preserves differences. -/
theorem deltaOne_real_sample (f : ℝ → ℝ) (c : ℝ) (a : ℕ) (n : ℤ) :
    (deltaOne^[a]) (fun k : ℤ => f ((k:ℝ)+c)) n =
      (realDelta^[a]) f ((n:ℝ)+c) := by
  induction a generalizing n with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',deltaOne,realDelta,ih,ih]
    rw [show ((n+1:ℤ):ℝ)+c = (n:ℝ)+c+1 by push_cast; ring]

/-- Finite differences depend only on the values in their actual stencil. -/
theorem deltaOne_local_congr (f g : ℤ → ℝ) (a : ℕ) (n : ℤ)
    (h : ∀ r : ℕ,r≤a → f (n+r)=g (n+r)) :
    (deltaOne^[a]) f n = (deltaOne^[a]) g n := by
  induction a generalizing n with
  | zero => simpa using h 0 (by omega)
  | succ a ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',deltaOne,deltaOne]
    rw [ih (n+1) (by
      intro r hr
      have hh := h (r+1) (by omega)
      convert hh using 1 <;> congr 1 <;> push_cast <;> omega),
      ih n (fun r hr => h r (by omega))]

/-- Exact reciprocal-square-root representation on every nonnegative index. -/
theorem reciprocal_root_rpow {μ : ℝ} (hμ : 0≤μ) (n : ℤ) (hn : 0≤n) :
    Real.sqrt (μ/((n:ℝ)+1)) = Real.sqrt μ * ((n:ℝ)+1)^(-(1/2:ℝ)) := by
  rw [Real.sqrt_div hμ,Real.rpow_neg (by exact_mod_cast (show (0:ℤ)≤n+1 by omega)),
    ←Real.sqrt_eq_rpow,div_eq_mul_inv]

/-- Arbitrary-order finite differences of the actual Poisson recurrence ratio.
The constant is the rising half-integer product and is independent of μ,n.
The theorem includes a=0 and μ=0, hence also every required a≥1. -/
theorem reciprocal_root_difference_bound {μ : ℝ} (hμ : 0≤μ) (a n : ℕ) :
    |(deltaOne^[a]) (fun k : ℤ => Real.sqrt (μ/((k:ℝ)+1))) (n:ℤ)| ≤
      risingBound (1/2) a * Real.sqrt μ * ((n:ℝ)+1)^(-(1/2:ℝ)-(a:ℝ)) := by
  have he := deltaOne_local_congr
    (fun k : ℤ => Real.sqrt (μ/((k:ℝ)+1)))
    (fun k : ℤ => Real.sqrt μ * ((k:ℝ)+1)^(-(1/2:ℝ))) a (n:ℤ) (by
      intro r _
      exact reciprocal_root_rpow hμ _ (by positivity))
  rw [he,deltaOne_real_sample (fun x : ℝ => Real.sqrt μ*x^(-(1/2:ℝ))) 1 a,
    realDelta_iterate_const_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg μ)]
  have h := mul_le_mul_of_nonneg_left
    (reciprocal_power_difference_bound a (1/2) ((n:ℝ)+1) (by norm_num) (by positivity))
    (Real.sqrt_nonneg μ)
  simpa only [Int.cast_natCast,mul_assoc,mul_comm,mul_left_comm] using h

/-- The equivalent denominator form exhibits the gain (n+1)^(-a-1/2). -/
theorem reciprocal_root_difference_bound_div {μ : ℝ} (hμ : 0≤μ) (a n : ℕ) :
    |(deltaOne^[a]) (fun k : ℤ => Real.sqrt (μ/((k:ℝ)+1))) (n:ℤ)| ≤
      (risingBound (1/2) a * Real.sqrt μ) /
        ((n:ℝ)+1)^((a:ℝ)+(1/2:ℝ)) := by
  have h := reciprocal_root_difference_bound hμ a n
  have he : -(1/2:ℝ)-(a:ℝ) = -((a:ℝ)+(1/2:ℝ)) := by ring
  rw [he,Real.rpow_neg (by positivity),←div_eq_mul_inv] at h
  exact h

end BourgainBasis
