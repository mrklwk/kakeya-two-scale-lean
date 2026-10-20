module
public import KakeyaTwoScale.NestedGrid
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open scoped BigOperators

/-! Two separated encounters control the actual affine parameters. This is
geometric input for brush counting, not a brush-transfer or Kakeya theorem. -/
namespace KakeyaTwoScale
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two close encounters at separated heights force the slopes to be close.
The separation is unoriented; either height may come first. -/
theorem slope_dist_of_two_encounters (b v b' v' : E) (s t r h : ℝ)
    (hh : 0 < h) (hsep : h ≤ |t-s|)
    (hs : dist (segmentPoint b v s) (segmentPoint b' v' s) ≤ r)
    (ht : dist (segmentPoint b v t) (segmentPoint b' v' t) ≤ r) :
    dist v v' ≤ 2*r/h := by
  have hid : (t-s) • (v-v') =
      (segmentPoint b v t - segmentPoint b' v' t) -
      (segmentPoint b v s - segmentPoint b' v' s) := by
    unfold segmentPoint
    module
  have hn : |t-s| * dist v v' ≤ 2*r := by
    calc
      _ = ‖(t-s) • (v-v')‖ := by rw [norm_smul, Real.norm_eq_abs, dist_eq_norm]
      _ = _ := congrArg norm hid
      _ ≤ ‖segmentPoint b v t - segmentPoint b' v' t‖ +
          ‖segmentPoint b v s - segmentPoint b' v' s‖ := norm_sub_le _ _
      _ ≤ 2*r := by rw [← dist_eq_norm, ← dist_eq_norm]; linarith
  apply (le_div_iff₀ hh).2
  have hm := mul_le_mul_of_nonneg_right hsep (dist_nonneg (x:=v) (y:=v'))
  nlinarith

/-- Recovering the intercept uses one encounter within the unit height interval. -/
theorem intercept_dist_of_encounter (b v b' v' : E) (s r R : ℝ)
    (hsunit : s ∈ Set.Icc (0:ℝ) 1)
    (hs : dist (segmentPoint b v s) (segmentPoint b' v' s) ≤ r)
    (hv : dist v v' ≤ R) : dist b b' ≤ r+R := by
  have hid : b-b' = (segmentPoint b v s - segmentPoint b' v' s) - s • (v-v') := by
    unfold segmentPoint
    module
  rw [dist_eq_norm, hid]
  calc
    _ ≤ ‖segmentPoint b v s - segmentPoint b' v' s‖ + ‖s • (v-v')‖ := norm_sub_le _ _
    _ = dist (segmentPoint b v s) (segmentPoint b' v' s) + s * dist v v' := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsunit.1, dist_eq_norm, dist_eq_norm]
    _ ≤ r+R := by
      have hm := mul_le_mul_of_nonneg_right hsunit.2 (dist_nonneg (x:=v) (y:=v'))
      nlinarith

theorem parameters_dist_of_two_encounters (b v b' v' : E) (s t r h : ℝ)
    (hh : 0 < h) (hsep : h ≤ |t-s|) (hsunit : s ∈ Set.Icc (0:ℝ) 1)
    (hs : dist (segmentPoint b v s) (segmentPoint b' v' s) ≤ r)
    (ht : dist (segmentPoint b v t) (segmentPoint b' v' t) ≤ r) :
    dist v v' ≤ 2*r/h ∧ dist b b' ≤ r+2*r/h := by
  have hv := slope_dist_of_two_encounters b v b' v' s t r h hh hsep hs ht
  exact ⟨hv, intercept_dist_of_encounter b v b' v' s r _ hsunit hs hv⟩

/-- Sharing two actual grid cells supplies both encounter hypotheses. -/
theorem parameters_dist_of_two_grid_cells {n : ℕ} {r : ℝ} (hr : 0 < r)
    (b v b' v' : Fin n → ℝ) (s t h : ℝ)
    (hh : 0 < h) (hsep : h ≤ |t-s|) (hsunit : s ∈ Set.Icc (0:ℝ) 1)
    (hs : gridIndex r (segmentPoint b v s) = gridIndex r (segmentPoint b' v' s))
    (ht : gridIndex r (segmentPoint b v t) = gridIndex r (segmentPoint b' v' t)) :
    dist v v' ≤ 2*r/h ∧ dist b b' ≤ r+2*r/h := by
  apply parameters_dist_of_two_encounters b v b' v' s t r h hh hsep hsunit
  · apply gridCell_dist_le hr.le (mem_own_gridCell hr _)
    rw [hs]
    exact mem_own_gridCell hr _
  · apply gridCell_dist_le hr.le (mem_own_gridCell hr _)
    rw [ht]
    exact mem_own_gridCell hr _
/-- Explicit conversion of the grid's sup metric to Euclidean distance. -/
theorem euclidean_dist_le_sqrt_mul_sup {n : ℕ} (x y : Fin n → ℝ) :
    dist (WithLp.toLp 2 x) (WithLp.toLp 2 y) ≤ Real.sqrt n * dist x y := by
  have hcoord : ∀ i, dist (x i) (y i) ≤ dist x y :=
    (dist_pi_le_iff (dist_nonneg (x:=x) (y:=y))).1 le_rfl
  have hs : dist (WithLp.toLp 2 x) (WithLp.toLp 2 y) ^ 2 ≤
      (n : ℝ) * dist x y ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      _ ≤ ∑ _i : Fin n, dist x y ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ dist_nonneg (hcoord i) 2
      _ = _ := by simp
  have hroot := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)
  have hnonneg : 0 ≤ Real.sqrt n * dist x y := mul_nonneg (Real.sqrt_nonneg _) dist_nonneg
  have he : (Real.sqrt n * dist x y)^2 = (n:ℝ)*dist x y^2 := by
    rw [mul_pow, hroot]
  nlinarith [dist_nonneg (x:=WithLp.toLp 2 x) (y:=WithLp.toLp 2 y)]

theorem gridCell_euclidean_dist_le {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    {k : Fin n → ℤ} {x y : Fin n → ℝ}
    (hx : x ∈ gridCell r k) (hy : y ∈ gridCell r k) :
    dist (WithLp.toLp 2 x) (WithLp.toLp 2 y) ≤ Real.sqrt n * r := by
  exact (euclidean_dist_le_sqrt_mul_sup x y).trans
    (mul_le_mul_of_nonneg_left (gridCell_dist_le hr hx hy) (Real.sqrt_nonneg _))
end KakeyaTwoScale
#print axioms KakeyaTwoScale.parameters_dist_of_two_encounters
#print axioms KakeyaTwoScale.parameters_dist_of_two_grid_cells

#print axioms KakeyaTwoScale.euclidean_dist_le_sqrt_mul_sup
#print axioms KakeyaTwoScale.gridCell_euclidean_dist_le
