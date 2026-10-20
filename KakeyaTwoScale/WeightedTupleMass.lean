module
public import KakeyaTwoScale.NonlinearTupleSelection

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Weights belong to the stored original tuples, before any selection. -/
def weightedTupleCubeMass {T Q : Type*} [DecidableEq Q]
    (Y : Finset T) (cube : T → Q) (cubes : Finset Q) (w : T → ℝ) (p : ℝ) : ℝ :=
  ∑ q ∈ cubes, (∑ y ∈ Y.filter (fun y => cube y = q), w y) ^ p

theorem weightedTupleCubeMass_band_bounds {T Q : Type*} [DecidableEq Q]
    (Y : Finset T) (cube : T → Q) (cubes : Finset Q) (w : T → ℝ)
    {lo hi p : ℝ} (hlo : 0 ≤ lo) (hp : 0 ≤ p)
    (hw : ∀ y ∈ Y, lo ≤ w y ∧ w y ≤ hi) :
    lo ^ p * tupleCubeMass Y cube cubes p ≤ weightedTupleCubeMass Y cube cubes w p ∧
    weightedTupleCubeMass Y cube cubes w p ≤ hi ^ p * tupleCubeMass Y cube cubes p := by
  classical
  have hsum (q) : lo * (ParentLevel.capacity Y cube q : ℝ) ≤
      ∑ y ∈ Y.filter (fun y => cube y = q), w y := by
    calc
      _ = ∑ _y ∈ Y.filter (fun y => cube y = q), lo := by
        simp [ParentLevel.capacity, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun y hy => (hw y (Finset.mem_filter.mp hy).1).1
  have hsum' (q) : (∑ y ∈ Y.filter (fun y => cube y = q), w y) ≤
      hi * (ParentLevel.capacity Y cube q : ℝ) := by
    calc
      _ ≤ ∑ _y ∈ Y.filter (fun y => cube y = q), hi :=
        Finset.sum_le_sum fun y hy => (hw y (Finset.mem_filter.mp hy).1).2
      _ = _ := by simp [ParentLevel.capacity, mul_comm]
  have hn (q) : 0 ≤ ∑ y ∈ Y.filter (fun y => cube y = q), w y :=
    (mul_nonneg hlo (Nat.cast_nonneg _)).trans (hsum q)
  constructor
  · unfold tupleCubeMass weightedTupleCubeMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    rw [← Real.mul_rpow hlo (Nat.cast_nonneg _)]
    exact Real.rpow_le_rpow (mul_nonneg hlo (Nat.cast_nonneg _)) (hsum q) hp
  · by_cases hhi : 0 ≤ hi
    · unfold tupleCubeMass weightedTupleCubeMass
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q hq
      rw [← Real.mul_rpow hhi (Nat.cast_nonneg _)]
      exact Real.rpow_le_rpow (hn q) (hsum' q) hp
    · have hY : Y = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        exact hhi (hlo.trans ((hw y hy).1.trans (hw y hy).2))
      subst Y
      by_cases hp0 : p = 0
      · subst p
        simp [weightedTupleCubeMass, tupleCubeMass, ParentLevel.capacity]
      · simp [weightedTupleCubeMass, tupleCubeMass, ParentLevel.capacity, Real.zero_rpow hp0]

/-- An unweighted retention bound is valid for determinant weights only after
restricting the ORIGINAL relation to a common band. The selected relation is
an actual subset, and its new fibers supply the retained mass. -/
theorem weightedTupleCubeMass_dyadic_retention {T Q : Type*}
    [DecidableEq Q] (Y Z : Finset T) (hZY : Z ⊆ Y)
    (cube : T → Q) (cubes : Finset Q) (w : T → ℝ)
    {θ p loss : ℝ} (hθ : 0 < θ) (hp : 0 ≤ p) (hloss : 0 < loss)
    (hw : ∀ y ∈ Y, θ ≤ w y ∧ w y ≤ 2 * θ)
    (hmass : tupleCubeMass Y cube cubes p / loss ≤ tupleCubeMass Z cube cubes p) :
    weightedTupleCubeMass Y cube cubes w p / (2 ^ p * loss) ≤
      weightedTupleCubeMass Z cube cubes w p := by
  have hY := (weightedTupleCubeMass_band_bounds Y cube cubes w hθ.le hp hw).2
  have hZ := (weightedTupleCubeMass_band_bounds Z cube cubes w hθ.le hp
    (fun y hy => hw y (hZY hy))).1
  have hmass' := (div_le_iff₀ hloss).mp hmass
  have hθp : 0 < θ ^ p := Real.rpow_pos_of_pos hθ p
  have h2p : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  apply (div_le_iff₀ (mul_pos h2p hloss)).mpr
  apply (mul_le_mul_iff_right₀ hθp).mp
  calc
    θ ^ p * weightedTupleCubeMass Y cube cubes w p ≤
        θ ^ p * ((2 * θ) ^ p * tupleCubeMass Y cube cubes p) :=
      mul_le_mul_of_nonneg_left hY hθp.le
    _ ≤ θ ^ p * ((2 * θ) ^ p * (tupleCubeMass Z cube cubes p * loss)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmass' (Real.rpow_nonneg (by positivity) p)) hθp.le
    _ = (2 ^ p * loss * θ ^ p) * (θ ^ p * tupleCubeMass Z cube cubes p) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hθ.le]
      ring
    _ ≤ (2 ^ p * loss * θ ^ p) * weightedTupleCubeMass Z cube cubes w p :=
      mul_le_mul_of_nonneg_left hZ (by positivity)
    _ = θ ^ p * (weightedTupleCubeMass Z cube cubes w p * (2 ^ p * loss)) := by ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.weightedTupleCubeMass_band_bounds
#print axioms KakeyaTwoScale.weightedTupleCubeMass_dyadic_retention
