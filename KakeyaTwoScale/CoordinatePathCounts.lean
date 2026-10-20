module
public import KakeyaTwoScale.CoordinatePathCrossing

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The complete coordinate line through a supplied base point. -/
def coordinateLinePoint {N : ℕ} (j : Fin N) (a : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (Function.update a.ofLp j t)

/-- Literal count of all zeros in the open unit ball on this line. -/
def ballCoordinateCount {N : ℕ} (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (j : Fin N) (a : EuclideanSpace ℝ (Fin N)) : ℝ≥0∞ :=
  ({t : ℝ | f (coordinateLinePoint j a t)=0 ∧ coordinateLinePoint j a t ∈ ball 0 1} : Set ℝ).encard.toENNReal

theorem coordinateLinePoint_eq {N : ℕ} (j : Fin N) (a w : EuclideanSpace ℝ (Fin N))
    (h : ∀ i, i ≠ j → w i = a i) : coordinateLinePoint j a (w j) = w := by
  ext i
  by_cases hi : i=j
  · subst i; simp [coordinateLinePoint]
  · simp [coordinateLinePoint,hi,h i hi]

/-- A genuine localized zero gives a count of at least one, even on a whole zero line. -/
theorem one_le_ballCoordinateCount {N : ℕ} (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (j : Fin N) (a w : EuclideanSpace ℝ (Fin N)) (hw : w ∈ ball 0 1) (hf : f w=0)
    (h : ∀ i, i ≠ j → w i=a i) : 1 ≤ ballCoordinateCount f j a := by
  have he := coordinateLinePoint_eq j a w h
  have hn : ({t : ℝ | f (coordinateLinePoint j a t)=0 ∧ coordinateLinePoint j a t ∈ ball 0 1} : Set ℝ).Nonempty :=
    ⟨w j,by simpa only [he,mem_ofPred_eq] using And.intro hf hw⟩
  have hc := one_le_encard_iff_nonempty.mpr hn
  simpa only [ENat.toENNReal_one,ballCoordinateCount] using ENat.toENNReal_mono hc

/-- Actual pointwise crossing inequality on the two safe coordinate paths. -/
theorem two_paths_count_lower {N : ℕ}
    (f : EuclideanSpace ℝ (Fin N) → ℝ) (hf : Continuous f)
    (x y z : EuclideanSpace ℝ (Fin N))
    (hxz : ‖x‖^2+‖z‖^2 < 1) (hyz : ‖y‖^2+‖z‖^2 < 1)
    (hx : 0 < f x) (hy : f y < 0) :
    1 ≤ (∑ j : Fin N, ballCoordinateCount f j (coordinateHybrid x z j.val)) +
      ∑ j : Fin N, ballCoordinateCount f j (coordinateHybrid y z j.val) := by
  obtain ⟨j,w,hw,hzero,he⟩ := two_coordinate_paths_zero f hf x y z hxz hyz hx hy
  rcases he with he | he
  · exact (one_le_ballCoordinateCount f j _ w hw hzero he).trans
      ((Finset.single_le_sum (f := fun k : Fin N => ballCoordinateCount f k (coordinateHybrid x z k.val)) (fun _ _ => zero_le) (Finset.mem_univ j)).trans (le_self_add))
  · exact (one_le_ballCoordinateCount f j _ w hw hzero he).trans
      ((Finset.single_le_sum (f := fun k : Fin N => ballCoordinateCount f k (coordinateHybrid y z k.val)) (fun _ _ => zero_le) (Finset.mem_univ j)).trans (le_add_self))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coordinateLinePoint_eq
#print axioms KakeyaTwoScale.one_le_ballCoordinateCount
#print axioms KakeyaTwoScale.two_paths_count_lower
