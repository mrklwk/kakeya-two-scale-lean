module
public import KakeyaTwoScale.GridMultiplicity
public import KakeyaTwoScale.PlaneAngle

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- The complete original incidence pattern, prior to any portion deletion. -/
def incidentPattern {X : Type*} {N : ℕ} (T : Fin N → Set X) (x : X) : Finset (Fin N) :=
  Finset.univ.filter (fun j => x ∈ T j)

theorem measurable_incidentPattern {X : Type*} [MeasurableSpace X] {N : ℕ}
    (T : Fin N → Set X) (hT : ∀ j, MeasurableSet (T j)) :
    Measurable (incidentPattern T) := by
  apply measurable_finset_iff.mpr
  intro j
  simpa [incidentPattern] using (hT j)

/-- Every property of the finite original incidence pattern is measurable,
even when its definition quantifies over all linear subspaces. -/
theorem measurableSet_incidentPattern_property {X : Type*} [MeasurableSpace X] {N : ℕ}
    (T : Fin N → Set X) (hT : ∀ j, MeasurableSet (T j)) (P : Finset (Fin N) → Prop) :
    MeasurableSet {x | P (incidentPattern T x)} := by
  exact (measurableSet_setOfPred.mpr (measurable_of_countable P)).preimage
    (measurable_incidentPattern T hT)

def narrowPattern {d N : ℕ} (u : Fin N → EuclideanSpace ℝ (Fin d))
    (k : ℕ) (r : ℝ) (S : Finset (Fin N)) : Prop :=
  ∃ H : Submodule ℝ (EuclideanSpace ℝ (Fin d)), Module.finrank ℝ H=k ∧
    S.card ≤ 2*(S.filter (fun j => planeAngle H (u j) ≤ r)).card

/-- One plane is selected for each finite incidence pattern. This finite
choice removes the need for a measurable selection theorem on a Grassmannian. -/
def narrowPatternPlane {d N : ℕ} (u : Fin N → EuclideanSpace ℝ (Fin d))
    (k : ℕ) (r : ℝ) (S : Finset (Fin N)) : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  if h : narrowPattern u k r S then Classical.choose h else ⊥

theorem narrowPatternPlane_spec {d N : ℕ} (u : Fin N → EuclideanSpace ℝ (Fin d))
    (k : ℕ) (r : ℝ) (S : Finset (Fin N)) (h : narrowPattern u k r S) :
    Module.finrank ℝ (narrowPatternPlane u k r S)=k ∧
    S.card ≤ 2*(S.filter (fun j => planeAngle (narrowPatternPlane u k r S) (u j) ≤ r)).card := by
  have he : narrowPatternPlane u k r S = Classical.choose h := dite_eq_left h
  rw [he]
  exact Classical.choose_spec h

/-- Actual retained height sets. The chosen plane depends only on the whole
original cell-incidence pattern, so all retained directions in one cell use
the same plane and later deletions preserve this concentration. -/
def narrowGridHeights {n N : ℕ} (b v : Fin N → Fin n → ℝ)
    (u : Fin N → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) (d r : ℝ) (j : Fin N) : Set ℝ :=
  {t | t ∈ Set.Icc (0:ℝ) 1 ∧
    let S := incidentPattern (fun l => gridPortion (b l) (v l) d (Set.Icc (0:ℝ) 1))
      (t,segmentPoint (b j) (v j) t)
    narrowPattern u k r S ∧ planeAngle (narrowPatternPlane u k r S) (u j) ≤ r}

theorem measurableSet_narrowGridHeights {n N : ℕ} (b v : Fin N → Fin n → ℝ)
    (u : Fin N → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) (d r : ℝ) (j : Fin N) :
    MeasurableSet (narrowGridHeights b v u k d r j) := by
  have hm := measurableSet_incidentPattern_property
    (fun l => gridPortion (b l) (v l) d (Set.Icc (0:ℝ) 1))
    (fun l => measurableSet_gridPortion (b l) (v l) d _ measurableSet_Icc)
    (fun S => narrowPattern u k r S ∧ planeAngle (narrowPatternPlane u k r S) (u j) ≤ r)
  have hp : Measurable (fun t : ℝ => (t,segmentPoint (b j) (v j) t)) :=
    measurable_id.prodMk (continuous_const.add (continuous_id.smul continuous_const)).measurable
  exact measurableSet_Icc.inter (hm.preimage hp)

/-- Incidence patterns are constant on each whole horizontal grid cell. -/
theorem incidentPattern_grid_cell {n N : ℕ} (b v : Fin N → Fin n → ℝ)
    (d t : ℝ) (x y : Fin n → ℝ) (hxy : gridIndex d x=gridIndex d y) :
    incidentPattern (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) (t,x)=
      incidentPattern (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) (t,y) := by
  ext j
  simp [incidentPattern,gridPortion,hxy]

/-- At every narrow cell, the actually retained measurable portions keep at
least half the original incident segments. -/
theorem narrowGrid_retained_card {n N : ℕ} (b v : Fin N → Fin n → ℝ)
    (u : Fin N → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) (d r t : ℝ) (x : Fin n → ℝ)
    (hn : narrowPattern u k r
      (incidentPattern (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) (t,x))) :
    (incidentPattern (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) (t,x)).card ≤
      2*(incidentPattern (fun j => gridPortion (b j) (v j) d
        (narrowGridHeights b v u k d r j)) (t,x)).card := by
  let S := incidentPattern (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) (t,x)
  have hs := (narrowPatternPlane_spec u k r S hn).2
  apply hs.trans
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro j hj
  obtain ⟨hj,ha⟩ := Finset.mem_filter.mp hj
  have hj' : t ∈ Set.Icc (0:ℝ) 1 ∧
      gridIndex d x=gridIndex d (segmentPoint (b j) (v j) t) := by
    simpa [S,incidentPattern,gridPortion] using hj
  have he := incidentPattern_grid_cell b v d t x (segmentPoint (b j) (v j) t) hj'.2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_,hj'.2⟩
  change t ∈ Set.Icc (0:ℝ) 1 ∧ _
  refine ⟨hj'.1,?_⟩
  simpa only [← he] using (And.intro hn ha)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.measurable_incidentPattern
#print axioms KakeyaTwoScale.measurableSet_incidentPattern_property
#print axioms KakeyaTwoScale.narrowPatternPlane_spec
#print axioms KakeyaTwoScale.measurableSet_narrowGridHeights

#print axioms KakeyaTwoScale.incidentPattern_grid_cell
#print axioms KakeyaTwoScale.narrowGrid_retained_card
