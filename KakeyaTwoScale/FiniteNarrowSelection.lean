module
public import KakeyaTwoScale.NarrowSelectionMass
public import KakeyaTwoScale.PlaneAngle

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale
open Classical
variable {J : Type*}

/-- The complete original incidence pattern, prior to any portion deletion. -/
def finiteIncidentPattern {X : Type*}  (G : Finset J) (T : J → Set X) (x : X) : Finset (J) :=
  G.filter (fun j => x ∈ T j)

theorem measurable_finiteIncidentPattern [Countable J] {X : Type*} [MeasurableSpace X]
    (G : Finset J) (T : J → Set X) (hT : ∀ j, MeasurableSet (T j)) :
    Measurable (finiteIncidentPattern G T) := by
  apply measurable_finset_iff.mpr
  intro j
  by_cases hj : j∈G
  · simpa [finiteIncidentPattern,hj] using (hT j)
  · simp [finiteIncidentPattern,hj]

/-- Every property of the finite original incidence pattern is measurable,
even when its definition quantifies over all linear subspaces. -/
theorem measurableSet_finiteIncidentPattern_property [Countable J] {X : Type*} [MeasurableSpace X]
    (G : Finset J) (T : J → Set X) (hT : ∀ j, MeasurableSet (T j)) (P : Finset (J) → Prop) :
    MeasurableSet {x | P (finiteIncidentPattern G T x)} := by
  exact (measurableSet_setOfPred.mpr (measurable_of_countable P)).preimage
    (measurable_finiteIncidentPattern G T hT)

def finiteNarrowPattern {d : ℕ} (u : J → EuclideanSpace ℝ (Fin d))
    (k : ℕ) (r : ℝ) (S : Finset (J)) : Prop :=
  ∃ H : Submodule ℝ (EuclideanSpace ℝ (Fin d)), Module.finrank ℝ H=k ∧
    S.card ≤ 2*(S.filter (fun j => planeAngle H (u j) ≤ r)).card

/-- One plane is selected for each finite incidence pattern. This finite
choice removes the need for a measurable selection theorem on a Grassmannian. -/
def finiteNarrowPatternPlane {d : ℕ} (u : J → EuclideanSpace ℝ (Fin d))
    (k : ℕ) (r : ℝ) (S : Finset (J)) : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  if h : finiteNarrowPattern u k r S then Classical.choose h else ⊥

theorem finiteNarrowPatternPlane_spec {d : ℕ} (u : J → EuclideanSpace ℝ (Fin d))
    (k : ℕ) (r : ℝ) (S : Finset (J)) (h : finiteNarrowPattern u k r S) :
    Module.finrank ℝ (finiteNarrowPatternPlane u k r S)=k ∧
    S.card ≤ 2*(S.filter (fun j => planeAngle (finiteNarrowPatternPlane u k r S) (u j) ≤ r)).card := by
  have he : finiteNarrowPatternPlane u k r S = Classical.choose h := dite_eq_left h
  rw [he]
  exact Classical.choose_spec h

/-- Actual retained height sets. The chosen plane depends only on the whole
original cell-incidence pattern, so all retained directions in one cell use
the same plane and later deletions preserve this concentration. -/
def finiteNarrowGridHeights {n : ℕ} (G : Finset J) (b v : J → Fin n → ℝ)
    (u : J → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) (d r : ℝ) (j : J) : Set ℝ :=
  {t | t ∈ Set.Icc (0:ℝ) 1 ∧
    let S := finiteIncidentPattern G (fun l => gridPortion (b l) (v l) d (Set.Icc (0:ℝ) 1))
      (t,segmentPoint (b j) (v j) t)
    finiteNarrowPattern u k r S ∧ planeAngle (finiteNarrowPatternPlane u k r S) (u j) ≤ r}

theorem measurableSet_finiteNarrowGridHeights [Countable J] {n : ℕ} (G : Finset J) (b v : J → Fin n → ℝ)
    (u : J → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) (d r : ℝ) (j : J) :
    MeasurableSet (finiteNarrowGridHeights G b v u k d r j) := by
  have hm := measurableSet_finiteIncidentPattern_property G
    (fun l => gridPortion (b l) (v l) d (Set.Icc (0:ℝ) 1))
    (fun l => measurableSet_gridPortion (b l) (v l) d _ measurableSet_Icc)
    (fun S => finiteNarrowPattern u k r S ∧ planeAngle (finiteNarrowPatternPlane u k r S) (u j) ≤ r)
  have hp : Measurable (fun t : ℝ => (t,segmentPoint (b j) (v j) t)) :=
    measurable_id.prodMk (continuous_const.add (continuous_id.smul continuous_const)).measurable
  exact measurableSet_Icc.inter (hm.preimage hp)

/-- Incidence patterns are constant on each whole horizontal grid cell. -/
theorem finiteIncidentPattern_grid_cell {n : ℕ} (G : Finset J) (b v : J → Fin n → ℝ)
    (d t : ℝ) (x y : Fin n → ℝ) (hxy : gridIndex d x=gridIndex d y) :
    finiteIncidentPattern G (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) (t,x)=
      finiteIncidentPattern G (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) (t,y) := by
  ext j
  simp [finiteIncidentPattern,gridPortion,hxy]

/-- At every narrow cell, the actually retained measurable portions keep at
least half the original incident segments. -/
theorem finiteNarrowGrid_retained_card {n : ℕ} (G : Finset J) (b v : J → Fin n → ℝ)
    (u : J → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) (d r t : ℝ) (x : Fin n → ℝ)
    (hn : finiteNarrowPattern u k r
      (finiteIncidentPattern G (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) (t,x))) :
    (finiteIncidentPattern G (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) (t,x)).card ≤
      2*(finiteIncidentPattern G (fun j => gridPortion (b j) (v j) d
        (finiteNarrowGridHeights G b v u k d r j)) (t,x)).card := by
  let S := finiteIncidentPattern G (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) (t,x)
  have hs := (finiteNarrowPatternPlane_spec u k r S hn).2
  apply hs.trans
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro j hj
  obtain ⟨hj,ha⟩ := Finset.mem_filter.mp hj
  have hj' : j∈G ∧ t ∈ Set.Icc (0:ℝ) 1 ∧
      gridIndex d x=gridIndex d (segmentPoint (b j) (v j) t) := by
    simpa [S,finiteIncidentPattern,gridPortion] using hj
  have he := finiteIncidentPattern_grid_cell G b v d t x (segmentPoint (b j) (v j) t) hj'.2.2
  apply Finset.mem_filter.mpr
  refine ⟨hj'.1,?_,hj'.2.2⟩
  change t ∈ Set.Icc (0:ℝ) 1 ∧ _
  refine ⟨hj'.2.1,?_⟩
  simpa only [← he] using (And.intro hn ha)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.measurable_finiteIncidentPattern
#print axioms KakeyaTwoScale.measurableSet_finiteIncidentPattern_property
#print axioms KakeyaTwoScale.finiteNarrowPatternPlane_spec
#print axioms KakeyaTwoScale.measurableSet_finiteNarrowGridHeights

#print axioms KakeyaTwoScale.finiteIncidentPattern_grid_cell
#print axioms KakeyaTwoScale.finiteNarrowGrid_retained_card
