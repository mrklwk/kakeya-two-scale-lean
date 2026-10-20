module
public import KakeyaTwoScale.WholeCellSelection
public import Mathlib.MeasureTheory.Function.Floor

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

def cellAnchor {n : ℕ} (r : ℝ) (k : Fin n → ℤ) : Fin n → ℝ := fun i => r*k i

def safeCellParents {n : ℕ} {P : Type*} (parents : Finset P)
    (bP vP : P → (Fin n → ℝ)) (r : ℝ) (k : Fin n → ℤ) (t : ℝ) : Finset P :=
  parents.filter fun p => dist (cellAnchor r k) (segmentPoint (bP p) (vP p) t) ≤ 3*r

theorem measurable_gridRound {n : ℕ} (r : ℝ) : Measurable (gridRound (n:=n) r) := by
  unfold gridRound gridIndex
  apply Measurable.of_eval
  intro i
  have hd : Measurable (fun x : Fin n → ℝ => x i / r) :=
    (measurable_pi_apply i).div measurable_const
  have hf : Measurable (fun x : Fin n → ℝ => (⌊x i / r⌋ : ℤ)) :=
    Int.measurable_floor.comp hd
  have hc : Measurable (fun x : Fin n → ℝ => (⌊x i / r⌋ : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z:ℝ))).comp hf
  exact measurable_const.mul hc

theorem measurable_safeCellWeight {n : ℕ} {P : Type*} (parents : Finset P)
    (bP vP : P → (Fin n → ℝ)) (b v : Fin n → ℝ) (u r : ℝ) :
    Measurable (fun t => u*(safeCellParents parents bP vP r
      (gridIndex r (segmentPoint b v t)) t).card) := by
  let sets := fun p => {t : ℝ | dist (gridRound r (segmentPoint b v t))
    (segmentPoint (bP p) (vP p) t) ≤ 3*r}
  have hm : ∀ p ∈ parents, MeasurableSet (sets p) := by
    intro p _
    apply measurableSet_le _ measurable_const
    exact ((measurable_gridRound r).comp
      (continuous_const.add (continuous_id.smul continuous_const)).measurable).dist
      (continuous_const.add (continuous_id.smul continuous_const)).measurable
  have he : (fun t => u*(safeCellParents parents bP vP r
      (gridIndex r (segmentPoint b v t)) t).card) = weightedOverlap parents sets (fun _ => u) := by
    funext t
    have hs : weightedOverlap parents sets (fun _ => u) t =
        ∑ p ∈ safeCellParents parents bP vP r (gridIndex r (segmentPoint b v t)) t, u := by
      simp only [weightedOverlap, safeCellParents, Finset.sum_filter, sets, Set.indicator]
      rfl
    rw [hs]
    simp [mul_comm]
  rw [he]
  exact measurable_weightedOverlap parents sets _ hm

/-- A concrete measurable whole-cell selection. We use a sufficient anchor
criterion and radius-4r parents, so no uncountable containment predicate is
silently assumed measurable. The original parent family remains fixed. -/
def safeRetainedHeights {n : ℕ} {P : Type*} (parents : Finset P)
    (bP vP : P → (Fin n → ℝ)) (b v : Fin n → ℝ) (u r M : ℝ) (I : Set ℝ) : Set ℝ :=
  I ∩ {t | M ≤ u*(safeCellParents parents bP vP r (gridIndex r (segmentPoint b v t)) t).card}

theorem measurableSet_safeRetainedHeights {n : ℕ} {P : Type*} (parents : Finset P)
    (bP vP : P → (Fin n → ℝ)) (b v : Fin n → ℝ) (u r M : ℝ)
    {I : Set ℝ} (hI : MeasurableSet I) :
    MeasurableSet (safeRetainedHeights parents bP vP b v u r M I) :=
  hI.inter (measurableSet_le measurable_const (measurable_safeCellWeight parents bP vP b v u r))

/-- Every rounded assigned parent passes the sufficient criterion. Thus using
it does not invalidate the original-capacity low-cell deletion estimate. -/
theorem rounded_parent_mem_safeCellParents {n : ℕ} {P : Type*}
    (parents : Finset P) (bP vP : P → (Fin n → ℝ)) (b v : Fin n → ℝ)
    {r : ℝ} (hr : 0 < r) {p : P} (hp : p ∈ parents)
    (hb : bP p = gridRound r b) (hv : vP p = gridRound r v)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    p ∈ safeCellParents parents bP vP r (gridIndex r (segmentPoint b v t)) t := by
  apply Finset.mem_filter.mpr
  refine ⟨hp,?_⟩
  change dist (gridRound r (segmentPoint b v t)) (segmentPoint (bP p) (vP p) t) ≤ 3*r
  have h₁ := dist_gridRound_le hr (segmentPoint b v t)
  have h₂ := segmentPoint_dist_le b v (bP p) (vP p) r t ht
    (by rw [hb]; exact dist_gridRound_le hr b) (by rw [hv]; exact dist_gridRound_le hr v)
  have h₃ := dist_triangle (gridRound r (segmentPoint b v t))
    (segmentPoint b v t) (segmentPoint (bP p) (vP p) t)
  rw [dist_comm (gridRound r (segmentPoint b v t)) (segmentPoint b v t)] at h₃
  linarith

theorem safeCellParents_cover_whole_cell {n : ℕ} {P : Type*}
    (parents : Finset P) (bP vP : P → (Fin n → ℝ)) {r : ℝ} (hr : 0 < r)
    (k : Fin n → ℤ) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    {p : P} (hp : p ∈ safeCellParents parents bP vP r k t) :
    gridCell r k ⊆ (fun x => (t,x)) ⁻¹' horizontalTube (bP p) (vP p) (4*r) := by
  intro x hx
  have hidx := (mem_gridCell_iff hr x k).mp hx
  have ha : gridRound r x = cellAnchor r k := by unfold gridRound; rw [hidx]; rfl
  have h₁ := dist_gridRound_le hr x
  rw [ha] at h₁
  have h₂ := (Finset.mem_filter.mp hp).2
  refine ⟨ht,?_⟩
  have h₃ := dist_triangle x (cellAnchor r k) (segmentPoint (bP p) (vP p) t)
  change dist x (segmentPoint (bP p) (vP p) t) ≤ 4*r
  linarith

/-- The measurable sufficient selection implies the source's full-cell
high-overlap condition for the same fixed radius-4r tubes. -/
theorem safeRetainedHeights_high_overlap {n : ℕ} {P : Type*}
    (parents : Finset P) (bP vP : P → (Fin n → ℝ)) (b v : Fin n → ℝ)
    (u r M : ℝ) (hu : 0 ≤ u) (hr : 0 < r) {I : Set ℝ}
    (hunit : I ⊆ Set.Icc 0 1) {t : ℝ}
    (ht : t ∈ safeRetainedHeights parents bP vP b v u r M I)
    {x : Fin n → ℝ} (hx : x ∈ gridCell r (gridIndex r (segmentPoint b v t))) :
    M ≤ weightedOverlap parents (fun p => horizontalTube (bP p) (vP p) (4*r)) (fun _ => u) (t,x) := by
  let tubes := fun p => horizontalTube (bP p) (vP p) (4*r)
  have hsub : safeCellParents parents bP vP r (gridIndex r (segmentPoint b v t)) t ⊆
      fullCellParents parents tubes (gridCell r (gridIndex r (segmentPoint b v t))) t := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,
      safeCellParents_cover_whole_cell parents bP vP hr _ (hunit ht.1) hp⟩
  have hcard : ((safeCellParents parents bP vP r (gridIndex r (segmentPoint b v t)) t).card : ℝ) ≤
      (fullCellParents parents tubes (gridCell r (gridIndex r (segmentPoint b v t))) t).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact ht.2.trans ((mul_le_mul_of_nonneg_left hcard hu).trans
    (fullCellWeight_le_overlap parents tubes u hu _ t hx))
/-- Volume inside the fixed parent/high-overlap intersection for the explicitly
constructed measurable retained heights. No whole-cell hypothesis remains. -/
theorem safe_retained_parent_volume {n : ℕ} {P : Type*}
    (parents : Finset P) (bP vP : P → (Fin n → ℝ)) (b v : Fin n → ℝ)
    (u r M : ℝ) (hu : 0 ≤ u) (hr : 0 < r) {I : Set ℝ}
    (hI : MeasurableSet I) (hunit : I ⊆ Set.Icc (0:ℝ) 1) {p : P} (hp : p ∈ parents)
    (hb : bP p = gridRound r b) (hv : vP p = gridRound r v) :
    ENNReal.ofReal r ^ n * volume (safeRetainedHeights parents bP vP b v u r M I) ≤
      volume (horizontalTube (bP p) (vP p) (4*r) ∩
        {z | M ≤ weightedOverlap parents (fun p => horizontalTube (bP p) (vP p) (4*r)) (fun _ => u) z}) := by
  let tubes := fun p => horizontalTube (bP p) (vP p) (4*r)
  let E := tubes p ∩ {z | M ≤ weightedOverlap parents tubes (fun _ => u) z}
  let J := safeRetainedHeights parents bP vP b v u r M I
  have hE : MeasurableSet E := (measurableSet_horizontalTube _ _ _).inter
    (measurableSet_le measurable_const
      (measurable_weightedOverlap parents tubes _ (fun p _ => measurableSet_horizontalTube _ _ _)))
  have hJ : MeasurableSet J := measurableSet_safeRetainedHeights parents bP vP b v u r M hI
  rw [Measure.volume_eq_prod]
  apply volume_lower_of_whole_cells volume volume E hE J hJ
    (fun t => gridCell r (gridIndex r (segmentPoint b v t))) (ENNReal.ofReal r ^ n)
  · intro t _
    exact le_of_eq (volume_gridCell r _).symm
  · intro t ht x hx
    refine ⟨?_,safeRetainedHeights_high_overlap parents bP vP b v u r M hu hr hunit ht hx⟩
    exact safeCellParents_cover_whole_cell parents bP vP hr _ (hunit ht.1)
      (rounded_parent_mem_safeCellParents parents bP vP b v hr hp hb hv (hunit ht.1)) hx

/-- Actual-grid low-cell loss: all covering and immutable-assignment conditions
are discharged by the constructed rounded parents. -/
theorem safe_low_children_mass {n : ℕ} {Child P : Type*}
    [DecidableEq Child] [DecidableEq P] (F : FixedParents Child P)
    (b v : Child → (Fin n → ℝ)) (bP vP : P → (Fin n → ℝ))
    {r : ℝ} (hr : 0 < r) (M t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hb : ∀ x ∈ F.children, bP (F.assign x) = gridRound r (b x))
    (hv : ∀ x ∈ F.children, vP (F.assign x) = gridRound r (v x))
    (D : Finset Child) (hD : D ⊆ F.children)
    (hlow : ∀ x ∈ D, F.weight*(safeCellParents F.parents bP vP r
      (gridIndex r (segmentPoint (b x) (v x) t)) t).card ≤ M) :
    F.fineCellVolume*D.card ≤ 2*M*(F.coarseCellVolume*
      (D.image (fun x => gridIndex r (segmentPoint (b x) (v x) t))).card) := by
  let idx := fun x => gridIndex r (segmentPoint (b x) (v x) t)
  let cells := D.image idx
  let selected := fun k => D.filter (fun x => idx x = k)
  have hcard : (D.card : ℝ) = ∑ k ∈ cells, ((selected k).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image idx D
  rw [hcard, Finset.mul_sum]
  apply F.low_cells_loss cells selected (fun k => safeCellParents F.parents bP vP r k t) M
  · intro k _
    exact (Finset.filter_subset _ _).trans hD
  · intro k _
    exact Finset.filter_subset _ _
  · intro k _ x hx
    obtain ⟨hx,hidx⟩ := Finset.mem_filter.mp hx
    rw [← hidx]
    exact rounded_parent_mem_safeCellParents F.parents bP vP (b x) (v x) hr
      (F.assigned x (hD hx)) (hb x (hD hx)) (hv x (hD hx)) ht
  · intro k hk
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
    exact hlow x hx

/-- The occupied-cell factor is genuine horizontal Lebesgue volume, not a
formal proxy. The physical cell volume in F must match r^n. -/
theorem safe_low_children_volume {n : ℕ} {Child P : Type*}
    [DecidableEq Child] [DecidableEq P] (F : FixedParents Child P)
    (b v : Child → (Fin n → ℝ)) (bP vP : P → (Fin n → ℝ))
    {r : ℝ} (hr : 0 < r) (hscale : F.coarseCellVolume = r^n)
    (M t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hb : ∀ x ∈ F.children, bP (F.assign x) = gridRound r (b x))
    (hv : ∀ x ∈ F.children, vP (F.assign x) = gridRound r (v x))
    (D : Finset Child) (hD : D ⊆ F.children)
    (hlow : ∀ x ∈ D, F.weight*(safeCellParents F.parents bP vP r
      (gridIndex r (segmentPoint (b x) (v x) t)) t).card ≤ M) :
    F.fineCellVolume*D.card ≤ 2*M*volume.real
      (⋃ k ∈ D.image (fun x => gridIndex r (segmentPoint (b x) (v x) t)), gridCell r k) := by
  have hvol : volume.real
      (⋃ k ∈ D.image (fun x => gridIndex r (segmentPoint (b x) (v x) t)), gridCell r k) =
      F.coarseCellVolume*(D.image (fun x => gridIndex r (segmentPoint (b x) (v x) t))).card := by
    rw [Measure.real, volume_gridCell_union hr]
    simp [hscale, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le, mul_comm]
  rw [hvol]
  exact safe_low_children_mass F b v bP vP hr M t ht hb hv D hD hlow

end KakeyaTwoScale
#print axioms KakeyaTwoScale.measurableSet_safeRetainedHeights
#print axioms KakeyaTwoScale.rounded_parent_mem_safeCellParents
#print axioms KakeyaTwoScale.safeRetainedHeights_high_overlap

#print axioms KakeyaTwoScale.safe_low_children_volume

#print axioms KakeyaTwoScale.safe_retained_parent_volume
