module
public import KakeyaTwoScale.RoundedParentWeightedBrush
public import KakeyaTwoScale.SafeParentDeletion

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Rounding changes normalized graph directions by O(rho), with no slope
bound needed for this estimate. -/
theorem graphUnitDirection_round_dist {n : ℕ} (i : Fin (n+1)) (v : Fin n → ℝ)
    (r : ℝ) (hr : 0 < r) :
    dist (graphUnitDirection i v) (graphUnitDirection i (gridRound r v)) ≤ 2*(n+2:ℝ)*r := by
  have hnorm : 1 ≤ ‖euclideanUnsplit i (1,v)‖ := by
    simpa [Real.norm_eq_abs,graphVector_height] using PiLp.norm_apply_le (euclideanUnsplit i (1,v)) i
  have hn := normalize_dist_le (euclideanUnsplit i (1,v)) (euclideanUnsplit i (1,gridRound r v))
    hnorm (norm_pos_iff.mpr (graphVector_ne_zero i _))
  have hd := unsplit_same_height_dist i v (gridRound r v) 1
  have hg := mul_le_mul_of_nonneg_left (dist_gridRound_le hr v) (show 0 ≤ (n+2:ℝ) by positivity)
  change dist (graphUnitDirection i v) (graphUnitDirection i (gridRound r v)) ≤ _ at hn
  nlinarith

/-- Plane concentration survives direction rounding, including the purely
normal projection boundary. -/
theorem rounded_graph_plane_concentration {n : ℕ} (i : Fin (n+1))
    (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))))
    (v : Fin n → ℝ) (r C : ℝ) (hr : 0 < r)
    (ha : planeAngle H (graphUnitDirection i v) ≤ C*r) :
    planeAngle H (graphUnitDirection i (gridRound r v)) ≤
      (Real.pi/2)*(C+2*(n+2:ℝ))*r := by
  let u := graphUnitDirection i v
  let z := graphUnitDirection i (gridRound r v)
  have hdiff := Hᗮ.norm_starProjection_apply_le (z-u)
  change ‖normalProjection H (z-u)‖ ≤ ‖z-u‖ at hdiff
  rw [map_sub] at hdiff
  have hnorm := norm_le_norm_add_norm_sub (normalProjection H u) (normalProjection H z)
  rw [norm_sub_rev] at hnorm
  have hu := (planeAngle_speed_bounds H u (graphUnitDirection_norm i v)).2
  have hz := (planeAngle_speed_bounds H z (graphUnitDirection_norm i _)).1
  have hd := graphUnitDirection_round_dist i v r hr
  change dist u z ≤ _ at hd
  rw [dist_eq_norm,norm_sub_rev] at hd
  have hb : (2/Real.pi)*planeAngle H z ≤ (C+2*(n+2:ℝ))*r := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ Real.pi/2 by positivity)
  have he : (Real.pi/2)*(2/Real.pi)=1 := by field_simp
  rw [← mul_assoc,he,one_mul] at hm
  convert hm using 1; ring

/-- A shared fine cell supplies an actual common point in all rounded parents,
without requiring an axis to pass through that point. -/
theorem fine_cell_point_in_rounded_parent {n : ℕ} (b v x : Fin n → ℝ)
    (d r t : ℝ) (hd : 0 < d) (hdr : d ≤ r) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hcell : gridIndex d x=gridIndex d (segmentPoint b v t)) :
    (t,x) ∈ horizontalTube (gridRound r b) (gridRound r v) (4*r) := by
  have hr : 0 < r := hd.trans_le hdr
  have hx : x ∈ gridCell d (gridIndex d (segmentPoint b v t)) := (mem_gridCell_iff hd x _).mpr hcell
  have hdist := gridCell_dist_le hd.le hx (mem_own_gridCell hd (segmentPoint b v t))
  have hround := segmentPoint_dist_le b v (gridRound r b) (gridRound r v) r t ht
    (dist_gridRound_le hr b) (dist_gridRound_le hr v)
  have hh := dist_triangle x (segmentPoint b v t) (segmentPoint (gridRound r b) (gridRound r v) t)
  exact ⟨ht,by linarith⟩

/-- Source-facing real-volume form of the already proved whole-cell capture
for each represented child after short-portion deletion. -/
theorem safe_long_parent_capture_real {n : ℕ} {Child P : Type*}
    [DecidableEq Child] [DecidableEq P] (F : FixedParents Child P)
    (b v : Child → (Fin n → ℝ)) (bP vP : P → (Fin n → ℝ))
    (r M eta : ℝ) (hr : 0 < r) (heta : 0 ≤ eta) (I : Child → Set ℝ)
    (hI : ∀ j ∈ F.children, MeasurableSet (I j))
    (hunit : ∀ j ∈ F.children, I j ⊆ Set.Icc (0:ℝ) 1)
    (hb : ∀ j ∈ F.children, bP (F.assign j) = gridRound r (b j))
    (hv : ∀ j ∈ F.children, vP (F.assign j) = gridRound r (v j))
    {j : Child} (hj : j ∈ F.children)
    (hactive : (F.longPortions volume (fun j =>
      safeRetainedHeights F.parents bP vP (b j) (v j) F.weight r M (I j)) eta j).Nonempty) :
    eta*r^n ≤ volume.real (horizontalTube (bP (F.assign j)) (vP (F.assign j)) (4*r) ∩
      {z | M ≤ weightedOverlap F.parents
        (fun p => horizontalTube (bP p) (vP p) (4*r)) (fun _ => F.weight) z}) := by
  have hh := safe_long_parent_capture F b v bP vP r M eta hr I hI hunit hb hv hj hactive
  have ht := ENNReal.toReal_mono (measure_ne_top_of_subset Set.inter_subset_left
    (horizontalTube_finite (bP (F.assign j)) (vP (F.assign j)) (4*r))) hh
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal hr.le,
    ENNReal.toReal_ofReal heta,mul_comm,Measure.real] using ht

/-- Actual parents represented at one final occupied fine cell. Their common
point, rounded-plane concentration and original-family capture are outputs.
The supplied per-parent cell cap is the earlier arithmetic-pruning bound;
its denominator counts original parent capacity, never surviving capacity. -/
theorem retained_cell_parent_geometry {n : ℕ} {Child P : Type*}
    [DecidableEq Child] [DecidableEq P] (F : FixedParents Child P)
    (b v : Child → Fin n → ℝ) (bP vP : P → Fin n → ℝ)
    (I : Child → Set ℝ) (d r M eta bound C : ℝ)
    (hd : 0 < d) (hdr : d ≤ r) (heta : 0 ≤ eta) (hbound : 0 < bound)
    (hI : ∀ j ∈ F.children, MeasurableSet (I j))
    (hunit : ∀ j ∈ F.children, I j ⊆ Set.Icc (0:ℝ) 1)
    (hb : ∀ j ∈ F.children, bP (F.assign j)=gridRound r (b j))
    (hv : ∀ j ∈ F.children, vP (F.assign j)=gridRound r (v j))
    (t : ℝ) (x : Fin n → ℝ) (i : Fin (n+1))
    (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))))
    (hcap : ∀ p ∈ F.parents,
      ((F.children.filter (fun j => t ∈ I j ∧
        gridIndex d (segmentPoint (b j) (v j) t)=gridIndex d x ∧ F.assign j=p)).card:ℝ) ≤ bound)
    (hplane : ∀ j ∈ F.children, t ∈ I j →
      gridIndex d (segmentPoint (b j) (v j) t)=gridIndex d x →
      planeAngle H (graphUnitDirection i (v j)) ≤ C*r) :
    let J := F.longPortions volume (fun j =>
      safeRetainedHeights F.parents bP vP (b j) (v j) F.weight r M (I j)) eta
    let A := F.children.filter (fun j => t ∈ J j ∧
      gridIndex d (segmentPoint (b j) (v j) t)=gridIndex d x)
    let parents := A.image F.assign
    parents ⊆ F.parents ∧
    F.weight*(A.card:ℝ)/bound ≤ F.weight*parents.card ∧
    (∀ p ∈ parents, (t,x) ∈ horizontalTube (bP p) (vP p) (4*r)) ∧
    (∀ p ∈ parents, planeAngle H (graphUnitDirection i (vP p)) ≤
      (Real.pi/2)*(C+2*(n+2:ℝ))*r) ∧
    (∀ p ∈ parents, eta*r^n ≤ volume.real (horizontalTube (bP p) (vP p) (4*r) ∩
      {z | M ≤ weightedOverlap F.parents (fun p => horizontalTube (bP p) (vP p) (4*r))
        (fun _ => F.weight) z})) := by
  dsimp only
  let J := F.longPortions volume (fun j =>
    safeRetainedHeights F.parents bP vP (b j) (v j) F.weight r M (I j)) eta
  let A := F.children.filter (fun j => t ∈ J j ∧
    gridIndex d (segmentPoint (b j) (v j) t)=gridIndex d x)
  let parents := A.image F.assign
  have hr : 0 < r := hd.trans_le hdr
  have hJI (j) : J j ⊆ I j :=
    (F.longPortions_subset volume _ eta j).trans Set.inter_subset_left
  have hAs : A ⊆ F.children := Finset.filter_subset _ _
  have hPs : parents ⊆ F.parents := by
    intro p hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
    exact F.assigned j (hAs hj)
  refine ⟨hPs,?_,?_,?_,?_⟩
  · apply F.represented_weight bound hbound
    intro p hp
    apply le_trans ?_ (hcap p (hPs hp))
    have hs : A.filter (fun j => F.assign j=p) ⊆
        F.children.filter (fun j => t ∈ I j ∧
          gridIndex d (segmentPoint (b j) (v j) t)=gridIndex d x ∧ F.assign j=p) := by
      intro j hj
      obtain ⟨hj,hp⟩ := Finset.mem_filter.mp hj
      obtain ⟨hj,ht,hcell⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hj,hJI j ht,hcell,hp⟩
    exact_mod_cast Finset.card_le_card hs
  · intro p hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hj,ht,hcell⟩ := Finset.mem_filter.mp hj
    rw [hb j hj,hv j hj]
    exact fine_cell_point_in_rounded_parent (b j) (v j) x d r t hd hdr (hunit j hj (hJI j ht)) hcell.symm
  · intro p hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hj,ht,hcell⟩ := Finset.mem_filter.mp hj
    rw [hv j hj]
    exact rounded_graph_plane_concentration i H (v j) r C hr (hplane j hj (hJI j ht) hcell)
  · intro p hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hj,ht,_⟩ := Finset.mem_filter.mp hj
    exact safe_long_parent_capture_real F b v bP vP r M eta hr heta I hI hunit hb hv hj ⟨t,ht⟩

end KakeyaTwoScale

#print axioms KakeyaTwoScale.graphUnitDirection_round_dist
#print axioms KakeyaTwoScale.rounded_graph_plane_concentration
#print axioms KakeyaTwoScale.fine_cell_point_in_rounded_parent
#print axioms KakeyaTwoScale.safe_long_parent_capture_real

#print axioms KakeyaTwoScale.retained_cell_parent_geometry
