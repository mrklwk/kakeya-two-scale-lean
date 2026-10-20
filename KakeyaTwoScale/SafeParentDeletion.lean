module
public import KakeyaTwoScale.PortionGridVolume

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- The measurable whole-cell deletion, with its low-cell and volume premises
discharged for the actual removed heights. The comparison volume is the
original coarse-grid union of the complete child axes. -/
theorem safe_retained_mass_volume {n : ℕ} {Child P : Type*}
    [DecidableEq Child] [DecidableEq P] (F : FixedParents Child P)
    (b v : Child → (Fin n → ℝ)) (bP vP : P → (Fin n → ℝ))
    {r : ℝ} (hr : 0 < r) (hscale : F.coarseCellVolume = r^n)
    (M : ℝ) (hM : 0 ≤ M) (I : Child → Set ℝ)
    (hI : ∀ j ∈ F.children, MeasurableSet (I j))
    (hunit : ∀ j ∈ F.children, I j ⊆ Set.Icc (0:ℝ) 1)
    (hb : ∀ j ∈ F.children, bP (F.assign j) = gridRound r (b j))
    (hv : ∀ j ∈ F.children, vP (F.assign j) = gridRound r (v j)) :
    F.portionMass volume I - 2*M*volume.real (occupiedGridRegion F.children b v r
      (fun _ => Set.Icc (0:ℝ) 1)) ≤
      F.portionMass volume (fun j =>
        safeRetainedHeights F.parents bP vP (b j) (v j) F.weight r M (I j)) := by
  let J := fun j => safeRetainedHeights F.parents bP vP (b j) (v j) F.weight r M (I j)
  let D := fun j => I j \ J j
  have hJ (j) (hj : j ∈ F.children) : MeasurableSet (J j) :=
    measurableSet_safeRetainedHeights F.parents bP vP (b j) (v j) F.weight r M (hI j hj)
  have hD (j) (hj : j ∈ F.children) : MeasurableSet (D j) := (hI j hj).diff (hJ j hj)
  have hDs (j) (hj : j ∈ F.children) : D j ⊆ Set.Icc (0:ℝ) 1 :=
    Set.sdiff_subset.trans (hunit j hj)
  have hlow (j) (_hj : j ∈ F.children) (t) (ht : t ∈ D j) :
      F.weight*(safeCellParents F.parents bP vP r
        (gridIndex r (segmentPoint (b j) (v j) t)) t).card ≤ M := by
    have hh : ¬ M ≤ F.weight*(safeCellParents F.parents bP vP r
        (gridIndex r (segmentPoint (b j) (v j) t)) t).card := by
      intro hh
      exact ht.2 ⟨ht.1,hh⟩
    exact (lt_of_not_ge hh).le
  have hloss := safe_low_portion_mass_volume F b v bP vP hr hscale M D hD hDs hb hv hlow
  have hsub : occupiedGridRegion F.children b v r D ⊆
      occupiedGridRegion F.children b v r (fun _ => Set.Icc (0:ℝ) 1) := by
    intro x hx
    obtain ⟨j,hj,ht,hx⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨j,hj,hDs j hj ht,hx⟩
  have hvol := measureReal_mono hsub (occupiedGridRegion_finite_volume F.children b v hr
    (fun _ => Set.Icc (0:ℝ) 1) (fun _ _ => measurableSet_Icc) (fun _ _ => Set.Subset.rfl))
  have hloss' := hloss.trans (mul_le_mul_of_nonneg_left hvol (by positivity : 0 ≤ 2*M))
  have he : F.portionMass volume J + F.portionMass volume D = F.portionMass volume I := by
    unfold FixedParents.portionMass
    rw [← mul_add,← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hfin : volume (I j) ≠ ⊤ := measure_ne_top_of_subset (hunit j hj) (by simp)
    have hh := measureReal_inter_add_sdiff (μ:=volume) (s:=I j) (hJ j hj) hfin
    have hs : I j ∩ J j = J j := Set.inter_eq_right.mpr Set.inter_subset_left
    rwa [hs] at hh
  change F.portionMass volume I - _ ≤ F.portionMass volume J
  linarith

/-- After deleting short portions, every represented fixed parent has actual
high-overlap capture. The high set uses the entire original parent family
and the original common weight, regardless of earlier deletions. -/
theorem safe_long_parent_capture {n : ℕ} {Child P : Type*}
    [DecidableEq Child] [DecidableEq P] (F : FixedParents Child P)
    (b v : Child → (Fin n → ℝ)) (bP vP : P → (Fin n → ℝ))
    (r M eta : ℝ) (hr : 0 < r) (I : Child → Set ℝ)
    (hI : ∀ j ∈ F.children, MeasurableSet (I j))
    (hunit : ∀ j ∈ F.children, I j ⊆ Set.Icc (0:ℝ) 1)
    (hb : ∀ j ∈ F.children, bP (F.assign j) = gridRound r (b j))
    (hv : ∀ j ∈ F.children, vP (F.assign j) = gridRound r (v j))
    {j : Child} (hj : j ∈ F.children)
    (hactive : (F.longPortions volume (fun j =>
      safeRetainedHeights F.parents bP vP (b j) (v j) F.weight r M (I j)) eta j).Nonempty) :
    ENNReal.ofReal r ^ n * ENNReal.ofReal eta ≤
      volume (horizontalTube (bP (F.assign j)) (vP (F.assign j)) (4*r) ∩
        {z | M ≤ weightedOverlap F.parents
          (fun p => horizontalTube (bP p) (vP p) (4*r)) (fun _ => F.weight) z}) := by
  let J := fun j => safeRetainedHeights F.parents bP vP (b j) (v j) F.weight r M (I j)
  have hlen := F.longPortions_mass_of_nonempty volume J eta hactive
  have hsub : F.longPortions volume J eta j ⊆ J j := F.longPortions_subset volume J eta j
  have hfinite : volume (J j) ≠ ⊤ :=
    measure_ne_top_of_subset (Set.inter_subset_left.trans (hunit j hj)) (by simp)
  have hlen' : eta ≤ volume.real (J j) := hlen.trans (measureReal_mono hsub hfinite)
  have hmeasure : ENNReal.ofReal eta ≤ volume (J j) := by
    exact (ENNReal.ofReal_le_iff_le_toReal hfinite).mpr hlen'
  exact (mul_le_mul_right hmeasure _).trans
    (safe_retained_parent_volume F.parents bP vP (b j) (v j) F.weight r M
      F.weight_pos.le hr (hI j hj) (hunit j hj) (F.assigned j hj) (hb j hj) (hv j hj))

/-- Exact measured budget for the concrete whole-cell deletion followed by
short-portion deletion; all low-cell integrability and coverage are proved. -/
theorem safe_long_mass_volume {n : ℕ} {Child P : Type*}
    [DecidableEq Child] [DecidableEq P] (F : FixedParents Child P)
    (b v : Child → (Fin n → ℝ)) (bP vP : P → (Fin n → ℝ))
    {r : ℝ} (hr : 0 < r) (hscale : F.coarseCellVolume = r^n)
    (M eta : ℝ) (hM : 0 ≤ M) (heta : 0 ≤ eta) (I : Child → Set ℝ)
    (hI : ∀ j ∈ F.children, MeasurableSet (I j))
    (hunit : ∀ j ∈ F.children, I j ⊆ Set.Icc (0:ℝ) 1)
    (hb : ∀ j ∈ F.children, bP (F.assign j) = gridRound r (b j))
    (hv : ∀ j ∈ F.children, vP (F.assign j) = gridRound r (v j)) :
    F.portionMass volume I - 2*M*volume.real (occupiedGridRegion F.children b v r
      (fun _ => Set.Icc (0:ℝ) 1)) - eta*F.fineCellVolume*F.children.card ≤
      F.portionMass volume (F.longPortions volume (fun j =>
        safeRetainedHeights F.parents bP vP (b j) (v j) F.weight r M (I j)) eta) := by
  have hs := safe_retained_mass_volume F b v bP vP hr hscale M hM I hI hunit hb hv
  have hl := F.longPortions_mass_lower volume (fun j =>
    safeRetainedHeights F.parents bP vP (b j) (v j) F.weight r M (I j)) eta heta
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.safe_retained_mass_volume
#print axioms KakeyaTwoScale.safe_long_parent_capture
#print axioms KakeyaTwoScale.safe_long_mass_volume
