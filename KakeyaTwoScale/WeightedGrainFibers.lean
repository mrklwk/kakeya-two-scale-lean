module
public import KakeyaTwoScale.WeightedGrainSelection

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace WeightedGrain

variable {Tuple Cube : Type*} [DecidableEq Cube]

/-- The selected cubes are exactly the represented cubes whose original
multiplicities belong to the chosen band. -/
theorem selected_image_eq_band (Y : Finset Tuple) (cube : Tuple → Cube) (j : ℕ) :
    (ParentLevel.selected Y cube j).image cube =
      band (Y.image cube) (ParentLevel.capacity Y cube) j := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨ht,hj⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨t,ht,rfl⟩,hj⟩
  · intro hq
    obtain ⟨hq,hj⟩ := Finset.mem_filter.mp hq
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,hj⟩,rfl⟩

/-- A retained cube keeps every original tuple over it, so its actual
multiplicity in the selected tuple set is exactly its original multiplicity. -/
theorem selected_capacity_eq (Y : Finset Tuple) (cube : Tuple → Cube) (j : ℕ)
    {q : Cube} (hq : q ∈ (ParentLevel.selected Y cube j).image cube) :
    ParentLevel.capacity (ParentLevel.selected Y cube j) cube q =
      ParentLevel.capacity Y cube q := by
  unfold ParentLevel.capacity
  rw [ParentLevel.fiber_unchanged Y cube j hq]

/-- Weighted dyadic selection for an actual tuple-to-cube assignment. The
objective uses actual selected multiplicities, not frozen proxy weights.
No localization, tube length, or relative partitioning conclusion is asserted. -/
theorem exists_full_fiber_rpow_selection (Y : Finset Tuple) (cube : Tuple → Cube)
    (B : ℕ) (hbound : ∀ q ∈ Y.image cube, ParentLevel.capacity Y cube q ≤ 2^B) (p : ℝ) :
    ∃ j ≤ B,
      ParentLevel.selected Y cube j ⊆ Y ∧
      (∀ q ∈ (ParentLevel.selected Y cube j).image cube,
        (ParentLevel.selected Y cube j).filter (fun t => cube t=q) =
          Y.filter (fun t => cube t=q)) ∧
      (∀ q ∈ (ParentLevel.selected Y cube j).image cube,
        2^j ≤ ParentLevel.capacity (ParentLevel.selected Y cube j) cube q ∧
        ParentLevel.capacity (ParentLevel.selected Y cube j) cube q < 2^(j+1)) ∧
      (∑ q ∈ Y.image cube, (ParentLevel.capacity Y cube q:ℝ)^p) ≤
        ((B+1:ℕ):ℝ) * ∑ q ∈ (ParentLevel.selected Y cube j).image cube,
          (ParentLevel.capacity (ParentLevel.selected Y cube j) cube q:ℝ)^p := by
  classical
  have hpos : ∀ q ∈ Y.image cube, 0 < ParentLevel.capacity Y cube q := by
    intro q hq
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
    exact ParentLevel.capacity_pos Y cube ht
  obtain ⟨j,hj,hband,hret⟩ := exists_rpow_band (Y.image cube)
    (ParentLevel.capacity Y cube) B hpos hbound p
  refine ⟨j,hj,ParentLevel.selected_subset Y cube j,
    fun _ hq => ParentLevel.fiber_unchanged Y cube j hq,?_,?_⟩
  · intro q hq
    rw [selected_capacity_eq Y cube j hq]
    exact ParentLevel.capacity_band Y cube j hq
  · rw [← selected_image_eq_band] at hret
    have he : (∑ q ∈ (ParentLevel.selected Y cube j).image cube,
        (ParentLevel.capacity (ParentLevel.selected Y cube j) cube q:ℝ)^p) =
        ∑ q ∈ (ParentLevel.selected Y cube j).image cube,
          (ParentLevel.capacity Y cube q:ℝ)^p := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [selected_capacity_eq Y cube j hq]
    rwa [he]

end WeightedGrain
end KakeyaTwoScale
#print axioms KakeyaTwoScale.WeightedGrain.selected_image_eq_band
#print axioms KakeyaTwoScale.WeightedGrain.selected_capacity_eq
#print axioms KakeyaTwoScale.WeightedGrain.exists_full_fiber_rpow_selection
