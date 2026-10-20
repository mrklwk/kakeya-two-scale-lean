module
public import KakeyaTwoScale.SharedSpatialOccurrences

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Dependent start families: different physical parents can have different
lengths and endpoint starts. Counts are deduplicated before summing. -/
theorem variable_child_record_bound {T P : Type*} [DecidableEq T] [DecidableEq P]
    (Y Z : Finset T) (parent : T → P) (start : T → ℝ) (starts : P → Finset ℝ)
    (hZY : Z ⊆ Y) (hmem : ∀ y ∈ Z, start y ∈ starts (parent y))
    {X : ℝ} (hcount : ∀ t ∈ Y.image parent, ((starts t).card:ℝ) ≤ X) :
    ((Z.image (fun y => (parent y,start y))).card:ℝ) ≤ X*((Y.image parent).card:ℝ) := by
  classical
  let S := (Y.image parent).biUnion (fun t => (starts t).image (fun a => (t,a)))
  have hsub : Z.image (fun y => (parent y,start y)) ⊆ S := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_biUnion.mpr ⟨parent y,Finset.mem_image_of_mem parent (hZY hy),
      Finset.mem_image_of_mem (fun a => (parent y,a)) (hmem y hy)⟩
  have hcard : S.card ≤ ∑ t ∈ Y.image parent, (starts t).card := by
    exact (Finset.card_biUnion_le).trans (Finset.sum_le_sum (fun _ _ => Finset.card_image_le))
  have hc : ((Z.image (fun y => (parent y,start y))).card:ℝ) ≤
      ∑ t ∈ Y.image parent, ((starts t).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans hcard
  exact hc.trans (by simpa [mul_comm] using Finset.sum_le_sum hcount)

theorem variable_child_origin_bound {T P G : Type*} [DecidableEq T] [DecidableEq P]
    [DecidableEq G] (Y Z : Finset T) (parent : T → P) (origin : P → G)
    (start : T → ℝ) (starts : P → Finset ℝ)
    (hZY : Z ⊆ Y) (hmem : ∀ y ∈ Z, start y ∈ starts (parent y))
    {X : ℝ} (hcount : ∀ t ∈ Y.image parent, ((starts t).card:ℝ) ≤ X) (g : G) :
    (((Z.filter fun y => origin (parent y)=g).image (fun y => (parent y,start y))).card:ℝ) ≤
      X*(((Y.filter fun y => origin (parent y)=g).image parent).card:ℝ) := by
  apply variable_child_record_bound _ _ parent start starts
  · intro y hy
    obtain ⟨hy,hg⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hZY hy,hg⟩
  · intro y hy
    exact hmem y (Finset.mem_filter.mp hy).1
  · intro t ht
    exact hcount t (Finset.image_subset_image (Finset.filter_subset _ _) ht)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.variable_child_record_bound
#print axioms KakeyaTwoScale.variable_child_origin_bound
