module
public import KakeyaTwoScale.FiniteIntervalMerge

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

/-- Construct the actual padded-and-merged axis cover, with exact parent
bounds, no gaps added by merging, and no incidence lost at source endpoints. -/
theorem exists_padded_axis_cover (S : Finset (ℝ × ℝ)) {L δ : ℝ}
    (hδ : 0 < δ) (hL : δ ≤ L)
    (hS : ∀ a ∈ S, 0 ≤ a.1 ∧ a.1 ≤ a.2 ∧ a.2 ≤ L) :
    ∃ U : Finset (ℝ × ℝ), U.card ≤ S.card ∧
      (∀ b ∈ U, 0 ≤ b.1 ∧ b.1+δ ≤ b.2 ∧ b.2 ≤ L) ∧
      PairwiseDisjoint (↑U : Set (ℝ × ℝ)) (fun b => Icc b.1 b.2) ∧
      (∀ a ∈ S, ∀ t ∈ Icc a.1 a.2, t ∈ Ioo (0:ℝ) L →
        ∃ b ∈ U, t ∈ Ioo b.1 b.2) ∧
      (∀ b ∈ U, ∀ t ∈ Icc b.1 b.2,
        ∃ a ∈ S, ∃ s ∈ Icc a.1 a.2, |t-s| ≤ δ) := by
  classical
  let V := S.image (paddedAxisInterval L δ)
  have hv : ∀ b ∈ V, 0 ≤ b.1 ∧ b.1+δ ≤ b.2 ∧ b.2 ≤ L := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    exact padded_axis_bounds hδ hL (hS a ha)
  obtain ⟨U,hcard,hvalid,hdis,hcover,hunion⟩ := exists_disjoint_interval_merge V L δ hv
  refine ⟨U,hcard.trans Finset.card_image_le,hvalid,hdis,?_,?_⟩
  · intro a ha t ht hp
    obtain ⟨b,hb,hba,hab⟩ := hcover (paddedAxisInterval L δ a) (Finset.mem_image_of_mem _ ha)
    have hi := padded_axis_incidence hδ ht hp
    exact ⟨b,hb,hba.trans_lt hi.1,hi.2.trans_le hab⟩
  · intro b hb t ht
    obtain ⟨v,hv,htv⟩ := hunion b hb t ht
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨s,hs,hst⟩ := padded_axis_near_source hδ.le (hS a ha).2.1 htv
    exact ⟨a,ha,s,hs,hst⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_padded_axis_cover
