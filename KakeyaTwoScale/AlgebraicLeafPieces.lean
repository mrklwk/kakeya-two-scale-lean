module
public import KakeyaTwoScale.PaddedAxisCover
public import KakeyaTwoScale.AxisCylinderTransport

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- Actual algebraic-leaf transport. The finite interval representation of
an axis-distance sublevel is the EXPLICIT remaining semialgebraic input.
Everything after that representation, including the disjoint long pieces,
parent containment and retention of every original near-variety incidence,
is constructed here. No successor or tube-count conclusion is assumed. -/
theorem exists_algebraic_leaf_pieces {n : ℕ}
    (b u : EuclideanSpace ℝ (Fin n)) (V : Set (EuclideanSpace ℝ (Fin n)))
    (S : Finset (ℝ × ℝ)) {L δ R : ℝ} (hu : ‖u‖=1) (hδ : 0 < δ) (hL : δ ≤ L)
    (hS : ∀ a ∈ S, 0 ≤ a.1 ∧ a.1 ≤ a.2 ∧ a.2 ≤ L)
    (hsafe : ∀ a ∈ S, ∀ s ∈ Icc a.1 a.2,
      ∃ z ∈ V, dist (b+s • u) z ≤ (R+1)*δ)
    (hcover : ∀ t ∈ Ioo (0:ℝ) L,
      (∃ z ∈ V, dist (b+t • u) z ≤ (R+1)*δ) → ∃ a ∈ S, t ∈ Icc a.1 a.2) :
    ∃ U : Finset (ℝ × ℝ), U.card ≤ S.card ∧
      (∀ a ∈ U, 0 ≤ a.1 ∧ δ ≤ a.2-a.1 ∧ a.2 ≤ L) ∧
      PairwiseDisjoint (↑U : Set (ℝ × ℝ)) (fun a => axisCylinder b u a δ) ∧
      (∀ a ∈ U, axisCylinder b u a δ ⊆ flatCylinder b u L δ ∩ thickening ((R+3)*δ) V) ∧
      flatCylinder b u L δ ∩ thickening (R*δ) V ⊆ ⋃ a ∈ U, axisCylinder b u a δ := by
  obtain ⟨U,hcard,hvalid,hdis,hinc,hnear⟩ := exists_padded_axis_cover S hδ hL hS
  refine ⟨U,hcard,?_,?_,?_,?_⟩
  · intro a ha
    exact ⟨(hvalid a ha).1,by linarith [(hvalid a ha).2.1],(hvalid a ha).2.2⟩
  · intro a ha c hc hne
    exact disjoint_axisCylinders b u hu δ (hdis ha hc hne)
  · intro a ha
    apply Set.subset_inter
    · exact axisCylinder_subset_parent b u (hvalid a ha).1 (hvalid a ha).2.2
    · apply axisCylinder_near_variety b u V hu
      intro t ht
      obtain ⟨c,hc,s,hs,hts⟩ := hnear a ha t ht
      obtain ⟨z,hz,hsz⟩ := hsafe c hc s hs
      exact ⟨s,z,hz,hts,hsz⟩
  · intro x hx
    obtain ⟨t,ht0,htL,hi,hn⟩ := hx.1
    obtain ⟨z,hz,hxz⟩ := mem_thickening_iff.mp hx.2
    have htx : dist (b+t • u) x < δ := by simpa [dist_eq_norm,norm_sub_rev] using hn
    have htz : dist (b+t • u) z ≤ (R+1)*δ := by
      have hh := dist_triangle (b+t • u) x z
      linarith
    obtain ⟨a,ha,hta⟩ := hcover t ⟨ht0,htL⟩ ⟨z,hz,htz⟩
    obtain ⟨c,hc,htc⟩ := hinc a ha t hta ⟨ht0,htL⟩
    exact Set.mem_iUnion₂.mpr ⟨c,hc,(mem_axisCylinder_iff b u x c δ).mpr ⟨t,htc,hi,hn⟩⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_algebraic_leaf_pieces
