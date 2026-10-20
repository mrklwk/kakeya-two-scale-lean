module
public import KakeyaTwoScale.ActualBufferedArchive
public import KakeyaTwoScale.BufferedSnapshotAncestry

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale
open BufferedArchiveSnapshot

namespace AmbientBufferedStageData
variable {b c k A B Lh J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]

theorem nextData_snapshot (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a)
    (hb : 1<b) (t : ℕ) (ht : 2≤t) :
    ofState (I.nextData Z hb t ht).W=ofState Z.state :=
  ofState_eq_of_HEq _ _ (by omega) (I.nextData_state_HEq Z hb t ht)

theorem normalized_physical_ancestor (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a) :
    PhysicalAncestor I.δ (ofState I.W) (ofState Z.state) := by
  refine ⟨rfl,Z.tuples_subset,fun y hy j=>(Z.geometry y hy j).trans inter_subset_left,Z.axes,?_⟩
  intro y hy j
  exact (Z.valid.2.2.1 y hy j).trans (I.valid.2.2.1 y (Z.tuples_subset hy) j).symm

end AmbientBufferedStageData
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

/-- Every complete immutable snapshot is an actual physical descendant of
the root, and every earlier snapshot is an ancestor of every later snapshot.
No externally supplied chain or archive is an input. -/
theorem snapshots_physical_ancestry
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    (∀ S∈H.snapshots, PhysicalAncestor I.δ (ofState I.W) S) ∧
    H.snapshots.Pairwise (PhysicalAncestor I.δ) := by
  induction H with
  | zero I P U =>
    change (∀ S∈[ofState I.W], PhysicalAncestor I.δ (ofState I.W) S) ∧ _
    exact ⟨fun _ h=>List.mem_singleton.mp h ▸ PhysicalAncestor.refl _ _,by simp [snapshots]⟩
  | short I P U hs =>
    change (∀ S∈[ofState I.W], PhysicalAncestor I.δ (ofState I.W) S) ∧ _
    exact ⟨fun _ h=>List.mem_singleton.mp h ▸ PhysicalAncestor.refl _ _,by simp [snapshots]⟩
  | last I P U Z =>
    change (∀ S∈[ofState I.W,ofState Z.state], PhysicalAncestor I.δ (ofState I.W) S) ∧
      [ofState I.W,ofState Z.state].Pairwise (PhysicalAncestor I.δ)
    have hz := I.normalized_physical_ancestor Z
    constructor
    · intro S hS
      rcases List.mem_cons.mp hS with rfl | hS
      · exact PhysicalAncestor.refl _ _
      · rcases List.mem_singleton.mp hS with rfl
        exact hz
    · simpa [List.pairwise_cons] using hz
  | next I P U Z hb ht tail ih =>
    change (∀ S∈ofState I.W::tail.snapshots, PhysicalAncestor I.δ (ofState I.W) S) ∧
      (ofState I.W::tail.snapshots).Pairwise (PhysicalAncestor I.δ)
    have hi : ∀ S∈tail.snapshots, PhysicalAncestor I.δ (ofState Z.state) S := by
      simpa only [AmbientBufferedStageData.nextData_delta,AmbientBufferedStageData.nextData_snapshot] using ih.1
    have hh : ∀ S∈tail.snapshots, PhysicalAncestor I.δ (ofState I.W) S :=
      fun S hS=>(I.normalized_physical_ancestor Z).trans (hi S hS)
    refine ⟨?_,List.pairwise_cons.mpr ⟨hh,?_⟩⟩
    · intro S hS
      rcases List.mem_cons.mp hS with rfl | hS
      · exact PhysicalAncestor.refl _ _
      · exact hh S hS
    · simpa only [AmbientBufferedStageData.nextData_delta] using ih.2

/-- Every stored level retains the actual unit axes, original tube identities,
nonempty represented cylinders and same-original disjointness. -/
theorem snapshots_certified
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    ∀ S∈H.snapshots, Certified I.δ I.tube S := by
  induction H with
  | zero I P U =>
    intro S hS
    change S∈[ofState I.W] at hS
    rcases List.mem_singleton.mp hS with rfl
    exact certified_of_valid _ _ _ _ _ _ I.valid I.nonempty
  | short I P U hs =>
    intro S hS
    change S∈[ofState I.W] at hS
    rcases List.mem_singleton.mp hS with rfl
    exact certified_of_valid _ _ _ _ _ _ I.valid I.nonempty
  | last I P U Z =>
    intro S hS
    change S∈[ofState I.W,ofState Z.state] at hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact certified_of_valid _ _ _ _ _ _ I.valid I.nonempty
    · rcases List.mem_singleton.mp hS with rfl
      exact certified_of_valid _ _ _ _ _ _ Z.valid Z.nonempty
  | next I P U Z hb ht tail ih =>
    intro S hS
    change S∈ofState I.W::tail.snapshots at hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact certified_of_valid _ _ _ _ _ _ I.valid I.nonempty
    · simpa only [AmbientBufferedStageData.nextData_delta,AmbientBufferedStageData.nextData_tube] using ih S hS

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.snapshots_physical_ancestry
#print axioms KakeyaTwoScale.ActualBufferedArchive.snapshots_certified
