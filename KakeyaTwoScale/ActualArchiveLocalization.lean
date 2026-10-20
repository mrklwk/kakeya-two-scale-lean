module
public import KakeyaTwoScale.ActualPolynomialArchive
public import KakeyaTwoScale.GrainOriginalMultiplicity

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace BufferedArchiveSnapshot
variable {k : ℕ} {T C O : Type}

def Localized (δ : ℝ) (cube : T→C) (S : BufferedArchiveSnapshot k T C O) : Prop :=
  ∀ y∈S.state.tuples, ∀ j, S.state.geometry δ j (S.state.parent y j) ⊆
    ball (S.state.ballCenter (S.state.grain (cube y))) S.state.ballRadius

def RadiusControlled (A : ℕ) (δ : ℝ) (S : BufferedArchiveSnapshot k T C O) : Prop :=
  S.state.ballRadius ≤ (A+S.dimension+5:ℝ)*δ*(∑ j, (2:ℝ)^(S.state.height j))
end BufferedArchiveSnapshot

namespace ActualBufferedArchive
open BufferedArchiveSnapshot
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

/-- Whole-cylinder localization holds in every actual immutable archive entry. -/
theorem snapshots_localized (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    ∀ S∈H.snapshots, Localized I.δ I.cube S := by
  induction H with
  | zero I P U =>
    intro S hS
    change S∈[ofState I.W] at hS
    rcases List.mem_singleton.mp hS with rfl
    exact fun y hy => (I.valid.2.2.2.2.2.2 y hy).2
  | short I P U _ =>
    intro S hS
    change S∈[ofState I.W] at hS
    rcases List.mem_singleton.mp hS with rfl
    exact fun y hy => (I.valid.2.2.2.2.2.2 y hy).2
  | last I P U Z =>
    intro S hS
    change S∈[ofState I.W,ofState Z.state] at hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact fun y hy => (I.valid.2.2.2.2.2.2 y hy).2
    · rcases List.mem_singleton.mp hS with rfl
      exact fun y hy => (Z.valid.2.2.2.2.2.2 y hy).2
  | next I P U Z hb ht tail ih =>
    intro S hS
    change S∈ofState I.W::tail.snapshots at hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact fun y hy => (I.valid.2.2.2.2.2.2 y hy).2
    · simpa only [AmbientBufferedStageData.nextData_delta,AmbientBufferedStageData.nextData_cube] using ih S hS

/-- The actual normalization radius calendar propagates to every snapshot,
including early stopping. The only initial condition is the root radius. -/
theorem snapshots_radius_controlled (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (hroot : RadiusControlled A I.δ (ofState I.W)) :
    ∀ S∈H.snapshots, RadiusControlled A I.δ S := by
  revert hroot
  induction H with
  | zero I P U =>
    intro hroot S hS
    change S∈[ofState I.W] at hS
    exact List.mem_singleton.mp hS ▸ hroot
  | short I P U _ =>
    intro hroot S hS
    change S∈[ofState I.W] at hS
    exact List.mem_singleton.mp hS ▸ hroot
  | last I P U Z =>
    intro hroot S hS
    change S∈[ofState I.W,ofState Z.state] at hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact hroot
    · rcases List.mem_singleton.mp hS with rfl
      simpa only [RadiusControlled,ofState,Nat.cast_add,show I.toInput.δ=I.δ from rfl] using Z.radius
  | next I P U Z hb ht tail ih =>
    intro hroot S hS
    change S∈ofState I.W::tail.snapshots at hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact hroot
    · have hnext : RadiusControlled A (I.nextData Z hb t ht).δ
          (ofState (I.nextData Z hb t ht).W) := by
        rw [I.nextData_snapshot Z hb t ht,I.nextData_delta Z hb t ht]
        simpa only [RadiusControlled,ofState,Nat.cast_add,show I.toInput.δ=I.δ from rfl] using Z.radius
      simpa only [AmbientBufferedStageData.nextData_delta] using ih hnext S hS

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.snapshots_localized
#print axioms KakeyaTwoScale.ActualBufferedArchive.snapshots_radius_controlled
