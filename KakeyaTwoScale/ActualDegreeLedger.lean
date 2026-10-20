module
public import KakeyaTwoScale.ActualArchiveMultilinear

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Numerical shadow of the actual executed stages. The root factors are
retained; dimensions decrease only at executed transitions. -/
def degreeLedger (b : ℕ) (P G : ℝ) : List ℝ → List (ℝ × ℝ)
  | [] => [(P,G)]
  | D::ds => (P,G)::degreeLedger (b-1) (P*D) (G*D^(b:ℝ)) ds

namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T Q O : Type} [DecidableEq T] [DecidableEq Q]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T Q O}
    {P U : ℝ} {fuel : ℕ}

theorem stageDegrees_length (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel) :
    H.stageDegrees.length=H.drops := by
  induction H with
  | zero => rfl
  | short => rfl
  | last => rfl
  | next _ _ _ _ _ _ _ ih => simpa only [stageDegrees,List.length_cons,drops] using congrArg (·+1) ih

theorem countLedger_length (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel) :
    H.countLedger.length=H.drops+1 := by
  have hh := congrArg List.length H.countLedger_snapshots
  simpa only [List.length_map,H.snapshots_length] using hh

theorem stageDegrees_positive (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel) :
    ∀D∈H.stageDegrees, 0<D := by
  induction H with
  | zero => simp [stageDegrees]
  | short => simp [stageDegrees]
  | last I P U Z => simpa only [stageDegrees,List.mem_singleton,forall_eq] using Z.degree_pos
  | next I P U Z hb ht tail ih =>
    intro D hD
    rcases List.mem_cons.mp hD with rfl | hD
    · exact Z.degree_pos
    · exact ih D hD

/-- Exact actual prefix product and grain cardinality, simultaneously at all
stored levels. There is no D≥1 or analytic estimate assumption. -/
theorem countLedger_degree_ledger (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel) :
    H.countLedger.map (fun E => (E.prefixProduct,((E.snapshot.state.grains I.cube).card:ℝ)))=
      degreeLedger b P ((I.W.grains I.cube).card:ℝ) H.stageDegrees := by
  classical
  induction H with
  | zero => rfl
  | short => rfl
  | last I P U Z =>
    simp only [countLedger,stageDegrees,degreeLedger,List.map_cons,List.map_nil,
      BufferedArchiveSnapshot.ofState,List.cons.injEq,Prod.mk.injEq,true_and,and_true]
    exact Z.degree_identity
  | next I P U Z hb ht tail ih =>
    simp only [countLedger,stageDegrees,degreeLedger,List.map_cons,BufferedArchiveSnapshot.ofState]
    congr 1
    rw [AmbientBufferedStageData.nextData_grain_count] at ih
    have hd := Z.degree_identity
    change ((Z.state.grains I.cube).card:ℝ)=((I.W.grains I.cube).card:ℝ)*_ at hd
    rw [hd] at ih
    simpa only [AmbientBufferedStageData.nextData_cube,countLedger,stageDegrees,BufferedArchiveSnapshot.ofState] using ih

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.stageDegrees_positive
#print axioms KakeyaTwoScale.ActualBufferedArchive.countLedger_degree_ledger
