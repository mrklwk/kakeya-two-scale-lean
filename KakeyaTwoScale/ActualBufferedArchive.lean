module
public import KakeyaTwoScale.NormalizedStageSuccessor
public import KakeyaTwoScale.BufferedArchiveSnapshot

@[expose] public section

open Set
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- A complete archive of constructed dimension transitions. `short` freezes
all families exactly when every height is zero; `last` retains the output
at fuel exhaustion, which may have positive dimension or dimension zero. No stage oracle or externally supplied sequence is stored. -/
inductive ActualBufferedArchive (k A B Lh a t : ℕ) (T C O : Type)
    [DecidableEq T] [DecidableEq C] (N : Fin k → ℝ) :
    {b c J s : ℕ} → AmbientBufferedStageData b c k A B Lh J s T C O → ℝ → ℝ → ℕ → Type 1
  | zero {b c J s} (I : AmbientBufferedStageData b c k A B Lh J s T C O) (P U : ℝ) :
      ActualBufferedArchive k A B Lh a t T C O N I P U 0
  | short {b c J s fuel} (I : AmbientBufferedStageData b c k A B Lh J s T C O) (P U : ℝ)
      (all_short : ∀ j, I.W.height j=0) :
      ActualBufferedArchive k A B Lh a t T C O N I P U (fuel+1)
  | last {b c J s} (I : AmbientBufferedStageData b c k A B Lh J s T C O) (P U : ℝ)
      (stage : ActualNormalizedBufferedStage I.toInput N P U a) :
      ActualBufferedArchive k A B Lh a t T C O N I P U 1
  | next {b c J s fuel} (I : AmbientBufferedStageData b c k A B Lh J s T C O) (P U : ℝ)
      (stage : ActualNormalizedBufferedStage I.toInput N P U a)
      (hb : 1 < b) (ht : 2 ≤ t)
      (tail : ActualBufferedArchive k A B Lh a t T C O N (I.nextData stage hb t ht)
        (P*stage.degree) stage.upperFactor (fuel+1)) :
      ActualBufferedArchive k A B Lh a t T C O N I P U (fuel+2)

namespace AmbientBufferedStageData
variable {b c k A B Lh J s a t : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]

/-- Run actual normalized polynomial transitions until the requested
codimension or the all-short branch is reached. The next raw input is
constructed from the previous actual output, including new equations,
coordinate transport, regenerated tags and the explicit degree calendar. -/
theorem exists_actual_archive (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    (N : Fin k → ℝ) (P U : ℝ) (ha : 0 < a) (ht : 2 ≤ t)
    (hN : ∀ j, 0 ≤ N j) (hP : 0 ≤ P) (hU : 0 ≤ U)
    (hcount : ∀ j, (I.W.count j:ℝ) ≤ U*(N j*P))
    (fuel : ℕ) (hfuel : fuel ≤ b) :
    Nonempty (ActualBufferedArchive k A B Lh a t T C O N I P U fuel) := by
  classical
  induction fuel generalizing b c J s P U with
  | zero => exact ⟨.zero I P U⟩
  | succ fuel ih =>
    by_cases hshort : ∀ j, I.W.height j=0
    · exact ⟨.short I P U hshort⟩
    · obtain ⟨Z⟩ := I.toInput.exists_actual_normalized_stage N P U a ha hN hP hU hcount
      cases fuel with
      | zero => exact ⟨.last I P U Z⟩
      | succ fuel =>
        have hb : 1 < b := by omega
        let I' := I.nextData Z hb t ht
        have hct : ∀ j, (I'.W.count j:ℝ) ≤ Z.upperFactor*(N j*(P*Z.degree)) := by
          intro j
          simpa only [I',nextData_count] using Z.total_count j
        obtain ⟨tail⟩ := ih I' (P*Z.degree) Z.upperFactor (mul_nonneg hP Z.degree_pos.le)
          Z.upperFactor_pos.le hct (by omega)
        exact ⟨.next I P U Z hb ht tail⟩

end AmbientBufferedStageData

namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k → ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

/-- The archive retains each incoming complete state, including records and
grains subsequently absent from the final tuple relation. -/
def snapshots (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) : List (BufferedArchiveSnapshot k T C O) := by
  induction H with
  | zero I => exact [BufferedArchiveSnapshot.ofState I.W]
  | short I => exact [BufferedArchiveSnapshot.ofState I.W]
  | last I _ _ Z => exact [BufferedArchiveSnapshot.ofState I.W,BufferedArchiveSnapshot.ofState Z.state]
  | next I _ _ Z _ _ _ ih => exact BufferedArchiveSnapshot.ofState I.W :: ih

def drops (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) : ℕ := by
  induction H with
  | zero I => exact 0
  | short I => exact 0
  | last I _ _ Z => exact 1
  | next I _ _ Z _ _ _ ih => exact ih+1

def terminal (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) : BufferedArchiveSnapshot k T C O := by
  induction H with
  | zero I => exact .ofState I.W
  | short I => exact .ofState I.W
  | last I _ _ Z => exact .ofState Z.state
  | next I _ _ Z _ _ _ ih => exact ih

def loss (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) : ℝ := by
  induction H with
  | zero I => exact 1
  | short I => exact 1
  | last I _ _ Z => exact Z.retentionLoss
  | next I _ _ Z _ _ _ ih => exact Z.retentionLoss*ih

def degreeProduct (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) : ℝ := by
  induction H with
  | zero I => exact 1
  | short I => exact 1
  | last I _ _ Z => exact Z.degree
  | next I _ _ Z _ _ _ ih => exact Z.degree*ih

def normalizationRounds (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) : List ℕ := by
  induction H with
  | zero I => exact []
  | short I => exact []
  | last I _ _ Z => exact [Z.rounds]
  | next I _ _ Z _ _ _ ih => exact Z.rounds::ih

def cellularDepths (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) : List ℕ := by
  induction H with
  | zero I => exact []
  | short I => exact []
  | last I _ _ Z => exact [Z.seed.cellular_depth]
  | next I _ _ Z _ _ _ ih => exact Z.seed.cellular_depth::ih


 theorem drops_le (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) : H.drops ≤ fuel := by
  induction H with
  | zero => simp [drops]
  | short => simp [drops]
  | last => simp [drops]
  | next _ _ _ _ _ _ tail ih =>
    change tail.drops+1 ≤ _
    omega

 theorem snapshots_length (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.snapshots.length=H.drops+1 := by
  induction H with
  | zero => rfl
  | short => rfl
  | last => rfl
  | next _ _ _ _ _ _ tail ih =>
    change tail.snapshots.length+1=(tail.drops+1)+1
    rw [ih]

 theorem snapshots_head (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.snapshots.head?=some (BufferedArchiveSnapshot.ofState I.W) := by cases H <;> rfl

 theorem loss_pos (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) : 0 < H.loss := by
  induction H with
  | zero => norm_num [loss]
  | short => norm_num [loss]
  | last _ _ _ Z => exact Z.retentionLoss_pos
  | next _ _ _ Z _ _ _ ih => exact mul_pos Z.retentionLoss_pos ih

 theorem degreeProduct_pos (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) : 0 < H.degreeProduct := by
  induction H with
  | zero => norm_num [degreeProduct]
  | short => norm_num [degreeProduct]
  | last _ _ _ Z => exact Z.degree_pos
  | next _ _ _ Z _ _ _ ih => exact mul_pos Z.degree_pos ih

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.AmbientBufferedStageData.exists_actual_archive
#print axioms KakeyaTwoScale.ActualBufferedArchive.drops_le
#print axioms KakeyaTwoScale.ActualBufferedArchive.loss_pos
