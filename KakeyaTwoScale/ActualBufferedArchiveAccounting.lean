module
public import KakeyaTwoScale.ActualBufferedArchive

@[expose] public section

open Set
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k → ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

/-- The actual run either reaches its requested number of dimension drops or
ends with all families at physical length δ. No active-family lower count is
asserted for the short terminal branch. -/
theorem exhausted_or_all_short (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.drops=fuel ∨ ∀ j, H.terminal.state.height j=0 := by
  induction H with
  | zero => exact Or.inl rfl
  | short _ _ _ hs => exact Or.inr hs
  | last => exact Or.inl rfl
  | next _ _ _ _ _ _ _ ih =>
    rcases ih with he | hs
    · exact Or.inl (congrArg (fun x => x+1) he)
    · exact Or.inr hs

 theorem terminal_nonempty (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.terminal.state.tuples.Nonempty := by
  induction H with
  | zero I => exact I.nonempty
  | short I => exact I.nonempty
  | last _ _ _ Z => exact Z.nonempty
  | next _ _ _ _ _ _ _ ih => exact ih

/-- Earlier complete archives are retained. The eventual terminal relation
is a subset of original tuples, with no regenerated incidences. -/
theorem terminal_tuples_subset (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.terminal.state.tuples ⊆ I.W.tuples := by
  induction H with
  | zero => exact Finset.Subset.refl _
  | short => exact Finset.Subset.refl _
  | last _ _ _ Z => exact Z.tuples_subset
  | next I _ _ Z hb ht _ ih =>
    rw [AmbientBufferedStageData.nextData_tuples] at ih
    exact ih.trans Z.tuples_subset

 theorem snapshots_tuples_subset (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (X : BufferedArchiveSnapshot k T C O) (hX : X ∈ H.snapshots) : X.state.tuples ⊆ I.W.tuples := by
  induction H with
  | zero I =>
    simp only [snapshots,List.mem_singleton] at hX
    subst X
    exact Finset.Subset.refl _
  | short I =>
    simp only [snapshots,List.mem_singleton] at hX
    subst X
    exact Finset.Subset.refl _
  | last I _ _ Z =>
    simp only [snapshots,List.mem_cons,List.not_mem_nil,or_false] at hX
    rcases hX with rfl | rfl
    · exact Finset.Subset.refl _
    · exact Z.tuples_subset
  | next I _ _ Z hb ht tail ih =>
    simp only [snapshots,List.mem_cons] at hX
    rcases hX with rfl | hX
    · exact Finset.Subset.refl _
    · have hh := ih hX
      rw [AmbientBufferedStageData.nextData_tuples] at hh
      exact hh.trans Z.tuples_subset

/-- Full archived tuple relations are nested pairwise, independently of any
later filtering used by the M4 certificate. -/
theorem snapshots_nested (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.snapshots.Pairwise (fun X Y => Y.state.tuples ⊆ X.state.tuples) := by
  induction H with
  | zero => simp [snapshots]
  | short => simp [snapshots]
  | last I _ _ Z =>
    change [BufferedArchiveSnapshot.ofState I.W,BufferedArchiveSnapshot.ofState Z.state].Pairwise _
    rw [List.pairwise_cons]
    refine ⟨?_,by simp⟩
    intro X hX
    have he := List.mem_singleton.mp hX
    subst X
    exact Z.tuples_subset
  | next I _ _ Z hb ht tail ih =>
    change (BufferedArchiveSnapshot.ofState I.W :: tail.snapshots).Pairwise _
    rw [List.pairwise_cons]
    refine ⟨?_,ih⟩
    intro X hX
    have hh := tail.snapshots_tuples_subset X hX
    rw [AmbientBufferedStageData.nextData_tuples] at hh
    exact hh.trans Z.tuples_subset

/-- Every stored complete level satisfies the cumulative deduplicated axial
budget against the initial family, including families already at height zero. -/
theorem snapshots_axial (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (X : BufferedArchiveSnapshot k T C O) (hX : X ∈ H.snapshots) (j : Fin k) :
    X.axial I.δ j ≤ I.W.length I.δ j*(I.W.count j:ℝ) := by
  induction H with
  | zero I =>
    simp only [snapshots,List.mem_singleton] at hX
    subst X
    exact le_rfl
  | short I =>
    simp only [snapshots,List.mem_singleton] at hX
    subst X
    exact le_rfl
  | last I _ _ Z =>
    simp only [snapshots,List.mem_cons,List.not_mem_nil,or_false] at hX
    rcases hX with rfl | rfl
    · exact le_rfl
    · exact Z.axial j
  | next I _ _ Z hb ht tail ih =>
    simp only [snapshots,List.mem_cons] at hX
    rcases hX with rfl | hX
    · exact le_rfl
    · have hh := ih hX
      simp only [AmbientBufferedStageData.nextData_delta,FrozenGeometryState.length,
        AmbientBufferedStageData.nextData_count,AmbientBufferedStageData.nextData_height] at hh
      exact hh.trans (Z.axial j)

/-- Pairwise cumulative axial bookkeeping is derived from the actual
constructed archive, rather than supplied as a sequence-wide assumption. -/
theorem snapshots_axial_pairwise (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.snapshots.Pairwise (fun X Y => ∀ j, Y.axial I.δ j ≤ X.axial I.δ j) := by
  induction H with
  | zero => simp [snapshots]
  | short => simp [snapshots]
  | last I _ _ Z =>
    change [BufferedArchiveSnapshot.ofState I.W,BufferedArchiveSnapshot.ofState Z.state].Pairwise _
    rw [List.pairwise_cons]
    refine ⟨?_,by simp⟩
    intro X hX
    have he := List.mem_singleton.mp hX
    subst X
    exact Z.axial
  | next I _ _ Z hb ht tail ih =>
    change (BufferedArchiveSnapshot.ofState I.W :: tail.snapshots).Pairwise _
    rw [List.pairwise_cons]
    refine ⟨?_,?_⟩
    · intro X hX j
      have hh := tail.snapshots_axial X hX j
      simp only [AmbientBufferedStageData.nextData_delta,FrozenGeometryState.length,
        AmbientBufferedStageData.nextData_count,AmbientBufferedStageData.nextData_height] at hh
      exact hh.trans (Z.axial j)
    · simpa only [AmbientBufferedStageData.nextData_delta] using ih

 theorem terminal_mem_snapshots (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.terminal ∈ H.snapshots := by
  induction H with
  | zero => simp [terminal,snapshots]
  | short => simp [terminal,snapshots]
  | last => simp [terminal,snapshots]
  | next _ _ _ _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

 theorem terminal_axial (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) (j : Fin k) :
    H.terminal.axial I.δ j ≤ I.W.length I.δ j*(I.W.count j:ℝ) :=
  H.snapshots_axial H.terminal H.terminal_mem_snapshots j

/-- Actual nonlinear mass survives the product of the concrete stage losses.
The same original cube labels and tuple IDs are used throughout the run. -/
theorem terminal_mass (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    tupleCubeMass I.W.tuples I.cube I.cubes I.alpha / H.loss ≤
      tupleCubeMass H.terminal.state.tuples I.cube I.cubes I.alpha := by
  induction H with
  | zero I =>
    change tupleCubeMass I.W.tuples I.cube I.cubes I.alpha/1 ≤ tupleCubeMass I.W.tuples I.cube I.cubes I.alpha
    rw [div_one]
  | short I =>
    change tupleCubeMass I.W.tuples I.cube I.cubes I.alpha/1 ≤ tupleCubeMass I.W.tuples I.cube I.cubes I.alpha
    rw [div_one]
  | last I _ _ Z => exact Z.mass
  | next I _ _ Z hb ht tail ih =>
    simp only [AmbientBufferedStageData.nextData_tuples,AmbientBufferedStageData.nextData_cube,
      AmbientBufferedStageData.nextData_cubes,AmbientBufferedStageData.nextData_alpha] at ih
    have hh := (div_le_div_of_nonneg_right Z.mass tail.loss_pos.le).trans ih
    change tupleCubeMass I.W.tuples I.cube I.cubes I.alpha/(Z.retentionLoss*tail.loss) ≤
      tupleCubeMass tail.terminal.state.tuples I.cube I.cubes I.alpha
    rw [← div_div]
    exact hh


end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.exhausted_or_all_short
#print axioms KakeyaTwoScale.ActualBufferedArchive.snapshots_nested

#print axioms KakeyaTwoScale.ActualBufferedArchive.snapshots_axial_pairwise
#print axioms KakeyaTwoScale.ActualBufferedArchive.terminal_mass
