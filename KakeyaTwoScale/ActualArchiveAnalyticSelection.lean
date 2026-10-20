module
public import KakeyaTwoScale.ActualBufferedArchiveAccounting

@[expose] public section

open Set
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k → ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

/-- Total lookup is convenient for finite stopping-time selection. All public
selection conclusions require an index at most `drops`, where this is the
literal immutable archived snapshot. -/
def snapshotAt (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) (i : ℕ) :
    BufferedArchiveSnapshot k T C O :=
  H.snapshots[i]?.getD (BufferedArchiveSnapshot.ofState I.W)

 theorem snapshotAt_eq (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (i : ℕ) (hi : i ≤ H.drops) :
    H.snapshotAt i = H.snapshots[i]'(by rw [H.snapshots_length]; omega) := by
  have hi' : i < H.snapshots.length := by rw [H.snapshots_length]; omega
  simp only [snapshotAt,List.getElem?_eq_getElem hi',Option.getD_some]

 theorem snapshotAt_mem (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (i : ℕ) (hi : i ≤ H.drops) : H.snapshotAt i ∈ H.snapshots := by
  rw [H.snapshotAt_eq i hi]
  exact List.getElem_mem _

 theorem snapshotAt_zero (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.snapshotAt 0=BufferedArchiveSnapshot.ofState I.W := by
  cases H <;> rfl

 theorem snapshotAt_last (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.snapshotAt H.drops=H.terminal := by
  induction H with
  | zero => rfl
  | short => rfl
  | last => rfl
  | next I _ _ Z hb ht tail ih =>
    change (BufferedArchiveSnapshot.ofState I.W :: tail.snapshots)[tail.drops+1]?.getD
      (BufferedArchiveSnapshot.ofState I.W) = tail.terminal
    rw [List.getElem?_cons_succ]
    have he := tail.snapshotAt_eq tail.drops (Nat.le_refl _)
    have hi : tail.drops < tail.snapshots.length := by rw [tail.snapshots_length]; omega
    rw [List.getElem?_eq_getElem hi,Option.getD_some]
    exact he.symm.trans ih

/-- The eventual selected relation is supported in every full archive, even
when many older grains cease to be represented at later levels. -/
theorem terminal_subset_every_snapshot
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (X : BufferedArchiveSnapshot k T C O) (hX : X ∈ H.snapshots) :
    H.terminal.state.tuples ⊆ X.state.tuples := by
  induction H with
  | zero =>
    simp only [snapshots,List.mem_singleton] at hX
    subst X
    exact Finset.Subset.refl _
  | short =>
    simp only [snapshots,List.mem_singleton] at hX
    subst X
    exact Finset.Subset.refl _
  | last I _ _ Z =>
    simp only [snapshots,List.mem_cons,List.not_mem_nil,or_false] at hX
    rcases hX with rfl | rfl
    · exact Z.tuples_subset
    · exact Finset.Subset.refl _
  | next I P U Z hb ht tail ih =>
    change X ∈ BufferedArchiveSnapshot.ofState I.W :: tail.snapshots at hX
    rcases List.mem_cons.mp hX with rfl | hX
    · exact (ActualBufferedArchive.next I P U Z hb ht tail).terminal_tuples_subset
    · exact ih hX

/-- Earlier original tuple relations dominate the terminal mass. This proof
uses the actual archived relations, not regenerated geometric incidences. -/
theorem snapshot_mass (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (i : ℕ) (hi : i ≤ H.drops) :
    tupleCubeMass I.W.tuples I.cube I.cubes I.alpha / H.loss ≤
      tupleCubeMass (H.snapshotAt i).state.tuples I.cube I.cubes I.alpha := by
  exact H.terminal_mass.trans (tuple_mass_mono _ _ I.cube I.cubes
    (H.terminal_subset_every_snapshot _ (H.snapshotAt_mem i hi)) I.exponent_pos.le)

/-- Select the first archived level where every family is at most Cstar δ,
or the final requested level if no earlier such level exists. Every level and
its complete tuple relation remain unchanged. -/
theorem exists_first_short_snapshot
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) (Cstar : ℝ) :
    ∃ r : ℕ, r ≤ H.drops ∧
      (r=H.drops ∨ ∀ j, (H.snapshotAt r).state.length I.δ j ≤ Cstar*I.δ) ∧
      (∀ i < r, ∃ j, Cstar*I.δ < (H.snapshotAt i).state.length I.δ j) ∧
      (∀ i ≤ r, (H.snapshotAt r).state.tuples ⊆ (H.snapshotAt i).state.tuples) ∧
      H.terminal.state.tuples ⊆ (H.snapshotAt r).state.tuples ∧
      tupleCubeMass I.W.tuples I.cube I.cubes I.alpha/H.loss ≤
        tupleCubeMass (H.snapshotAt r).state.tuples I.cube I.cubes I.alpha := by
  classical
  let Good (i : ℕ) := i=H.drops ∨ ∀ j, (H.snapshotAt i).state.length I.δ j ≤ Cstar*I.δ
  have hex : ∃ i, Good i := ⟨H.drops,Or.inl rfl⟩
  let r := Nat.find hex
  have hr : r ≤ H.drops := Nat.find_min' hex (Or.inl rfl)
  have hg : Good r := Nat.find_spec hex
  refine ⟨r,hr,hg,?_,?_,H.terminal_subset_every_snapshot _ (H.snapshotAt_mem r hr),H.snapshot_mass r hr⟩
  · intro i hi
    have hn := Nat.find_min hex hi
    change ¬ (i=H.drops ∨ ∀ j, (H.snapshotAt i).state.length I.δ j ≤ Cstar*I.δ) at hn
    push Not at hn
    exact hn.2
  · intro i hi
    by_cases he : i=r
    · subst i
      exact Finset.Subset.refl _
    · have hir : i<r := lt_of_le_of_ne hi he
      have hn := H.snapshots_nested
      have hi' : i < H.snapshots.length := by rw [H.snapshots_length]; omega
      have hr' : r < H.snapshots.length := by rw [H.snapshots_length]; omega
      rw [H.snapshotAt_eq r hr,H.snapshotAt_eq i (hi.trans hr)]
      exact (List.pairwise_iff_getElem.mp hn) i r hi' hr' hir

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.snapshotAt_last
#print axioms KakeyaTwoScale.ActualBufferedArchive.snapshot_mass
#print axioms KakeyaTwoScale.ActualBufferedArchive.exists_first_short_snapshot
