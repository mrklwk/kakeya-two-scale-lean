module
public import KakeyaTwoScale.DegreeLedgerObjective

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T Q O : Type} [DecidableEq T] [DecidableEq Q]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T Q O}
    {P U : ℝ} {fuel : ℕ}

/-- Literal indexed ledger lookup; only real executed prefix indices are allowed. -/
def entryAt (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (r : ℕ) (hr : r≤H.drops) : BufferedCountSnapshot k T Q O :=
  H.countLedger[r]'(by rw [H.countLedger_length]; omega)

theorem entryAt_mem (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (r : ℕ) (hr : r≤H.drops) : H.entryAt r hr∈H.countLedger := List.getElem_mem _

theorem entryAt_snapshot (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (r : ℕ) (hr : r≤H.drops) : (H.entryAt r hr).snapshot=H.snapshotAt r := by
  have hi : r<H.countLedger.length := by rw [H.countLedger_length]; omega
  have hs : r<H.snapshots.length := by rw [H.snapshots_length]; omega
  have he := congrArg (fun l : List (BufferedArchiveSnapshot k T Q O) => l[r]?) H.countLedger_snapshots
  simp only [List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hs,
    Option.map_some,Option.some.injEq] at he
  rw [H.snapshotAt_eq r hr]
  exact he

/-- Exact indexed optimizer denominator for the actual archive. The general
initial grain and product factors remain visible. -/
theorem entryAt_degree_objective
    (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (m : ℕ) (hb : b=m+k) (r : ℕ) (hr : r≤H.drops) (hrm : r ≤ m) :
    (H.entryAt r hr).prefixProduct^k/((H.entryAt r hr).snapshot.state.grains I.cube).card =
      (P^k/(I.W.grains I.cube).card)*
        Real.exp (-degreeObjectiveLog m r (fun i => Real.log (H.stageDegrees[i]?.getD 1))) := by
  classical
  have hi : r<H.countLedger.length := by rw [H.countLedger_length]; omega
  have hm : r<(H.countLedger.map (fun E => (E.prefixProduct,((E.snapshot.state.grains I.cube).card:ℝ)))).length := by
    simpa only [List.length_map] using hi
  have hd : r≤H.stageDegrees.length := by rwa [H.stageDegrees_length]
  have hn : r<(degreeLedger b P ((I.W.grains I.cube).card:ℝ) H.stageDegrees).length := by
    rw [degreeLedger_length]; omega
  have he := congrArg (fun l : List (ℝ×ℝ) => l[r]?.getD (0,0)) H.countLedger_degree_ledger
  simp only [List.getElem?_eq_getElem hm,List.getElem?_eq_getElem hn,
    Option.getD_some,List.getElem_map] at he
  have hG : (0:ℝ)<(I.W.grains I.cube).card := by
    exact_mod_cast Finset.card_pos.mpr (I.nonempty.image _)
  have hh := degreeLedger_ratio b k P ((I.W.grains I.cube).card:ℝ) H.stageDegrees r hd (by omega) hG H.stageDegrees_positive
  have hbk : (b:ℝ)-k=m := by rw [hb]; push_cast; ring
  rw [hbk,degreeWeightedLog_objective m H.stageDegrees r hd] at hh
  exact (congrArg (fun e : ℝ×ℝ => e.1^k/e.2) he).trans hh

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.entryAt_snapshot
#print axioms KakeyaTwoScale.ActualBufferedArchive.entryAt_degree_objective
