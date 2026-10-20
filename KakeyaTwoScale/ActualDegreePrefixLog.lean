module
public import KakeyaTwoScale.ActualArchiveDegreeFloor

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

theorem degreeLedger_prefixProduct (b : ℕ) (P G : ℝ) (ds : List ℝ)
    (r : ℕ) (hr : r≤ds.length) :
    ((degreeLedger b P G ds)[r]'(by rw [degreeLedger_length]; omega)).1=
      P*∏i∈Finset.range r, ds[i]?.getD 1 := by
  induction r generalizing b P G ds with
  | zero => cases ds <;> simp [degreeLedger]
  | succ r ih =>
    cases ds with
    | nil => simp at hr
    | cons D ds =>
      have hidx : r<(degreeLedger (b-1) (P*D) (G*D^(b:ℝ)) ds).length := by
        rw [degreeLedger_length]
        simp only [List.length_cons] at hr
        omega
      change ((degreeLedger (b-1) (P*D) (G*D^(b:ℝ)) ds)[r]).1=_
      rw [ih (b-1) (P*D) (G*D^(b:ℝ)) ds (by simpa using hr)]
      rw [Finset.prod_range_succ']
      simp only [List.getElem?_cons_zero,Option.getD_some,List.getElem?_cons_succ]
      ring

namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T Q O : Type} [DecidableEq T] [DecidableEq Q]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T Q O}
    {P U : ℝ} {fuel : ℕ}

theorem entryAt_prefixProduct (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (r : ℕ) (hr : r≤H.drops) :
    (H.entryAt r hr).prefixProduct=P*∏i∈Finset.range r, H.stageDegrees[i]?.getD 1 := by
  classical
  have hi : r<H.countLedger.length := by rw [H.countLedger_length]; omega
  have hm : r<(H.countLedger.map (fun E => (E.prefixProduct,((E.snapshot.state.grains I.cube).card:ℝ)))).length := by
    simpa only [List.length_map] using hi
  have hd : r≤H.stageDegrees.length := by rwa [H.stageDegrees_length]
  have hn : r<(degreeLedger b P ((I.W.grains I.cube).card:ℝ) H.stageDegrees).length := by rw [degreeLedger_length]; omega
  have he := congrArg (fun l : List (ℝ×ℝ) => l[r]?.getD (0,0)) H.countLedger_degree_ledger
  simp only [List.getElem?_eq_getElem hm,List.getElem?_eq_getElem hn,Option.getD_some,List.getElem_map] at he
  exact (congrArg Prod.fst he).trans (degreeLedger_prefixProduct b P _ H.stageDegrees r hd)

theorem stageDegree_get_pos (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (i : ℕ) (hi : i<H.drops) : 0<H.stageDegrees[i]?.getD 1 := by
  have h : i<H.stageDegrees.length := by rwa [H.stageDegrees_length]
  rw [List.getElem?_eq_getElem h,Option.getD_some]
  exact H.stageDegrees_positive _ (List.getElem_mem h)

/-- Exact prefix log; executed log degrees may have either sign. -/
theorem entryAt_log_prefix (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (hP : 0<P) (r : ℕ) (hr : r≤H.drops) :
    Real.log (H.entryAt r hr).prefixProduct=Real.log P+
      degreePrefixLog (fun i => Real.log (H.stageDegrees[i]?.getD 1)) r := by
  have hd (i) (hi : i∈Finset.range r) := H.stageDegree_get_pos i ((Finset.mem_range.mp hi).trans_le hr)
  rw [H.entryAt_prefixProduct r hr,
    Real.log_mul hP.ne' (Finset.prod_ne_zero_iff.mpr (fun i hi => (hd i hi).ne')),
    Real.log_prod (fun i hi => (hd i hi).ne')]
  rfl

/-- Actual last-degree floor at any executed prefix, paid by the single
archive loss. This is the floor needed by early-stop completion. -/
theorem prefix_last_degree_floor (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (r : ℕ) (hr : r≤H.drops) (hr0 : 0<r) :
    -Real.log (2*H.loss)≤Real.log (H.stageDegrees[r-1]?.getD 1) := by
  have hi : r-1<H.stageDegrees.length := by rw [H.stageDegrees_length]; omega
  rw [List.getElem?_eq_getElem hi,Option.getD_some]
  exact H.stageDegrees_log_floor _ (List.getElem_mem hi)

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.entryAt_log_prefix
#print axioms KakeyaTwoScale.ActualBufferedArchive.prefix_last_degree_floor
