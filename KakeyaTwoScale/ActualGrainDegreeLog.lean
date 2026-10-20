module
public import KakeyaTwoScale.ActualDegreePrefixLog

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T Q O : Type} [DecidableEq T] [DecidableEq Q]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T Q O}
    {P U : ℝ} {fuel : ℕ}

/-- Exact logarithm of the actual grain cardinality; the initial grain
factor is retained and executed log degrees need not be nonnegative. -/
theorem entryAt_log_grains
    (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (r : ℕ) (hr : r≤H.drops) (hrb : r≤b) :
    Real.log (((H.entryAt r hr).snapshot.state.grains I.cube).card:ℝ)=
      Real.log ((I.W.grains I.cube).card:ℝ)+
        ∑i∈Finset.range r, ((b:ℝ)-i)*Real.log (H.stageDegrees[i]?.getD 1) := by
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
  have hh := degreeLedger_ratio b 0 P ((I.W.grains I.cube).card:ℝ)
    H.stageDegrees r hd hrb hG H.stageDegrees_positive
  simp only [pow_zero,Nat.cast_zero,sub_zero,one_div] at hh
  have hhlog := congrArg Real.log hh
  rw [Real.log_mul (inv_ne_zero hG.ne') (Real.exp_ne_zero _),Real.log_inv,
    Real.log_exp,Real.log_inv,degreeWeightedLog_take _ _ _ hd] at hhlog
  have hhgrain := congrArg (fun e : ℝ×ℝ => Real.log e.2) he
  change Real.log (((H.entryAt r hr).snapshot.state.grains I.cube).card:ℝ)=_ at hhgrain
  linarith

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.entryAt_log_grains
