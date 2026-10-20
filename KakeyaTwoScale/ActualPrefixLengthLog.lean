module
public import KakeyaTwoScale.ActualIndexedCapture
public import KakeyaTwoScale.PrefixLengthLog

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T Q O : Type} [DecidableEq T] [DecidableEq Q]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T Q O}
    {P U : ℝ} {fuel : ℕ}

def upperAt (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel) (i : ℕ) : ℝ :=
  (H.countLedger[i]?.getD ⟨.ofState I.W,P,U⟩).upper

theorem upperAt_eq (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (i : ℕ) (hi : i≤H.drops) : H.upperAt i=(H.entryAt i hi).upper := by
  have h : i<H.countLedger.length := by rw [H.countLedger_length]; omega
  simp only [upperAt,List.getElem?_eq_getElem h,Option.getD_some,entryAt]

theorem log_prefixCaptureLengths (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (r : ℕ) (hr : r≤H.drops) (j : Fin k) :
    Real.log (((List.finRange r).map (H.prefixCaptureLengths (H.polynomialIndex r hr) j)).prod)=
      ∑i∈Finset.range r, Real.log ((H.snapshotAt (i+1)).state.length I.δ j) := by
  have hp : ∀x∈(List.finRange r).map (H.prefixCaptureLengths (H.polynomialIndex r hr) j), x≠0 := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact (H.prefixCaptureLengths_pos _ j i).ne'
  dsimp only [polynomialIndex] at hp ⊢
  rw [Real.log_list_prod hp,List.map_map,←List.ofFn_eq_map,List.sum_ofFn,Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  change Real.log (H.prefixCaptureLengths (H.polynomialIndex r hr) j i)=_
  apply congrArg Real.log
  rw [←H.entryAt_snapshot (i.val+1) (by omega),H.entryAt_capture_length]
  rfl

/-- The actual nested-count denominator has precisely the weighted
same-family log lower bound. All activity is derived from endpoint length. -/
theorem prefixCaptureLengths_log_lower
    (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (hN : ∀j, 0<N j) (hP : 0<P) (hU : 1≤U)
    (hcount : ∀j, (I.W.count j:ℝ)≤U*(N j*P))
    (r : ℕ) (hr : r≤H.drops) (j : Fin k)
    (hlong : I.δ<(H.entryAt r hr).snapshot.state.length I.δ j) :
    (r:ℝ)*Real.log ((H.entryAt r hr).snapshot.state.length I.δ j)+
      (∑i∈Finset.range r, (i:ℝ)*Real.log (H.stageDegrees[i]?.getD 1))-
      (∑i∈Finset.range r, (i:ℝ)*Real.log (H.upperAt i)) ≤
      Real.log (((List.finRange r).map (H.prefixCaptureLengths (H.polynomialIndex r hr) j)).prod) := by
  rw [H.log_prefixCaptureLengths,H.entryAt_snapshot]
  apply prefix_length_log_bound
  intro i hi
  have hiD : i≤H.drops := by omega
  have hd := H.stageDegree_get_pos i (hi.trans_le hr)
  have hu := (H.countLedger_positive hP hU _ (H.entryAt_mem i (by omega))).2
  have hla : 0<(H.entryAt i hiD).snapshot.state.length I.δ j :=
    mul_pos I.width_pos (pow_pos (by norm_num) _)
  have hlb : 0<(H.entryAt (i+1) (by omega)).snapshot.state.length I.δ j :=
    mul_pos I.width_pos (pow_pos (by norm_num) _)
  have hh := H.entryAt_active_length_step hN hP hcount i (by omega) j
    (H.entryAt_active_of_long (i+1) r (by omega) hr j hlong)
  have hhlog := Real.log_le_log (mul_pos hd hlb) hh
  rw [Real.log_mul hd.ne' hlb.ne',Real.log_mul (by linarith : (H.entryAt i hiD).upper≠0) hla.ne'] at hhlog
  rw [H.upperAt_eq i (by omega),←H.entryAt_snapshot (i+1) (by omega),←H.entryAt_snapshot i (by omega)]
  exact hhlog

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.log_prefixCaptureLengths
#print axioms KakeyaTwoScale.ActualBufferedArchive.prefixCaptureLengths_log_lower
