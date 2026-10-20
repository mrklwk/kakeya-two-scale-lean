module
public import KakeyaTwoScale.ActualPrefixLengthLog
public import KakeyaTwoScale.ActualGrainDegreeLog
public import KakeyaTwoScale.LongPrefixLogConstraint

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive

/-- Algebraic assembly on actual archive levels. The count and effective-length
bounds are explicit inputs to this interface; the concrete wrapper discharges
them from actual tube data. No degree constraints are assumed. -/
theorem entryAt_degree_constraint_of_count_and_length
    {n k A B Lh a t c J s : ℕ} {T Q O : Type} [DecidableEq T] [DecidableEq Q]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData (n+1) c k A B Lh J s T Q O}
    {U : ℝ} {fuel : ℕ}
    (H : ActualBufferedArchive k A B Lh a t T Q O N I 1 U fuel)
    (hN : ∀j, 0<N j) (hU : 1≤U)
    (hrootcount : ∀j, (I.W.count j:ℝ)≤U*(N j*1))
    (hgrain : (I.W.grains I.cube).card=1)
    (r : ℕ) (hr : r≤H.drops) (hrn : r≤n+1) (j : Fin k)
    (hlong : I.δ<(H.entryAt r hr).snapshot.state.length I.δ j)
    {Lambda E K : ℝ} (hLambda : 0<Lambda) (hE : 0<E) (hK : 0<K)
    (hcount : N j*(H.entryAt r hr).prefixProduct/
        (((H.entryAt r hr).snapshot.state.grains I.cube).card:ℝ)≤
      K*I.δ^((r:ℤ)-(n:ℤ))/
        ((List.finRange r).map (H.prefixCaptureLengths (H.polynomialIndex r hr) j)).prod)
    (hlength : Lambda≤E*(H.entryAt r hr).snapshot.state.length I.δ j*(H.entryAt r hr).prefixProduct) :
    Real.log (N j*I.δ^n)+(r:ℝ)*Real.log (Lambda/I.δ)-
      (Real.log K+(r:ℝ)*Real.log E+
        ∑i∈Finset.range r, (i:ℝ)*Real.log (H.upperAt i)) ≤
      degreeConstraintLog (n+1) (fun i => Real.log (H.stageDegrees[i]?.getD 1)) r := by
  classical
  have hpos := H.countLedger_positive (by norm_num : (0:ℝ)<1) hU _ (H.entryAt_mem r hr)
  have hG : (0:ℝ)<((H.entryAt r hr).snapshot.state.grains I.cube).card := by
    have hX : (H.entryAt r hr).snapshot∈H.snapshots := by
      rw [H.entryAt_snapshot]
      exact H.snapshotAt_mem r hr
    exact_mod_cast Finset.card_pos.mpr ((H.snapshots_certified _ hX).1.image _)
  have hprod : 0<((List.finRange r).map (H.prefixCaptureLengths (H.polynomialIndex r hr) j)).prod := by
    apply List.prod_pos
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact H.prefixCaptureLengths_pos _ j i
  have hell : 0<(H.entryAt r hr).snapshot.state.length I.δ j :=
    mul_pos I.width_pos (pow_pos (by norm_num) _)
  have hh := long_prefix_log_constraint n r (hN j) hpos.1 hG I.width_pos hprod hell
    hLambda hE hK hcount hlength
    (H.prefixCaptureLengths_log_lower hN (by norm_num) hU hrootcount r hr j hlong)
  rw [H.entryAt_log_grains r hr hrn,hgrain,Nat.cast_one,Real.log_one,zero_add,
    H.entryAt_log_prefix (by norm_num : (0:ℝ)<1) r hr,Real.log_one,zero_add] at hh
  rwa [hrz_degree_log_identity] at hh

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.entryAt_degree_constraint_of_count_and_length
