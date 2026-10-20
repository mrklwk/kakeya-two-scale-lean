module
public import KakeyaTwoScale.ActualPrefixLengthLog

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

theorem sum_range_cast (r : ℕ) : (∑i∈Finset.range r, (i:ℝ))=(r:ℝ)*(r-1)/2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ,ih]
    push_cast
    ring

/-- A single simultaneous product-loss envelope pays every weighted prefix
error. The sharp triangular coefficient comes from the actual indexing. -/
theorem prefix_log_error_bound (r : ℕ) (K C loss E : ℝ) (U : ℕ→ℝ)
    (hC : 0<C) (hloss : 1≤loss)
    (hU : ∀i≤r, 1≤U i) (henv : ∀i≤r, loss*U i≤Real.exp E) :
    Real.log K+(r:ℝ)*Real.log (C*(loss*U r))+
      (∑i∈Finset.range r, (i:ℝ)*Real.log (U i)) ≤
        Real.log K+(r:ℝ)*Real.log C+(r:ℝ)*(r+1)/2*E := by
  have hL : 0<loss := by linarith
  have hpos (i) (hi : i≤r) : 0<U i := lt_of_lt_of_le zero_lt_one (hU i hi)
  have hp (i) (hi : i≤r) : Real.log (loss*U i)≤E := by
    have hh := Real.log_le_log (mul_pos hL (hpos i hi)) (henv i hi)
    simpa only [Real.log_exp] using hh
  have hu (i) (hi : i≤r) : Real.log (U i)≤E := by
    apply (Real.log_le_log (hpos i hi) (le_mul_of_one_le_left (hpos i hi).le hloss)).trans
    exact hp i hi
  have hs : (∑i∈Finset.range r, (i:ℝ)*Real.log (U i))≤
      (∑i∈Finset.range r, (i:ℝ))*E := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hu i (by have := Finset.mem_range.mp hi; omega)) (Nat.cast_nonneg i))
  rw [sum_range_cast] at hs
  rw [Real.log_mul hC.ne' (mul_pos hL (hpos r le_rfl)).ne']
  have hh := mul_le_mul_of_nonneg_left (hp r le_rfl) (Nat.cast_nonneg (α:=ℝ) r)
  nlinarith

namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T Q O : Type} [DecidableEq T] [DecidableEq Q]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T Q O}
    {P U : ℝ} {fuel : ℕ}

/-- Convert the existing simultaneous dyadic envelope to the exact error
appearing in every actual long-prefix constraint. -/
theorem long_prefix_error_le
    (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (hP : 0<P) (hU : 1≤U) (epsilon : ℝ) (q : ℕ)
    (henv : ∀E∈H.countLedger, H.loss*E.upper≤(2:ℝ)^(epsilon*(q:ℝ)))
    (r : ℕ) (hr : r≤H.drops) (K C : ℝ) (hC : 0<C) :
    Real.log K+(r:ℝ)*Real.log (C*(H.loss*(H.entryAt r hr).upper))+
      (∑i∈Finset.range r, (i:ℝ)*Real.log (H.upperAt i)) ≤
        Real.log K+(r:ℝ)*Real.log C+(r:ℝ)*(r+1)/2*(epsilon*(q:ℝ)*Real.log 2) := by
  rw [←H.upperAt_eq r hr]
  apply prefix_log_error_bound r K C H.loss _ H.upperAt hC H.loss_one_le
  · intro i hi
    rw [H.upperAt_eq i (hi.trans hr)]
    exact (H.countLedger_positive hP hU _ (H.entryAt_mem i (hi.trans hr))).2
  · intro i hi
    rw [H.upperAt_eq i (hi.trans hr)]
    have hh := henv _ (H.entryAt_mem i (hi.trans hr))
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)] at hh
    convert hh using 1
    congr 1
    ring

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.prefix_log_error_bound
#print axioms KakeyaTwoScale.ActualBufferedArchive.long_prefix_error_le
