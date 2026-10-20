module
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators
namespace KakeyaTwoScale

/-- Summation by parts on positive levels 1,...,r. The root length is
excluded; the zero-indexed transition at s has weight s. -/
theorem prefix_length_log_telescope (L : ℕ→ℝ) (r : ℕ) :
    (∑s∈Finset.range r, (s:ℝ)*(L s-L (s+1)))=
      (∑s∈Finset.range r, L (s+1))-(r:ℝ)*L r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ,ih]
    push_cast
    ring

/-- Logs of adjacent same-family length inequalities give the exact full
prefix denominator. No sign is imposed on log degrees or log lengths. -/
theorem prefix_length_log_bound (L D U : ℕ→ℝ) (r : ℕ)
    (hstep : ∀s<r, D s+L (s+1)≤U s+L s) :
    (r:ℝ)*L r+(∑s∈Finset.range r, (s:ℝ)*D s)-
      (∑s∈Finset.range r, (s:ℝ)*U s) ≤ ∑s∈Finset.range r, L (s+1) := by
  have hh : (∑s∈Finset.range r, (s:ℝ)*(D s-U s))≤
      ∑s∈Finset.range r, (s:ℝ)*(L s-L (s+1)) := by
    apply Finset.sum_le_sum
    intro s hs
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s)
    have := hstep s (Finset.mem_range.mp hs)
    linarith
  rw [prefix_length_log_telescope] at hh
  simp only [mul_sub,Finset.sum_sub_distrib] at hh
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.prefix_length_log_bound
