module
public import KakeyaTwoScale.OptimizedWeightedMass

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

def stoppedLogDegrees (D : ℕ→ℝ) (r i : ℕ) : ℝ := if i<r then D i else 0

theorem stopped_prefix_log (D : ℕ→ℝ) (r i : ℕ) (hi : i≤r) :
    degreePrefixLog (stoppedLogDegrees D r) i=degreePrefixLog D i := by
  unfold degreePrefixLog
  apply Finset.sum_congr rfl
  intro s hs
  exact ite_eq_left ((Finset.mem_range.mp hs).trans_le hi)

theorem stopped_constraint_log (n : ℕ) (D : ℕ→ℝ) (r i : ℕ) (hi : i≤r) :
    degreeConstraintLog n (stoppedLogDegrees D r) i=degreeConstraintLog n D i := by
  unfold degreeConstraintLog
  apply Finset.sum_congr rfl
  intro s hs
  rw [stoppedLogDegrees,ite_eq_left ((Finset.mem_range.mp hs).trans_le hi)]

theorem stopped_objective_log (m : ℕ) (D : ℕ→ℝ) (r : ℕ) :
    degreeObjectiveLog m r (stoppedLogDegrees D r)=degreeObjectiveLog m r D := by
  unfold degreeObjectiveLog
  apply Finset.sum_congr rfl
  intro s hs
  rw [stoppedLogDegrees,ite_eq_left (Finset.mem_range.mp hs)]

/-- One numerical conclusion for the actual first-short or exhausted-long
alternative. Only the numerical sequence is padded; no archive is extended. -/
theorem stopped_degree_optimization {n m r : ℕ} (D : ℕ→ℝ)
    (hn : m+2≤n) (hrm : r ≤ m) {x w E : ℝ} (hE : 0≤E)
    (hbefore : ∀i, 1≤ i → i<r → (i:ℝ)*x+w-E≤degreeConstraintLog n D i)
    (hstop : x-E≤degreePrefixLog D r ∨
      (r=m ∧ (r:ℝ)*x+w-E≤degreeConstraintLog n D r))
    (hfloor : 0<r → -E≤ D (r-1)) (hpacking : w≤E) :
    (m:ℝ)*(m+1)/(2*n)*x+
      (1/2-((n:ℝ)-m)*((n:ℝ)-m-1)/(2*n*((n:ℝ)-1)))*(w-((n:ℝ)+m+2)*E) ≤
        degreeObjectiveLog m r D := by
  let D' := stoppedLogDegrees D r
  have hzero : ∀s, r≤ s → D' s=0 := by
    intro s hs
    exact ite_eq_right (by omega)
  have hc : ∀i, 1≤ i → i ≤ m →
      (i:ℝ)*x+w-((n:ℝ)+m+2)*E≤degreeConstraintLog n D' i := by
    rcases hstop with hshort | ⟨he,hlast⟩
    · apply terminal_degree_constraints_complete D' hrm (by omega) hE hzero
      · intro i hi hir
        rw [show degreeConstraintLog n D' i=degreeConstraintLog n D i from stopped_constraint_log n D r i (by omega)]
        exact hbefore i hi hir
      · rw [show degreePrefixLog D' r=degreePrefixLog D r from stopped_prefix_log D r r le_rfl]
        exact hshort
      · intro hr
        rw [show D' (r-1)=D (r-1) from ite_eq_left (by omega)]
        exact hfloor hr
      · exact hpacking
    · intro i hi him
      have hir : i≤r := by omega
      rw [show degreeConstraintLog n D' i=degreeConstraintLog n D i from stopped_constraint_log n D r i hir]
      have hh : (i:ℝ)*x+w-E≤degreeConstraintLog n D i := by
        obtain hlt | rfl := lt_or_eq_of_le hir
        · exact hbefore i hi hlt
        · exact hlast
      have hcoef : 1≤(n:ℝ)+m+2 := by
        have := Nat.cast_nonneg (α := ℝ) n
        have := Nat.cast_nonneg (α := ℝ) m
        linarith
      have hmul := mul_le_mul_of_nonneg_right hcoef hE
      linarith
  have hh := degree_log_optimization n m D' hn x w (((n:ℝ)+m+2)*E)
    (fun i hi => by simpa only [Nat.cast_add,Nat.cast_one] using hc (i+1) (by omega) (by omega))
  rw [virtual_degree_objective D' hrm hzero,
    show degreeObjectiveLog m r D'=degreeObjectiveLog m r D from stopped_objective_log m D r] at hh
  exact hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.stopped_degree_optimization
