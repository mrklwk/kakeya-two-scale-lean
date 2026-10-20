module
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Logarithm of the degree product P_i. The entries are log D_s, indexed from zero. -/
def degreePrefixLog (D : ℕ → ℝ) (i : ℕ) : ℝ := ∑ s ∈ Finset.range i, D s

/-- Logarithm of the degree monomial R_i in Section 4. -/
def degreeConstraintLog (n : ℕ) (D : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ s ∈ Finset.range i, ((n:ℝ)+i-1-2*s)*D s

/-- Logarithm of the final denominator, also valid for a truncated terminal run. -/
def degreeObjectiveLog (m r : ℕ) (D : ℕ → ℝ) : ℝ :=
  ∑ s ∈ Finset.range r, ((m:ℝ)-s)*D s

theorem degree_log_step (n i : ℕ) (D : ℕ → ℝ) :
    degreeConstraintLog n D (i+1) = degreeConstraintLog n D i +
      degreePrefixLog D (i+1) + ((n:ℝ)-(i+1))*D i := by
  unfold degreeConstraintLog degreePrefixLog
  rw [Finset.sum_range_succ,Finset.sum_range_succ]
  push_cast
  have he : ∑ s ∈ Finset.range i, ((n:ℝ)+(i+1)-1-2*s)*D s =
      (∑ s ∈ Finset.range i, ((n:ℝ)+i-1-2*s)*D s)+∑ s ∈ Finset.range i, D s := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  rw [he]
  ring

theorem virtual_degree_prefix {r i : ℕ} (D : ℕ → ℝ) (hri : r ≤ i)
    (hzero : ∀ s, r ≤ s → D s=0) : degreePrefixLog D i=degreePrefixLog D r := by
  induction i, hri using Nat.le_induction with
  | base => rfl
  | succ i hri ih =>
    rw [degreePrefixLog,Finset.sum_range_succ,hzero i hri,add_zero]
    exact ih

theorem virtual_degree_constraint {n r i : ℕ} (D : ℕ → ℝ) (hri : r ≤ i)
    (hzero : ∀ s, r ≤ s → D s=0) :
    degreeConstraintLog n D i = degreeConstraintLog n D r + ((i:ℝ)-r)*degreePrefixLog D r := by
  induction i, hri using Nat.le_induction with
  | base => simp
  | succ i hri ih =>
    rw [degree_log_step,virtual_degree_prefix D (by omega) hzero,hzero i hri,ih]
    push_cast
    ring

theorem virtual_degree_objective {m r : ℕ} (D : ℕ → ℝ) (hrm : r ≤ m)
    (hzero : ∀ s, r ≤ s → D s=0) : degreeObjectiveLog m m D=degreeObjectiveLog m r D := by
  have hh : ∀ i, r ≤ i → degreeObjectiveLog m i D=degreeObjectiveLog m r D := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => rfl
    | succ i hi ih =>
      rw [degreeObjectiveLog,Finset.sum_range_succ,hzero i hi,mul_zero,add_zero]
      exact ih
  exact hh m hrm

/-- Complete ALL numerical Section 4 constraints after an early all-small
terminal stage. E explicitly pays earlier constraints, selected mass and the
last degree floor. No D>=1 assumption is made. The zero-depth case is included. -/
theorem terminal_degree_constraints_complete {n m r : ℕ} (D : ℕ → ℝ)
    (hrm : r ≤ m) (hmn : m ≤ n) {x w E : ℝ} (hE : 0 ≤ E)
    (hzero : ∀ s, r ≤ s → D s=0)
    (hbefore : ∀ i, 1 ≤ i → i < r → (i:ℝ)*x+w-E ≤ degreeConstraintLog n D i)
    (hterminal : x-E ≤ degreePrefixLog D r)
    (hfloor : 0 < r → -E ≤ D (r-1))
    (hpacking : w ≤ E) :
    ∀ i, 1 ≤ i → i ≤ m →
      (i:ℝ)*x+w-((n:ℝ)+m+2)*E ≤ degreeConstraintLog n D i := by
  intro i hi him
  by_cases hir : i < r
  · have hh := hbefore i hi hir
    have hc : 1 ≤ (n:ℝ)+m+2 := by
      linarith [Nat.cast_nonneg (α:=ℝ) n,Nat.cast_nonneg (α:=ℝ) m]
    nlinarith
  have hri : r ≤ i := by omega
  rw [virtual_degree_constraint D hri hzero]
  by_cases hr : r=0
  · subst r
    simp only [degreePrefixLog,degreeConstraintLog,Finset.range_zero,Finset.sum_empty,Nat.cast_zero,
      sub_zero,mul_zero,add_zero] at hterminal ⊢
    have hi' : (i:ℝ) ≤ (m:ℝ) := by exact_mod_cast him
    nlinarith [Nat.cast_nonneg (α:=ℝ) i,Nat.cast_nonneg (α:=ℝ) n]
  have hrpos : 0 < r := by omega
  have hpred : ((r:ℝ)-1)*x+w-E ≤ degreeConstraintLog n D (r-1) := by
    by_cases hr1 : r=1
    · subst r
      simp only [Nat.cast_one,sub_self,zero_mul,zero_add,Nat.sub_self,degreeConstraintLog,
        Finset.range_zero,Finset.sum_empty]
      linarith
    · have hh := hbefore (r-1) (by omega) (by omega)
      have hc : ((r-1:ℕ):ℝ)=(r:ℝ)-1 := by
        have hh : ((r-1:ℕ):ℝ)+1=(r:ℝ) := by exact_mod_cast Nat.sub_add_cancel hrpos
        linarith
      simpa only [hc] using hh
  have he := degree_log_step n (r-1) D
  have hrr : r-1+1=r := by omega
  rw [hrr] at he
  have hn : (r:ℝ) ≤ (n:ℝ) := by exact_mod_cast hrm.trans hmn
  have hfloor' := mul_le_mul_of_nonneg_left (hfloor hrpos) (sub_nonneg.mpr hn)
  have hri' : 0 ≤ (i:ℝ)-r := by
    exact sub_nonneg.mpr (by exact_mod_cast hri)
  have hterm' := mul_le_mul_of_nonneg_left hterminal hri'
  have hi' : (i:ℝ) ≤ (m:ℝ) := by exact_mod_cast him
  have hc : ((r-1:ℕ):ℝ)+1=(r:ℝ) := by exact_mod_cast hrr
  rw [hc] at he
  nlinarith [Nat.cast_nonneg (α:=ℝ) r]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.degree_log_step
#print axioms KakeyaTwoScale.virtual_degree_prefix
#print axioms KakeyaTwoScale.virtual_degree_constraint
#print axioms KakeyaTwoScale.virtual_degree_objective
#print axioms KakeyaTwoScale.terminal_degree_constraints_complete
