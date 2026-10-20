module
public import KakeyaTwoScale.TerminalDegreeConstraints

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

def degreeWeight (n : ℕ) (i : ℕ) : ℝ :=
  1 / (((n:ℝ)-i)*((n:ℝ)-i-1)*((n:ℝ)-i-2))

theorem degree_objective_step (m : ℕ) (D : ℕ → ℝ) :
    degreeObjectiveLog (m+1) (m+1) D = degreeObjectiveLog m m D + degreePrefixLog D (m+1) := by
  unfold degreeObjectiveLog degreePrefixLog
  rw [Finset.sum_range_succ,Finset.sum_range_succ]
  push_cast
  have he : (∑ s ∈ Finset.range m, ((m:ℝ)+1-s)*D s) =
      ∑ s ∈ Finset.range m, (((m:ℝ)-s)*D s+D s) := by
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [he,Finset.sum_add_distrib]
  ring

theorem degree_constraint_objective (n m : ℕ) (D : ℕ → ℝ) :
    degreeConstraintLog n D (m+1) = 2*degreeObjectiveLog m m D +
      ((n:ℝ)-m)*degreePrefixLog D (m+1) := by
  unfold degreeConstraintLog degreeObjectiveLog degreePrefixLog
  rw [Finset.sum_range_succ,Finset.sum_range_succ,mul_add,Finset.mul_sum,Finset.mul_sum]
  push_cast
  have he : (∑ s ∈ Finset.range m, ((n:ℝ)+(m+1)-1-2*s)*D s) =
      ∑ s ∈ Finset.range m, (2*(((m:ℝ)-s)*D s)+((n:ℝ)-m)*D s) := by
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [he,Finset.sum_add_distrib]
  ring

/-- Exact finite optimizer identity, in logs. No sign is imposed on log D. -/
theorem degree_weighted_identity (n m : ℕ) (D : ℕ → ℝ) (h : m+2 ≤ n) :
    (∑ i ∈ Finset.range m, degreeWeight n i * degreeConstraintLog n D (i+1)) =
      degreeObjectiveLog m m D / (((n:ℝ)-m)*((n:ℝ)-m-1)) := by
  induction m with
  | zero => simp [degreeObjectiveLog]
  | succ m ih =>
    have hm : m+2 ≤ n := by omega
    rw [Finset.sum_range_succ,ih hm,degree_objective_step,degree_constraint_objective]
    unfold degreeWeight
    push_cast
    have hn : (m:ℝ)+3 ≤ n := by exact_mod_cast h
    have h0 : (n:ℝ)-m ≠ 0 := by linarith
    have h1 : (n:ℝ)-m-1 ≠ 0 := by linarith
    have h2 : (n:ℝ)-m-2 ≠ 0 := by linarith
    have h3 : (n:ℝ)-(m+1) ≠ 0 := by linarith
    have h4 : (n:ℝ)-(m+1)-1 ≠ 0 := by linarith
    field_simp
    ring


theorem degree_weight_sum (n m : ℕ) (h : m+2 ≤ n) :
    (∑ i ∈ Finset.range m, degreeWeight n i) =
      1/(2*((n:ℝ)-m)*((n:ℝ)-m-1)) - 1/(2*(n:ℝ)*((n:ℝ)-1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ,ih (by omega)]
    unfold degreeWeight
    push_cast
    have hn : (m:ℝ)+3 ≤ n := by exact_mod_cast h
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
    have h0 : (n:ℝ) ≠ 0 := by linarith
    have h1 : (n:ℝ)-1 ≠ 0 := by linarith
    have h2 : (n:ℝ)-m ≠ 0 := by linarith
    have h3 : (n:ℝ)-m-1 ≠ 0 := by linarith
    have h4 : (n:ℝ)-m-2 ≠ 0 := by linarith
    have h5 : (n:ℝ)-(m+1) ≠ 0 := by linarith
    have h6 : (n:ℝ)-(m+1)-1 ≠ 0 := by linarith
    field_simp
    ring

theorem degree_weight_moment (n m : ℕ) (h : m+2 ≤ n) :
    (∑ i ∈ Finset.range m, ((i:ℝ)+1)*degreeWeight n i) =
      (m:ℝ)*(m+1)/(2*n*((n:ℝ)-m)*((n:ℝ)-m-1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ,ih (by omega)]
    unfold degreeWeight
    push_cast
    have hn : (m:ℝ)+3 ≤ n := by exact_mod_cast h
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
    have h0 : (n:ℝ) ≠ 0 := by linarith
    have h1 : (n:ℝ)-m ≠ 0 := by linarith
    have h2 : (n:ℝ)-m-1 ≠ 0 := by linarith
    have h3 : (n:ℝ)-m-2 ≠ 0 := by linarith
    have h4 : (n:ℝ)-(m+1) ≠ 0 := by linarith
    have h5 : (n:ℝ)-(m+1)-1 ≠ 0 := by linarith
    field_simp
    ring


/-- Finite Section 4 log optimization with its exact coefficients. All degree
logs may be negative. The ONLY premises are the explicitly listed numerical
constraints, not hidden analytic estimates. -/
theorem degree_log_optimization (n m : ℕ) (D : ℕ → ℝ) (h : m+2 ≤ n)
    (x w E : ℝ)
    (hc : ∀ i < m, ((i:ℝ)+1)*x+w-E ≤ degreeConstraintLog n D (i+1)) :
    (m:ℝ)*(m+1)/(2*n)*x +
      (1/2-((n:ℝ)-m)*((n:ℝ)-m-1)/(2*n*((n:ℝ)-1)))*(w-E) ≤
        degreeObjectiveLog m m D := by
  have hweights : ∀ i ∈ Finset.range m, 0 ≤ degreeWeight n i := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have hh : (i:ℝ)+2 < n := by exact_mod_cast (show i+2<n by omega)
    unfold degreeWeight
    exact div_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
  have hh := Finset.sum_le_sum (fun i hi =>
    mul_le_mul_of_nonneg_left (hc i (Finset.mem_range.mp hi)) (hweights i hi))
  have he : (∑ i ∈ Finset.range m, degreeWeight n i * (((i:ℝ)+1)*x+w-E)) =
      (∑ i ∈ Finset.range m, ((i:ℝ)+1)*degreeWeight n i)*x +
        (∑ i ∈ Finset.range m, degreeWeight n i)*(w-E) := by
    rw [Finset.sum_mul,Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,degree_weighted_identity n m D h,degree_weight_sum n m h,degree_weight_moment n m h] at hh
  have hn : (m:ℝ)+2 ≤ n := by exact_mod_cast h
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have h0 : (n:ℝ) ≠ 0 := by linarith
  have h1 : (n:ℝ)-1 ≠ 0 := by linarith
  have h2 : (n:ℝ)-m ≠ 0 := by linarith
  have h3 : (n:ℝ)-m-1 ≠ 0 := by linarith
  have hd : 0 < ((n:ℝ)-m)*((n:ℝ)-m-1) := mul_pos (by linarith) (by linarith)
  have hmul := (le_div_iff₀ hd).mp hh
  convert hmul using 1
  field_simp


/-- Early terminal completion and exact optimization assembled. The same
objective and coefficients result for every stopping depth, including zero. -/
theorem early_terminal_degree_optimization {n m r : ℕ} (D : ℕ → ℝ)
    (hrm : r ≤ m) (hmn : m+2 ≤ n) {x w E : ℝ} (hE : 0 ≤ E)
    (hzero : ∀ s, r ≤ s → D s=0)
    (hbefore : ∀ i, 1 ≤ i → i < r → (i:ℝ)*x+w-E ≤ degreeConstraintLog n D i)
    (hterminal : x-E ≤ degreePrefixLog D r)
    (hfloor : 0 < r → -E ≤ D (r-1)) (hpacking : w ≤ E) :
    (m:ℝ)*(m+1)/(2*n)*x +
      (1/2-((n:ℝ)-m)*((n:ℝ)-m-1)/(2*n*((n:ℝ)-1)))*
        (w-((n:ℝ)+m+2)*E) ≤ degreeObjectiveLog m r D := by
  have hc := terminal_degree_constraints_complete D hrm (by omega) hE hzero
    hbefore hterminal hfloor hpacking
  have hh := degree_log_optimization n m D hmn x w (((n:ℝ)+m+2)*E)
    (fun i hi => by simpa only [Nat.cast_add,Nat.cast_one] using hc (i+1) (by omega) (by omega))
  simpa only [virtual_degree_objective D hrm hzero] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.degree_objective_step
#print axioms KakeyaTwoScale.degree_constraint_objective
#print axioms KakeyaTwoScale.degree_weighted_identity

#print axioms KakeyaTwoScale.degree_weight_sum
#print axioms KakeyaTwoScale.degree_weight_moment

#print axioms KakeyaTwoScale.degree_log_optimization

#print axioms KakeyaTwoScale.early_terminal_degree_optimization
