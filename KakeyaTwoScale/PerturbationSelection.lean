module
public import KakeyaTwoScale.PerturbationSuperlevels

@[expose] public section

open MvPolynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- A positive number strictly below every member of a finite positive family,
including the empty family. -/
theorem finite_positive_lower_bound {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (hv : ∀ i, 0 < v i) : ∃ a : ℝ, 0 < a ∧ ∀ i, a < v i := by
  classical
  have h : ∀ A : Finset ι, ∃ a : ℝ, 0 < a ∧ ∀ i ∈ A, a < v i := by
    intro A
    induction A using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert i A hi ih =>
      obtain ⟨a,ha,hA⟩ := ih
      obtain ⟨b,hb,hbi⟩ := exists_between (hv i)
      refine ⟨min a b,lt_min ha hb,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (min_le_right _ _).trans_lt hbi
      · exact (min_le_left _ _).trans_lt (hA j hj)
  obtain ⟨a,ha,hall⟩ := h Finset.univ
  exact ⟨a,ha,fun i => hall i (Finset.mem_univ i)⟩

/-- One positive perturbation and positive superlevel threshold preserve any
finite family of points outside the zero set. Global component finiteness is
not used to make this choice. -/
theorem exists_positive_perturbation_superlevel {ι : Type*} [Fintype ι] {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (D : ℕ) (x : ι → Fin n → ℝ)
    (hx : ∀ j, eval (x j) P ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ a : ℝ, 0 < a ∧ ∀ j,
      a < eval (x j) (coercivePolynomialPerturbation P D ε) := by
  let A : ι → ℝ := fun j => 1 + ∑ i : Fin n, (x j i)^(2*D+2)
  have hA : ∀ j, 0 < A j := by
    intro j
    have he : Even (2*D+2) := ⟨D+1,by omega⟩
    have hsum := Finset.sum_nonneg (s := Finset.univ) (fun i _ => he.pow_nonneg (x j i))
    dsimp [A]
    linarith
  obtain ⟨ε,hε,he⟩ := finite_positive_lower_bound
    (fun j => (eval (x j) P)^2 / A j) (fun j => div_pos (sq_pos_of_ne_zero (hx j)) (hA j))
  have hpos : ∀ j, 0 < eval (x j) (coercivePolynomialPerturbation P D ε) := by
    intro j
    have h := (lt_div_iff₀ (hA j)).mp (he j)
    simpa only [coercivePolynomialPerturbation,map_sub,map_mul,map_add,map_pow,
      eval_C,map_one,map_sum,eval_X,sub_pos] using h
  obtain ⟨a,ha,hall⟩ := finite_positive_lower_bound _ hpos
  exact ⟨ε,hε,a,ha,hall⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_positive_lower_bound
#print axioms KakeyaTwoScale.exists_positive_perturbation_superlevel
