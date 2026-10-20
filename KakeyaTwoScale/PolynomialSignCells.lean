module
public import KakeyaTwoScale.BoxHamSandwich

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

def polynomialSignSide {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (b : Bool) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  if b then {x | 0 < MvPolynomial.eval (fun i => x i) p}
  else {x | MvPolynomial.eval (fun i => x i) p < 0}

def polynomialSignCell {n s : ℕ} (p : Fin s → MvPolynomial (Fin n) ℝ)
    (b : Fin s → Bool) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, x ∈ polynomialSignSide (p i) (b i)}

theorem isOpen_polynomialSignSide {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (b : Bool) :
    IsOpen (polynomialSignSide p b) := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) p) := by
    exact p.continuous_eval.comp (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))
  cases b <;> simp only [polynomialSignSide, Bool.false_eq_true, ↓reduceIte]
  · exact isOpen_lt hc continuous_const
  · exact isOpen_lt continuous_const hc

theorem isOpen_polynomialSignCell {n s : ℕ} (p : Fin s → MvPolynomial (Fin n) ℝ)
    (b : Fin s → Bool) : IsOpen (polynomialSignCell p b) := by
  have h := isOpen_iInter_of_finite (fun i => isOpen_polynomialSignSide (p i) (b i))
  have heq : polynomialSignCell p b = ⋂ i, polynomialSignSide (p i) (b i) := by
    ext x
    simp [polynomialSignCell]
  rw [heq]
  exact h

theorem polynomialSignCell_cons {n s : ℕ} (q : MvPolynomial (Fin n) ℝ)
    (p : Fin s → MvPolynomial (Fin n) ℝ) (b : Fin (s+1) → Bool) :
    polynomialSignCell (Fin.cons q p) b =
      polynomialSignSide q (b 0) ∩ polynomialSignCell p (fun i => b i.succ) := by
  ext x
  simp [polynomialSignCell, Fin.forall_fin_succ]

theorem polynomialSignCells_disjoint {n s : ℕ} (p : Fin s → MvPolynomial (Fin n) ℝ)
    {a b : Fin s → Bool} (hab : a ≠ b) :
    Disjoint (polynomialSignCell p a) (polynomialSignCell p b) := by
  classical
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hab
  apply Set.disjoint_left.mpr
  intro x hx hy
  have ha := hx i
  have hb := hy i
  cases hai : a i <;> cases hbi : b i <;>
    simp_all [polynomialSignSide] <;> linarith

/-- The sign regions cover precisely the complement of the product's zero
set. They need not be connected or nonempty. -/
theorem polynomialSignCells_cover {n s : ℕ} (p : Fin s → MvPolynomial (Fin n) ℝ) :
    (⋃ b, polynomialSignCell p b) =
      {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun i => x i) (∏ i, p i) ≠ 0} := by
  classical
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, map_prod, Finset.prod_ne_zero_iff]
  constructor
  · rintro ⟨b,hb⟩ i _
    have h := hb i
    cases hi : b i <;> simp [polynomialSignSide, hi] at h <;> linarith
  · intro h
    refine ⟨fun i => decide (0 < MvPolynomial.eval (fun j => x j) (p i)), ?_⟩
    intro i
    have hi := h i (Finset.mem_univ _)
    by_cases hp : 0 < MvPolynomial.eval (fun j => x j) (p i)
    · simp [polynomialSignSide, hp]
    · simp [polynomialSignSide, hp]
      exact lt_of_le_of_ne (le_of_not_gt hp) hi

end KakeyaTwoScale
#print axioms KakeyaTwoScale.isOpen_polynomialSignCell
#print axioms KakeyaTwoScale.polynomialSignCell_cons
#print axioms KakeyaTwoScale.polynomialSignCells_disjoint
#print axioms KakeyaTwoScale.polynomialSignCells_cover
