module
public import KakeyaTwoScale.PolynomialSignCells
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- The union of the actual zero loci of the partition factors. -/
def polynomialFactorZeros {n s : ℕ} (p : Fin s → MvPolynomial (Fin n) ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∃ i, MvPolynomial.eval (fun j => x j) (p i) = 0}

theorem polynomialFactorZeros_eq_union {n s : ℕ} (p : Fin s → MvPolynomial (Fin n) ℝ) :
    polynomialFactorZeros p = ⋃ i, {x : EuclideanSpace ℝ (Fin n) |
      MvPolynomial.eval (fun j => x j) (p i) = 0} := by
  ext x
  simp [polynomialFactorZeros]

/-- A continuous real function that never vanishes on a preconnected set has
one strict sign throughout that set. Empty sets need no special hypothesis. -/
theorem preconnected_strict_sign {X : Type*} [TopologicalSpace X]
    (Q : Set X) (hQ : IsPreconnected Q) (f : X → ℝ) (hf : ContinuousOn f Q)
    (hnz : ∀ x ∈ Q, f x ≠ 0) :
    (∀ x ∈ Q, 0 < f x) ∨ (∀ x ∈ Q, f x < 0) := by
  by_cases hp : ∀ x ∈ Q, 0 < f x
  · exact Or.inl hp
  · right
    push Not at hp
    obtain ⟨a,ha,hfa⟩ := hp
    have hneg : f a < 0 := lt_of_le_of_ne hfa (hnz a ha)
    intro b hb
    by_contra hbneg
    have hfb : 0 ≤ f b := le_of_not_gt hbneg
    obtain ⟨z,hz,hzero⟩ := hQ.intermediate_value ha hb hf ⟨hneg.le,hfb⟩
    exact hnz z hz hzero

/-- A preconnected actual set either projects wholly into one sign cell, or
some actual point of it projects onto a factor's zero set. The projection only
needs to be continuous; continuous linear projections are included. -/
theorem preconnected_polynomial_cell_or_zero {X : Type*} [TopologicalSpace X]
    {n s : ℕ} (Q : Set X) (hQ : IsPreconnected Q)
    (π : X → EuclideanSpace ℝ (Fin n)) (hπ : Continuous π)
    (p : Fin s → MvPolynomial (Fin n) ℝ) :
    (∃ b : Fin s → Bool, Q ⊆ π ⁻¹' polynomialSignCell p b) ∨
      ∃ x ∈ Q, π x ∈ polynomialFactorZeros p := by
  by_cases hz : ∃ x ∈ Q, π x ∈ polynomialFactorZeros p
  · exact Or.inr hz
  · left
    have hsign (i : Fin s) :
        (∀ x ∈ Q, 0 < MvPolynomial.eval (fun j => π x j) (p i)) ∨
        (∀ x ∈ Q, MvPolynomial.eval (fun j => π x j) (p i) < 0) := by
      apply preconnected_strict_sign Q hQ
      · exact ((p i).continuous_eval.comp
          ((PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).comp hπ)).continuousOn
      · intro x hx he
        exact hz ⟨x,hx,i,he⟩
    let b : Fin s → Bool := fun i => decide
      (∀ x ∈ Q, 0 < MvPolynomial.eval (fun j => π x j) (p i))
    refine ⟨b,?_⟩
    intro x hx i
    by_cases hi : ∀ x ∈ Q, 0 < MvPolynomial.eval (fun j => π x j) (p i)
    · have hbi : b i = true := decide_eq_true hi
      simp only [polynomialSignSide, hbi, ite_true, Set.mem_ofPred_eq]
      exact hi x hx
    · have hbi : b i = false := decide_eq_false hi
      simp only [polynomialSignSide, hbi, Bool.false_eq_true, ite_false, Set.mem_ofPred_eq]
      exact (hsign i).resolve_left hi x hx

/-- Avoiding the actual buffered factor-zero set forces the entire projected
preconnected piece into one cell. This is not a pointwise choice of cells. -/
theorem preconnected_polynomial_cell_of_avoids_buffer {X : Type*} [TopologicalSpace X]
    {n s : ℕ} (Q : Set X) (hQ : IsPreconnected Q)
    (π : X → EuclideanSpace ℝ (Fin n)) (hπ : Continuous π)
    (p : Fin s → MvPolynomial (Fin n) ℝ) (r : ℝ) (hr : 0 < r)
    (havoid : ∀ x ∈ Q, π x ∉ Metric.thickening r (polynomialFactorZeros p)) :
    ∃ b : Fin s → Bool, Q ⊆ π ⁻¹' polynomialSignCell p b := by
  rcases preconnected_polynomial_cell_or_zero Q hQ π hπ p with hcell | ⟨x,hx,hzero⟩
  · exact hcell
  · exact (havoid x hx (Metric.self_subset_thickening hr _ hzero)).elim

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomialFactorZeros_eq_union
#print axioms KakeyaTwoScale.preconnected_strict_sign
#print axioms KakeyaTwoScale.preconnected_polynomial_cell_or_zero
#print axioms KakeyaTwoScale.preconnected_polynomial_cell_of_avoids_buffer
