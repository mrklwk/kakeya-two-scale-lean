module
public import KakeyaTwoScale.OddSphereZero
public import KakeyaTwoScale.ArbitraryDegreePartition

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Proved from the reviewed Borsuk–Ulam dependency; no odd-sphere premise. -/
theorem box_bisection (n D : ℕ) {κ : Type*} [Fintype κ]
    (hd : Fintype.card κ < (D+1)^n)
    (w : κ → EuclideanSpace ℝ (Fin n) → ℝ) (hw : ∀ j, Integrable (w j)) :
    ∃ p : MvPolynomial (Fin n) ℝ, p≠0 ∧ p.totalDegree≤n*D ∧ ∀ j,
      (∫ x in {x : EuclideanSpace ℝ (Fin n) | 0<MvPolynomial.eval (fun i => x i) p}, w j x)=
        (∫ x, w j x)/2 ∧
      (∫ x in {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun i => x i) p<0}, w j x)=
        (∫ x, w j x)/2 := by
  exact box_bisection_of_oddSphereZero n D (boxOddSphereZero_of_dimension n D _ hd) w hw

/-- Proved from the reviewed Borsuk–Ulam dependency; no odd-sphere premise. -/
theorem exists_iterated_polynomial_partition_of_dimensions (n s : ℕ) (D : ℕ → ℕ)
    (hd : ∀ j < s, 2^j < (D j+1)^n)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w) :
    ∃ p : Fin s → MvPolynomial (Fin n) ℝ,
      (∀ i, p i ≠ 0) ∧
      (∑ i, (p i).totalDegree) ≤ n * ∑ j ∈ Finset.range s, D j ∧
      ∀ b, (∫ x in polynomialSignCell p b, w x) = (∫ x, w x)/(2:ℝ)^s := by
  exact exists_iterated_polynomial_partition n s D (fun j hj => boxOddSphereZero_of_dimension n (D j) (2^j) (hd j hj)) w hw

/-- Proved from the reviewed Borsuk–Ulam dependency; no odd-sphere premise. -/
theorem exists_product_polynomial_partition_of_dimensions (n s : ℕ) (D : ℕ → ℕ)
    (hd : ∀ j < s, 2^j < (D j+1)^n)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧
      P.totalDegree ≤ n * ∑ j ∈ Finset.range s, D j ∧
      ∃ cells : (Fin s → Bool) → Set (EuclideanSpace ℝ (Fin n)),
        (∀ b, IsOpen (cells b)) ∧
        (∀ a b, a ≠ b → Disjoint (cells a) (cells b)) ∧
        (⋃ b, cells b) = {x | MvPolynomial.eval (fun i => x i) P ≠ 0} ∧
        (∀ b, (∫ x in cells b, w x) = (∫ x, w x)/(2:ℝ)^s) := by
  exact exists_product_polynomial_partition n s D (fun j hj => boxOddSphereZero_of_dimension n (D j) (2^j) (hd j hj)) w hw

/-- Proved from the reviewed Borsuk–Ulam dependency; no odd-sphere premise. -/
theorem exists_dyadic_polynomial_partition_unconditional (n : ℕ) (hn : 0 < n) (t : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : MeasureTheory.Integrable w) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧ P.totalDegree ≤ 2*n^2*2^t ∧
      ∃ cells : (Fin (n*t) → Bool) → Set (EuclideanSpace ℝ (Fin n)),
        (∀ b, IsOpen (cells b)) ∧
        (∀ a b, a ≠ b → Disjoint (cells a) (cells b)) ∧
        (⋃ b, cells b) = {x | MvPolynomial.eval (fun i => x i) P ≠ 0} ∧
        (∀ b, (∫ x in cells b, w x) = (∫ x, w x)/(2:ℝ)^(n*t)) := by
  exact exists_dyadic_polynomial_partition n hn t
    (fun j _ => boxOddSphereZero_of_dimension n _ _ (partitionBoxDegree_dimension n hn j)) w hw

/-- Proved from the reviewed Borsuk–Ulam dependency; no odd-sphere premise. -/
theorem exists_componentwise_polynomial_partition_of_dimensions (n s : ℕ) (D : ℕ → ℕ)
    (hd : ∀ j < s, 2^j < (D j+1)^n)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w) (hwn : ∀ x, 0 ≤ w x) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧
      P.totalDegree ≤ n * ∑ j ∈ Finset.range s, D j ∧
      volume {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun i => x i) P = 0} = 0 ∧
      ∀ x, MvPolynomial.eval (fun i => x i) P ≠ 0 →
        (∫ y in connectedComponentIn {y | MvPolynomial.eval (fun i => y i) P ≠ 0} x, w y)
          ≤ (∫ y, w y)/(2:ℝ)^s := by
  exact exists_componentwise_polynomial_partition n s D
    (fun j hj => boxOddSphereZero_of_dimension n _ _ (hd j hj)) w hw hwn

/-- Proved from the reviewed Borsuk–Ulam dependency; no odd-sphere premise. -/
theorem exists_dyadic_component_partition
    (n : ℕ) (hn : 0 < n) (t : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w) (hwn : ∀ x, 0 ≤ w x) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧ P.totalDegree ≤ 2*n^2*2^t ∧
      volume {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun i => x i) P = 0} = 0 ∧
      ∀ x, MvPolynomial.eval (fun i => x i) P ≠ 0 →
        (∫ y in connectedComponentIn {y | MvPolynomial.eval (fun i => y i) P ≠ 0} x, w y)
          ≤ (∫ y, w y)/(2:ℝ)^(n*t) := by
  exact exists_dyadic_component_partition_of_oddSphereZero n hn t (boxOddSphereZero_of_dimension n) w hw hwn

/-- Proved from the reviewed Borsuk–Ulam dependency; no odd-sphere premise. -/
theorem exists_degree_budget_component_partition
    (n : ℕ) (hn : 0 < n) (D : ℕ) (hD : 0 < D)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w) (hwn : ∀ x, 0 ≤ w x) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧ P.totalDegree ≤ D ∧
      volume {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun i => x i) P = 0} = 0 ∧
      ∀ x, MvPolynomial.eval (fun i => x i) P ≠ 0 →
        (∫ y in connectedComponentIn {y | MvPolynomial.eval (fun i => y i) P ≠ 0} x, w y)
          ≤ ((4*(n:ℝ)^2)/(D:ℝ))^n*(∫ y, w y) := by
  exact exists_degree_budget_component_partition_of_oddSphereZero n hn D hD (boxOddSphereZero_of_dimension n) w hw hwn

end KakeyaTwoScale
#print axioms KakeyaTwoScale.box_bisection
#print axioms KakeyaTwoScale.exists_iterated_polynomial_partition_of_dimensions
#print axioms KakeyaTwoScale.exists_product_polynomial_partition_of_dimensions
#print axioms KakeyaTwoScale.exists_dyadic_polynomial_partition_unconditional
#print axioms KakeyaTwoScale.exists_componentwise_polynomial_partition_of_dimensions
#print axioms KakeyaTwoScale.exists_dyadic_component_partition
#print axioms KakeyaTwoScale.exists_degree_budget_component_partition
