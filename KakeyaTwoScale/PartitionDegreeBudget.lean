module
public import KakeyaTwoScale.IteratedPolynomialPartition

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Degree-box side length for the j-th simultaneous bisection. -/
def partitionBoxDegree (n j : ℕ) : ℕ := 2^(j/n+1)

/-- The exact coefficient dimension exceeds the number of densities at
every stage. This arithmetic statement does not supply the topological zero. -/
theorem partitionBoxDegree_dimension (n : ℕ) (hn : 0 < n) (j : ℕ) :
    2^j < (partitionBoxDegree n j + 1)^n := by
  have hj : j < n*(j/n+1) := Nat.lt_mul_div_succ j hn
  calc
    2^j < 2^(n*(j/n+1)) := Nat.pow_lt_pow_right (by omega) hj
    _ = (partitionBoxDegree n j)^n := by rw [partitionBoxDegree, ← pow_mul, Nat.mul_comm]
    _ ≤ (partitionBoxDegree n j+1)^n := Nat.pow_le_pow_left (Nat.le_succ _) n

/-- Summing complete blocks of n stages gives a geometric, rather than
linear-times-geometric, degree budget. -/
theorem partitionBoxDegree_sum (n : ℕ) (hn : 0 < n) (t : ℕ) :
    (∑ j ∈ Finset.range (n*t), partitionBoxDegree n j) + 2*n = 2*n*2^t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.mul_succ, Finset.sum_range_add]
      have hblock : (∑ j ∈ Finset.range n, partitionBoxDegree n (n*t+j)) = n*2^(t+1) := by
        calc
          _ = ∑ _j ∈ Finset.range n, 2^(t+1) := by
            apply Finset.sum_congr rfl
            intro j hj
            dsimp [partitionBoxDegree]
            rw [Nat.add_comm (n*t), Nat.add_mul_div_left _ _ hn,
              Nat.div_eq_of_lt (Finset.mem_range.mp hj), Nat.zero_add]
          _ = _ := by simp
      rw [hblock, pow_succ]
      nlinarith

/-- Conditional quantitative partitioning at dyadic polynomial scale 2^t:
2^(n*t) equal-mass sign regions and total degree at most 2*n²*2^t.
The higher-dimensional Borsuk–Ulam inputs remain explicit premises. -/
theorem exists_dyadic_polynomial_partition (n : ℕ) (hn : 0 < n) (t : ℕ)
    (hzero : ∀ j < n*t, BoxOddSphereZero n (partitionBoxDegree n j) (2^j))
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : MeasureTheory.Integrable w) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧ P.totalDegree ≤ 2*n^2*2^t ∧
      ∃ cells : (Fin (n*t) → Bool) → Set (EuclideanSpace ℝ (Fin n)),
        (∀ b, IsOpen (cells b)) ∧
        (∀ a b, a ≠ b → Disjoint (cells a) (cells b)) ∧
        (⋃ b, cells b) = {x | MvPolynomial.eval (fun i => x i) P ≠ 0} ∧
        (∀ b, (∫ x in cells b, w x) = (∫ x, w x)/(2:ℝ)^(n*t)) := by
  obtain ⟨P,hP,hd,cells,hcells⟩ := exists_product_polynomial_partition n (n*t)
    (partitionBoxDegree n) hzero w hw
  refine ⟨P,hP,?_,cells,hcells⟩
  have hsum := partitionBoxDegree_sum n hn t
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.partitionBoxDegree_dimension
#print axioms KakeyaTwoScale.partitionBoxDegree_sum
#print axioms KakeyaTwoScale.exists_dyadic_polynomial_partition
