module
public import KakeyaTwoScale.PolynomialSignCells

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Simultaneous bisection iterates with a sum-of-degrees budget. The only
existence assumptions are the explicitly displayed odd-sphere zero inputs.
At stage j the codomain has 2^j coordinates, not j coordinates. -/
theorem exists_iterated_polynomial_partition (n s : ℕ) (D : ℕ → ℕ)
    (hzero : ∀ j < s, BoxOddSphereZero n (D j) (2^j))
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w) :
    ∃ p : Fin s → MvPolynomial (Fin n) ℝ,
      (∀ i, p i ≠ 0) ∧
      (∑ i, (p i).totalDegree) ≤ n * ∑ j ∈ Finset.range s, D j ∧
      ∀ b, (∫ x in polynomialSignCell p b, w x) = (∫ x, w x)/(2:ℝ)^s := by
  classical
  induction s with
  | zero =>
      refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_, ?_⟩
      · simp
      · intro b
        simp [polynomialSignCell]
  | succ s ih =>
      obtain ⟨p,hp,hdeg,hmass⟩ := ih (fun j hj => hzero j (by omega))
      let v := fun b : Fin s → Bool => (polynomialSignCell p b).indicator w
      have hv : ∀ b, Integrable (v b) := fun b =>
        hw.indicator (isOpen_polynomialSignCell p b).measurableSet
      have hz : BoxOddSphereZero n (D s) (Fintype.card (Fin s → Bool)) := by
        simpa using hzero s (Nat.lt_succ_self s)
      obtain ⟨q,hq,hqd,hbis⟩ := box_bisection_of_oddSphereZero n (D s) hz v hv
      refine ⟨Fin.cons q p, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases hq (fun j => hp j) i
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [Finset.sum_range_succ]
        nlinarith
      · intro b
        let a : Fin s → Bool := fun i => b i.succ
        have hpos := (hbis a).1
        have hneg := (hbis a).2
        dsimp [v] at hpos hneg
        rw [setIntegral_indicator (isOpen_polynomialSignCell p a).measurableSet,
          integral_indicator (isOpen_polynomialSignCell p a).measurableSet, hmass a] at hpos hneg
        rw [polynomialSignCell_cons]
        cases hb : b 0
        · change (∫ x in {x : EuclideanSpace ℝ (Fin n) |
              MvPolynomial.eval (fun i => x i) q < 0} ∩ polynomialSignCell p a, w x) = _
          rw [hneg]
          simp [pow_succ, div_div]
        · change (∫ x in {x : EuclideanSpace ℝ (Fin n) |
              0 < MvPolynomial.eval (fun i => x i) q} ∩ polynomialSignCell p a, w x) = _
          rw [hpos]
          simp [pow_succ, div_div]

/-- The iteration yields an actual nonzero product polynomial and 2^s
disjoint open sign regions covering its complement. Region connectedness
and a bound on the number of connected components are not asserted. -/
theorem exists_product_polynomial_partition (n s : ℕ) (D : ℕ → ℕ)
    (hzero : ∀ j < s, BoxOddSphereZero n (D j) (2^j))
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧
      P.totalDegree ≤ n * ∑ j ∈ Finset.range s, D j ∧
      ∃ cells : (Fin s → Bool) → Set (EuclideanSpace ℝ (Fin n)),
        (∀ b, IsOpen (cells b)) ∧
        (∀ a b, a ≠ b → Disjoint (cells a) (cells b)) ∧
        (⋃ b, cells b) = {x | MvPolynomial.eval (fun i => x i) P ≠ 0} ∧
        (∀ b, (∫ x in cells b, w x) = (∫ x, w x)/(2:ℝ)^s) := by
  classical
  obtain ⟨p,hp,hd,hm⟩ := exists_iterated_polynomial_partition n s D hzero w hw
  refine ⟨∏ i, p i, Finset.prod_ne_zero_iff.mpr (fun i _ => hp i),
    (MvPolynomial.totalDegree_finsetProd _ _).trans hd,
    polynomialSignCell p, isOpen_polynomialSignCell p, ?_, polynomialSignCells_cover p, hm⟩
  exact fun a b hab => polynomialSignCells_disjoint p hab

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_iterated_polynomial_partition
#print axioms KakeyaTwoScale.exists_product_polynomial_partition
