module
public import KakeyaTwoScale.RelativeRegularFactorSelection
public import KakeyaTwoScale.UnconditionalPolynomialPartition

@[expose] public section

open MvPolynomial MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- A genuine iterated ham-sandwich partition with individually transverse
cylindrical factors on the given regular polynomial fiber. Constant shifts
preserve the original degree budget. -/
theorem exists_relative_regular_iterated_partition {b c : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (hP : ∀ x, rectangularPolynomialMap P x=0 →
      (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤)
    (s : ℕ) (D : ℕ → ℕ) (hd : ∀ j < s, 2^j < (D j+1)^b)
    (w : EuclideanSpace ℝ (Fin b) → ℝ) (hw : Integrable w)
    (hH : 0 < ∫ x, w x) :
    ∃ q : Fin s → MvPolynomial (Fin b) ℝ,
      (∀ i, q i ≠ 0) ∧
      (∑ i, (q i).totalDegree) ≤ b*(∑ j ∈ Finset.range s, D j) ∧
      (∀ i x, rectangularPolynomialMap P x=0 →
        eval (coordinateBaseProjection x) (q i)=0 →
        (fderiv ℝ (fun y => (rectangularPolynomialMap P y,
          eval (coordinateBaseProjection y) (q i))) x).range=⊤) ∧
      (∀ sign : Fin s → Bool,
        ((∫ x, w x)/(2:ℝ)^s)/2 < (∫ x in polynomialSignCell q sign, w x) ∧
        (∫ x in polynomialSignCell q sign, w x) < 2*((∫ x, w x)/(2:ℝ)^s)) := by
  classical
  obtain ⟨q,hq,hdeg,hmass⟩ := exists_iterated_polynomial_partition_of_dimensions b s D hd w hw
  let m : ℝ := (∫ x, w x)/(2:ℝ)^s
  have hm : 0 < m := div_pos hH (by positivity)
  obtain ⟨shift,_,hne,hdegree,hclose,hreg⟩ :=
    exists_polynomial_relative_regular_factor_shifts P hP q hq w hw 1 (m/2)
      (by norm_num) (half_pos hm)
  refine ⟨fun i => q i+C (shift i),hne,?_,hreg,?_⟩
  · exact (Finset.sum_le_sum (fun i _ => hdegree i)).trans hdeg
  · intro sign
    have hc := hclose sign
    rw [hmass sign,abs_lt] at hc
    change -(m/2) < (∫ x in polynomialSignCell (fun i => q i+C (shift i)) sign, w x)-m ∧
      (∫ x in polynomialSignCell (fun i => q i+C (shift i)) sign, w x)-m < m/2 at hc
    constructor <;> dsimp [m] at * <;> linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_relative_regular_iterated_partition
