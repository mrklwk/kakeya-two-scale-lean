module
public import KakeyaTwoScale.BisectionIntegralAssembly

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

def coordinateAreaSum {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (A : DisjointChartAtlas n {x | MvPolynomial.eval x P=0}) : ℝ≥0∞ :=
  ∑ j : Fin (n+1), (A.restrict (coordinateEuclideanBall (n+1) 1)
    (coordinateEuclideanBall_open _ _).measurableSet).directionalArea (Pi.single j 1)

theorem weightedCoordinateArea_le {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (A : DisjointChartAtlas n {x | MvPolynomial.eval x P=0})
    (α b : ℝ) (hα : α ≤ 1) (hb : b ≤ 1) :
    weightedCoordinateArea P A α b ≤ (2:ℝ≥0∞)^(n+2)*coordinateAreaSum P A := by
  have ha : ENNReal.ofReal (2*α) ≤ 2 := by
    have h := ENNReal.ofReal_le_ofReal (show 2*α ≤ 2 by linarith)
    simpa using h
  have hbb : ENNReal.ofReal (2*b) ≤ 2 := by
    have h := ENNReal.ofReal_le_ofReal (show 2*b ≤ 2 by linarith)
    simpa using h
  unfold weightedCoordinateArea coordinateAreaSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  refine mul_le_mul ?_ le_rfl zero_le zero_le
  calc
    _ ≤ (2:ℝ≥0∞)^(j.val+1)*2^(n+1-j.val) := by gcongr
    _ = _ := by rw [← pow_add]; congr 1; omega

end KakeyaTwoScale
#print axioms KakeyaTwoScale.weightedCoordinateArea_le
