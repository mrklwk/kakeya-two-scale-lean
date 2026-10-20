module
public import KakeyaTwoScale.OpenJacobianMultiplicity
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

open MeasureTheory Set Matrix
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Coordinate projection onto the transverse base of the first coordinate axis. -/
def transverseProjection (n : ℕ) : (Fin (n+1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

/-- The signed chart cofactor evaluated on an ambient direction. Rows contain
that direction followed by the actual differential applied to the coordinate basis. -/
def chartCofactor {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ)) (u : Fin (n+1) → ℝ) : ℝ :=
  Matrix.det (Matrix.of (Fin.cons u (fun j => A (Pi.single j 1))))

/-- Exact projected-Jacobian/cofactor normalization for the first unit axis. -/
theorem chartCofactor_first_axis {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ)) :
    chartCofactor A (Pi.single 0 1) = ((transverseProjection n).comp A).det := by
  rw [chartCofactor, Matrix.det_succ_row_zero]
  simp only [Matrix.of_apply, Fin.cons_zero]
  rw [Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, Pi.single_eq_same, one_mul]
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix']
    apply Eq.trans _ (Matrix.det_transpose _)
    congr 1
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.chartCofactor_first_axis
