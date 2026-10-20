module
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Tactic

@[expose] public section

open Matrix
noncomputable section
namespace KakeyaTwoScale

/-- Actual Euclidean coordinate graph of the negative slope matrix. The
codomain is Euclidean on the sum index, not the sup-metric product. -/
def euclideanGraphLinear {b c : Type*} [Fintype b] [Fintype c] [DecidableEq b]
    (L : Matrix c b ℝ) : EuclideanSpace ℝ b →ₗ[ℝ] EuclideanSpace ℝ (b ⊕ c) :=
  (Matrix.fromRows 1 (-L)).toEuclideanLin

theorem euclideanGraphLinear_inl {b c : Type*} [Fintype b] [Fintype c] [DecidableEq b]
    (L : Matrix c b ℝ) (x : EuclideanSpace ℝ b) (i : b) :
    euclideanGraphLinear L x (Sum.inl i) = x i := by
  simp [euclideanGraphLinear, Matrix.toLpLin_apply, Matrix.fromRows_mulVec]

theorem euclideanGraphLinear_inr {b c : Type*} [Fintype b] [Fintype c] [DecidableEq b]
    (L : Matrix c b ℝ) (x : EuclideanSpace ℝ b) (i : c) :
    euclideanGraphLinear L x (Sum.inr i) = -(L.mulVec (WithLp.ofLp x) i) := by
  simp [euclideanGraphLinear, Matrix.toLpLin_apply, Matrix.fromRows_mulVec, Matrix.neg_mulVec]

theorem euclideanGraphLinear_injective {b c : Type*}
    [Fintype b] [Fintype c] [DecidableEq b] (L : Matrix c b ℝ) :
    Function.Injective (euclideanGraphLinear L) := by
  intro x y h
  apply PiLp.ext
  intro i
  have hi := congrArg (fun v : EuclideanSpace ℝ (b ⊕ c) => v (Sum.inl i)) h
  simpa only [euclideanGraphLinear_inl] using hi

/-- The squared norm determinant of a rectangular Euclidean matrix map is its
actual Gram determinant. This bridges the matrix and normed-space APIs. -/
theorem matrix_toEuclideanLin_normDet_sq {b c : Type*}
    [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c]
    (M : Matrix c b ℝ) :
    M.toEuclideanLin.normDet ^ 2 = (M.transpose * M).det := by
  have h := M.toEuclideanLin.normDet_sq
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h
  rw [← Matrix.toLpLin_mul_same] at h
  rw [LinearMap.det_toLpLin] at h
  simpa using h

/-- Exact graph-volume identity with the genuine Euclidean norm. -/
theorem euclideanGraphLinear_normDet_sq {b c : Type*}
    [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c]
    (L : Matrix c b ℝ) :
    (euclideanGraphLinear L).normDet ^ 2 = (1 + L.transpose * L).det := by
  rw [euclideanGraphLinear, matrix_toEuclideanLin_normDet_sq,
    Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows]
  simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.euclideanGraphLinear_inl
#print axioms KakeyaTwoScale.euclideanGraphLinear_inr
#print axioms KakeyaTwoScale.euclideanGraphLinear_injective
#print axioms KakeyaTwoScale.matrix_toEuclideanLin_normDet_sq
#print axioms KakeyaTwoScale.euclideanGraphLinear_normDet_sq
