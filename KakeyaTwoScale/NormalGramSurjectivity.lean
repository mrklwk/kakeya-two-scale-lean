module
public import KakeyaTwoScale.CoordinateNormalProjection

@[expose] public section

open Matrix
noncomputable section
namespace KakeyaTwoScale

/-- Full normal rank makes the actual normal Gram determinant positive,
without choosing any particular invertible coordinate minor. -/
theorem normalGram_det_pos_of_range {b c : Type*} [Fintype b] [Fintype c]
    [DecidableEq b] [DecidableEq c]
    (K : Matrix c b ℝ) (H : Matrix c c ℝ)
    (hA : (coordinateNormalLinear K H).range = ⊤) :
    0 < (K*K.transpose+H*H.transpose).det := by
  let A := (Matrix.fromCols K H).toEuclideanLin
  have hr : A.range = ⊤ := hA
  have hk : A.adjoint.ker = ⊥ := by
    rw [← LinearMap.orthogonal_range, hr]
    simp
  have hn : A.adjoint.normDet ≠ 0 := by
    intro hz
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp hz) hk
  have he := matrix_toEuclideanLin_normDet_sq (Matrix.fromCols K H).transpose
  have ha : (Matrix.fromCols K H).transpose.toEuclideanLin = A.adjoint := by
    simpa [A] using Matrix.toEuclideanLin_conjTranspose_eq_adjoint (Matrix.fromCols K H)
  rw [ha] at he
  simp only [Matrix.transpose_transpose, Matrix.transpose_fromCols, Matrix.transpose_fromRows,
    Matrix.fromCols_mul_fromRows] at he
  rw [← he]
  exact sq_pos_of_ne_zero hn

end KakeyaTwoScale
#print axioms KakeyaTwoScale.normalGram_det_pos_of_range
