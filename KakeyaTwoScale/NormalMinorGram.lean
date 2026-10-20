module
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

open Matrix
noncomputable section
namespace KakeyaTwoScale

/-- A normal block written through a graph slope has Gram determinant equal
 to the vertical minor squared times the tangent graph Gram determinant. -/
theorem normal_block_gram_det {b c : Type*} [Fintype b] [Fintype c]
    [DecidableEq b] [DecidableEq c]
    (H : Matrix c c ℝ) (L : Matrix c b ℝ) :
    Matrix.det ((H*L)*(H*L).transpose + H*H.transpose) =
      H.det^2 * Matrix.det (1 + L.transpose*L) := by
  have he : (H*L)*(H*L).transpose + H*H.transpose =
      H * (1+L*L.transpose) * H.transpose := by
    rw [Matrix.transpose_mul, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    abel
  rw [he, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_one_add_mul_comm L L.transpose]
  ring

/-- The precise polynomial-normal-minor ratio for a coordinate graph. The
normal matrix has blocks K,H; no assumed Gram-ratio identity is used. -/
theorem normal_minor_graph_gram_ratio {b c : Type*} [Fintype b] [Fintype c]
    [DecidableEq b] [DecidableEq c]
    (K : Matrix c b ℝ) (H : Matrix c c ℝ) (hH : H.det ≠ 0) :
    Matrix.det (1 + (H⁻¹*K).transpose*(H⁻¹*K)) =
      Matrix.det (K*K.transpose+H*H.transpose) / H.det^2 := by
  have hunit : IsUnit H.det := isUnit_iff_ne_zero.mpr hH
  have he : H*(H⁻¹*K) = K := Matrix.mul_nonsing_inv_cancel_left H K hunit
  have h := normal_block_gram_det H (H⁻¹*K)
  rw [he] at h
  apply (eq_div_iff (pow_ne_zero 2 hH)).mpr
  nlinarith [h]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.normal_block_gram_det
#print axioms KakeyaTwoScale.normal_minor_graph_gram_ratio
