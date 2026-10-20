module
public import KakeyaTwoScale.NormalMinorGram
public import KakeyaTwoScale.EuclideanGraphGram
public import KakeyaTwoScale.TangentProjectionCapture

@[expose] public section

open Matrix
noncomputable section
namespace KakeyaTwoScale
variable {b c : Type*} [Fintype b] [Fintype c] [DecidableEq b] [DecidableEq c]

def coordinateNormalLinear (K : Matrix c b ℝ) (H : Matrix c c ℝ) :
    EuclideanSpace ℝ (b ⊕ c) →L[ℝ] EuclideanSpace ℝ c :=
  (Matrix.fromCols K H).toEuclideanLin.toContinuousLinearMap

def coordinateBaseProjection : EuclideanSpace ℝ (b ⊕ c) →L[ℝ] EuclideanSpace ℝ b :=
  (Matrix.fromCols (1 : Matrix b b ℝ) (0 : Matrix b c ℝ)).toEuclideanLin.toContinuousLinearMap

@[simp] theorem coordinateBaseProjection_apply (x : EuclideanSpace ℝ (b ⊕ c)) (i : b) :
    coordinateBaseProjection x i = x (Sum.inl i) := by
  simp [coordinateBaseProjection, Matrix.toLpLin_apply, Matrix.fromCols_mulVec, Function.comp_def]

@[simp] theorem coordinateNormalLinear_apply (K : Matrix c b ℝ) (H : Matrix c c ℝ)
    (x : EuclideanSpace ℝ (b ⊕ c)) (i : c) :
    coordinateNormalLinear K H x i =
      K.mulVec (fun j => x (Sum.inl j)) i + H.mulVec (fun j => x (Sum.inr j)) i := by
  simp [coordinateNormalLinear, Matrix.toLpLin_apply, Matrix.fromCols_mulVec, Function.comp_def]

theorem coordinate_graph_mem_kernel (K : Matrix c b ℝ) (H : Matrix c c ℝ)
    (hH : H.det ≠ 0) (x : EuclideanSpace ℝ b) :
    euclideanGraphLinear (H⁻¹*K) x ∈ (coordinateNormalLinear K H).ker := by
  have he := Matrix.mul_nonsing_inv_cancel_left H K (isUnit_iff_ne_zero.mpr hH)
  change coordinateNormalLinear K H (euclideanGraphLinear (H⁻¹*K) x) = 0
  apply PiLp.ext
  intro i
  simp only [coordinateNormalLinear_apply, euclideanGraphLinear_inl, euclideanGraphLinear_inr]
  change K.mulVec (WithLp.ofLp x) i + H.mulVec (-(H⁻¹*K).mulVec (WithLp.ofLp x)) i = 0
  rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, he]
  simp

theorem coordinate_kernel_graph (K : Matrix c b ℝ) (H : Matrix c c ℝ)
    (hH : H.det ≠ 0) (x : (coordinateNormalLinear K H).ker) :
    euclideanGraphLinear (H⁻¹*K) (coordinateBaseProjection (x : EuclideanSpace ℝ (b ⊕ c))) = x := by
  have hx : K.mulVec (fun j => x.val (Sum.inl j)) +
      H.mulVec (fun j => x.val (Sum.inr j)) = 0 := by
    funext i
    have hh : coordinateNormalLinear K H (x : EuclideanSpace ℝ (b ⊕ c)) = 0 := x.property
    have hi := congrArg (fun z : EuclideanSpace ℝ c => z i) hh
    rw [coordinateNormalLinear_apply] at hi
    exact hi
  have hv := congrArg (fun v => H⁻¹.mulVec v) hx
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr hH), Matrix.one_mulVec,
    Matrix.mulVec_zero] at hv
  apply PiLp.ext
  intro i
  cases i with
  | inl i => simp only [euclideanGraphLinear_inl, coordinateBaseProjection_apply]
  | inr i =>
    simp only [euclideanGraphLinear_inr]
    have hh := congrFun hv i
    have hc : WithLp.ofLp (coordinateBaseProjection (x : EuclideanSpace ℝ (b ⊕ c))) =
        fun j => x.val (Sum.inl j) := by funext j; simp
    rw [hc]
    change -((H⁻¹*K).mulVec (fun j => x.val (Sum.inl j)) i) = x.val (Sum.inr i)
    change (H⁻¹*K).mulVec (fun j => x.val (Sum.inl j)) i + x.val (Sum.inr i) = 0 at hh
    linarith

/-- The coordinate tangent kernel is the actual graph of the solved normal block. -/
def coordinateKernelEquiv (K : Matrix c b ℝ) (H : Matrix c c ℝ) (hH : H.det ≠ 0) :
    EuclideanSpace ℝ b ≃ₗ[ℝ] (coordinateNormalLinear K H).ker :=
  LinearEquiv.ofBijective
    ((euclideanGraphLinear (H⁻¹*K)).codRestrict _ (coordinate_graph_mem_kernel K H hH))
    ⟨fun _x _y h => euclideanGraphLinear_injective _ (congrArg Subtype.val h),
      fun x => ⟨coordinateBaseProjection (x : EuclideanSpace ℝ (b ⊕ c)),
        Subtype.ext (coordinate_kernel_graph K H hH x)⟩⟩

/-- Exact normal-minor formula for the actual tangent projection determinant. -/
theorem coordinate_tangent_projection_normDet_sq (K : Matrix c b ℝ) (H : Matrix c c ℝ)
    (hH : H.det ≠ 0) :
    (tangentProjection (coordinateNormalLinear K H) coordinateBaseProjection).toLinearMap.normDet^2 =
      H.det^2 / (K*K.transpose+H*H.transpose).det := by
  let e := coordinateKernelEquiv K H hH
  let T := (tangentProjection (coordinateNormalLinear K H) coordinateBaseProjection).toLinearMap
  have hcomp : T.comp e.toLinearMap = LinearMap.id := by
    ext x i
    change coordinateBaseProjection (euclideanGraphLinear (H⁻¹*K) x) i = x i
    rw [coordinateBaseProjection_apply, euclideanGraphLinear_inl]
  have hdet := LinearMap.normDet_comp_of_finrank_eq e.toLinearMap T e.finrank_eq
  rw [hcomp, LinearMap.normDet_id] at hdet
  have he : e.toLinearMap.normDet = (euclideanGraphLinear (H⁻¹*K)).normDet :=
    LinearMap.normDet_codRestrict _
  rw [he] at hdet
  have hs : T.normDet^2 * (euclideanGraphLinear (H⁻¹*K)).normDet^2 = 1 := by nlinarith [sq_nonneg (T.normDet * (euclideanGraphLinear (H⁻¹*K)).normDet - 1)]
  rw [euclideanGraphLinear_normDet_sq, normal_minor_graph_gram_ratio K H hH] at hs
  have hden : (K*K.transpose+H*H.transpose).det ≠ 0 := by
    intro hz
    rw [hz, zero_div, mul_zero] at hs
    norm_num at hs
  apply (eq_div_iff hden).mpr
  field_simp [hH] at hs
  exact hs

/-- The base coordinate projection is a contraction in the genuine Euclidean norm. -/
theorem coordinateBaseProjection_norm_le :
    ‖(coordinateBaseProjection : EuclideanSpace ℝ (b ⊕ c) →L[ℝ] EuclideanSpace ℝ b)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have hs : ‖coordinateBaseProjection x‖^2 ≤ ‖x‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
    simp only [coordinateBaseProjection_apply]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  simp only [one_mul]
  nlinarith [norm_nonneg x, norm_nonneg (coordinateBaseProjection x)]

/-- A nonzero vertical minor proves surjectivity of the actual normal derivative. -/
theorem coordinateNormalLinear_range (K : Matrix c b ℝ) (H : Matrix c c ℝ)
    (hH : H.det ≠ 0) : (coordinateNormalLinear K H).range = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro y
  refine ⟨WithLp.toLp 2 (Sum.elim (0 : b → ℝ) (H⁻¹.mulVec (WithLp.ofLp y))), ?_⟩
  change coordinateNormalLinear K H _ = y
  apply PiLp.ext
  intro i
  rw [coordinateNormalLinear_apply]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H (isUnit_iff_ne_zero.mpr hH),
    Matrix.one_mulVec]
  change K.mulVec (0 : b → ℝ) i + y i = y i
  simp

theorem coordinate_kernel_finrank (K : Matrix c b ℝ) (H : Matrix c c ℝ)
    (hH : H.det ≠ 0) :
    Module.finrank ℝ (coordinateNormalLinear K H).ker = Module.finrank ℝ (EuclideanSpace ℝ b) :=
  (coordinateKernelEquiv K H hH).finrank_eq.symm

/-- Nonnegativity of the actual normal Gram determinant, without a rank premise. -/
theorem normalGram_det_nonneg (K : Matrix c b ℝ) (H : Matrix c c ℝ) :
    0 ≤ (K*K.transpose+H*H.transpose).det := by
  have he := matrix_toEuclideanLin_normDet_sq (Matrix.fromRows K.transpose H.transpose)
  simp only [Matrix.transpose_fromRows, Matrix.transpose_transpose,
    Matrix.fromCols_mul_fromRows] at he
  rw [← he]
  positivity

/-- A nonzero actual normal minor makes the normal Gram determinant positive. -/
theorem normalGram_det_pos (K : Matrix c b ℝ) (H : Matrix c c ℝ) (hH : H.det ≠ 0) :
    0 < (K*K.transpose+H*H.transpose).det := by
  have hg : (euclideanGraphLinear (H⁻¹*K)).normDet ≠ 0 := by
    intro hz
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp hz)
      (LinearMap.ker_eq_bot.mpr (euclideanGraphLinear_injective _))
  have he := normal_block_gram_det H (H⁻¹*K)
  rw [Matrix.mul_nonsing_inv_cancel_left H K (isUnit_iff_ne_zero.mpr hH),
    ← euclideanGraphLinear_normDet_sq] at he
  rw [he]
  exact mul_pos (sq_pos_of_ne_zero hH) (sq_pos_of_ne_zero hg)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coordinate_tangent_projection_normDet_sq

#print axioms KakeyaTwoScale.coordinateBaseProjection_norm_le
#print axioms KakeyaTwoScale.coordinateNormalLinear_range
#print axioms KakeyaTwoScale.coordinate_kernel_finrank

#print axioms KakeyaTwoScale.normalGram_det_nonneg
#print axioms KakeyaTwoScale.normalGram_det_pos
