module
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import KakeyaTwoScale.ContractionDeterminantInverse
public import KakeyaTwoScale.FixedProjectionCapture

@[expose] public section

open Set Metric
open scoped NNReal
noncomputable section
namespace KakeyaTwoScale

/-- The actual restriction of a fixed projection to the tangent kernel. -/
def tangentProjection {E F V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : E →L[ℝ] F) (π : E →L[ℝ] V) : A.ker →L[ℝ] V :=
  π.comp A.ker.subtypeL

/-- Construct the linear tangent section from the actual determinant of
projection on the tangent space. No inverse or inverse bound is assumed. -/
theorem exists_tangent_section_of_projection_det {E F V : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (A : E →L[ℝ] F) (π : E →L[ℝ] V) (hπ : ‖π‖ ≤ 1)
    (hdim : Module.finrank ℝ A.ker = Module.finrank ℝ V)
    (hdet : (3:ℝ)/4 < (tangentProjection A π).toLinearMap.normDet^2) :
    ∃ B : V →L[ℝ] E, A.comp B = 0 ∧
      π.comp B = ContinuousLinearMap.id ℝ V ∧
      (∀ x, A x = 0 → π x = 0 → x = 0) ∧ ‖B‖ ≤ (4:ℝ)/3 ∧ ‖B‖₊ < 2 := by
  have hT : ‖tangentProjection A π‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    change ‖π (x:E)‖ ≤ 1 * ‖x‖
    calc
      _ ≤ ‖π‖ * ‖(x:E)‖ := π.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hπ (norm_nonneg x)
  obtain ⟨e,he,hebound,_⟩ := exists_contraction_inverse_of_normDet_sq
    (tangentProjection A π) hT hdim hdet
  let B := A.ker.subtypeL.comp e.symm.toContinuousLinearMap
  have hBbound : ‖B‖ ≤ (4:ℝ)/3 := by
    calc
      ‖B‖ ≤ ‖A.ker.subtypeL‖ * ‖e.symm.toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ((4:ℝ)/3) := mul_le_mul A.ker.norm_subtypeL_le hebound
        (norm_nonneg _) (by norm_num)
      _ = (4:ℝ)/3 := one_mul _
  refine ⟨B,?_,?_,?_,hBbound,?_⟩
  · ext v
    exact (e.symm v).property
  · ext v
    have hh := e.apply_symm_apply v
    rw [show e (e.symm v) = tangentProjection A π (e.symm v) from
      congrArg (fun T : A.ker →L[ℝ] V => T (e.symm v)) he] at hh
    exact hh
  · intro x hAx hπx
    have hh : e (⟨x,hAx⟩ : A.ker) = e 0 := by
      rw [map_zero]
      change e.toContinuousLinearMap (⟨x,hAx⟩ : A.ker) = 0
      rw [he]
      exact hπx
    exact congrArg Subtype.val (e.injective hh)
  · change ‖B‖ < 2
    linarith

/-- Whole-cube capture with the inverse and local differential hypotheses
instantiated from the actual C1 constraint and tangent projection determinant.
The determinant/normal-minor identification is a separate algebraic theorem. -/
theorem whole_set_capture_of_tangent_projection_det {E F V : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (f : E → F) (hf : ContDiff ℝ 1 f) (value : F)
    (π : E →L[ℝ] V) (hπ : ‖π‖₊ ≤ 1) (g : E → ℝ) (hg : Continuous g)
    (hdim : Module.finrank ℝ F + Module.finrank ℝ V = Module.finrank ℝ E)
    (hregular : ∀ y, f y = value → 0 < g y → (fderiv ℝ f y).range = ⊤)
    (hdet : ∀ y, f y = value → 0 < g y →
      (3:ℝ)/4 < (tangentProjection (fderiv ℝ f y) π).toLinearMap.normDet^2)
    (Q : Set E) (T : Set V) (z : E) (hz : f z = value) (hgz : 0 ≤ g z)
    (η r : ℝ) (hnear : ∀ x ∈ Q, dist x z < η)
    (hbad : ∃ x ∈ Q, π x ∈ thickening r T) :
    Q ⊆ thickening (η+2*(η+r)) ({y | f y = value} ∩ π ⁻¹' T) ∨
    Q ⊆ thickening (η+2*(η+r)) ({y | f y = value} ∩ {y | g y = 0}) := by
  apply whole_set_fixed_projection_fiber_capture f hf.continuous value π hπ g hg _
    Q T z hz hgz η r hnear hbad
  intro y hy hgy
  let A := fderiv ℝ f y
  have hA := hregular y hy hgy
  have hdimA : Module.finrank ℝ A.ker = Module.finrank ℝ V := by
    have hr := A.toLinearMap.finrank_range_add_finrank_ker
    change Module.finrank ℝ A.range + Module.finrank ℝ A.ker = _ at hr
    rw [hA,finrank_top] at hr
    omega
  obtain ⟨B,hAB,hπB,hinj,_,hB⟩ := exists_tangent_section_of_projection_det
    A π (by exact_mod_cast hπ) hdimA (hdet y hy hgy)
  exact ⟨A,B,hf.hasStrictFDerivAt (by norm_num),hA,hAB,hπB,hinj,hB⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_tangent_section_of_projection_det
#print axioms KakeyaTwoScale.whole_set_capture_of_tangent_projection_det
