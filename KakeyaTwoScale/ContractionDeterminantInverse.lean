module
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators
open Module
noncomputable section
set_option maxHeartbeats 800000
namespace KakeyaTwoScale

/-- A contraction's squared norm determinant bounds its least squared stretch.
The inequality is derived from the actual spectral decomposition of T* T. -/
theorem contraction_normDet_sq_mul_norm_sq_le {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T : E →L[ℝ] F) (hT : ‖T‖ ≤ 1) (x : E) :
    T.toLinearMap.normDet ^ 2 * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
  classical
  let f := T.toLinearMap
  let S := f.adjoint.comp f
  have hS : S.IsSymmetric := f.isSymmetric_adjoint_comp_self
  let b := hS.eigenvectorBasis rfl
  let ev := hS.eigenvalues rfl
  have heig : ∀ i, S (b i) = ev i • b i := hS.apply_eigenvectorBasis rfl
  have heq : ∀ i, ‖T (b i)‖^2 = ev i := by
    intro i
    calc
      ‖T (b i)‖^2 = inner ℝ (S (b i)) (b i) := by
        simp [S, f, LinearMap.adjoint_inner_left]
      _ = ev i := by rw [heig i]; simp [real_inner_smul_left, b]
  have hnonneg : ∀ i, 0 ≤ ev i := by
    intro i
    rw [← heq i]
    positivity
  have hle : ∀ i, ev i ≤ 1 := by
    intro i
    have hb : ‖T (b i)‖ ≤ 1 := by
      calc
        ‖T (b i)‖ ≤ ‖T‖ * ‖b i‖ := T.le_opNorm _
        _ ≤ 1 := by simpa [b] using hT
    rw [← heq i]
    nlinarith [norm_nonneg (T (b i))]
  have hdet : T.toLinearMap.normDet ^ 2 = ∏ i, ev i := by
    simpa [f, S, ev] using (f.normDet_sq.trans (hS.det_eq_prod_eigenvalues rfl))
  have hprod : ∀ i, (∏ j, ev j) ≤ ev i := by
    intro i
    calc
      (∏ j, ev j) ≤ ∏ j, if j=i then ev i else 1 := by
        apply Finset.prod_le_prod₀ (fun j _ => hnonneg j)
        intro j _
        split_ifs with hj
        · simp [hj]
        · exact hle j
      _ = ev i := by simp
  have hexp : ‖T x‖^2 = ∑ i, ev i * (inner ℝ (b i) x)^2 := by
    calc
      ‖T x‖^2 = inner ℝ x (S x) := by
        simp [S, f, LinearMap.adjoint_inner_right]
      _ = ∑ i, inner ℝ x (b i) * inner ℝ (b i) (S x) :=
        (b.sum_inner_mul_inner x (S x)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hS (b i) x, heig i, real_inner_smul_left, real_inner_comm x (b i)]
        ring
  have hparseval : ∑ i, (inner ℝ (b i) x)^2 = ‖x‖^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner_right x
  rw [hdet, ← hparseval, Finset.mul_sum, hexp]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hprod i) (sq_nonneg _))

/-- The Gauss threshold gives a rational, dimension-independent inverse stretch
bound strictly below the 3/2 local-chart budget. -/
theorem contraction_norm_le_four_thirds {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T : E →L[ℝ] F) (hT : ‖T‖ ≤ 1)
    (hdet : (3:ℝ)/4 < T.toLinearMap.normDet ^ 2) (x : E) :
    ‖x‖ ≤ (4:ℝ)/3 * ‖T x‖ := by
  have h := contraction_normDet_sq_mul_norm_sq_le T hT x
  have hsq : (3:ℝ)/4 * ‖x‖^2 ≤ ‖T x‖^2 :=
    (mul_le_mul_of_nonneg_right hdet.le (sq_nonneg _)).trans h
  nlinarith [norm_nonneg x, norm_nonneg (T x), sq_nonneg (‖x‖ - (4:ℝ)/3 * ‖T x‖)]

/-- Invertibility and the norm bound are constructed from the determinant and
contraction hypotheses; they are not premises. -/
theorem exists_contraction_inverse_of_normDet_sq {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T : E →L[ℝ] F) (hT : ‖T‖ ≤ 1)
    (hdim : finrank ℝ E = finrank ℝ F)
    (hdet : (3:ℝ)/4 < T.toLinearMap.normDet ^ 2) :
    ∃ e : E ≃L[ℝ] F, e.toContinuousLinearMap = T ∧
      ‖e.symm.toContinuousLinearMap‖ ≤ (4:ℝ)/3 ∧
      ‖e.symm.toContinuousLinearMap‖ < (3:ℝ)/2 := by
  have hinj : Function.Injective T := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have h := contraction_norm_le_four_thirds T hT hdet x
    change T x = 0 at hx
    rw [hx, norm_zero, mul_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg x))
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let e : E ≃L[ℝ] F := (LinearEquiv.ofBijective T.toLinearMap ⟨hinj,hsurj⟩).toContinuousLinearEquiv
  have he : e.toContinuousLinearMap = T := rfl
  have hb : ‖e.symm.toContinuousLinearMap‖ ≤ (4:ℝ)/3 := by
    apply e.symm.toContinuousLinearMap.opNorm_le_bound (by norm_num)
    intro y
    have h := contraction_norm_le_four_thirds T hT hdet (e.symm y)
    simpa only [← he, ContinuousLinearEquiv.coe_coe, e.apply_symm_apply] using h
  exact ⟨e,he,hb,hb.trans_lt (by norm_num)⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.contraction_normDet_sq_mul_norm_sq_le
#print axioms KakeyaTwoScale.contraction_norm_le_four_thirds
#print axioms KakeyaTwoScale.exists_contraction_inverse_of_normDet_sq
