module
public import KakeyaTwoScale.OrthogonalPolynomialTransport
public import Mathlib.Algebra.MvPolynomial.Rename

@[expose] public section

open Set MvPolynomial
noncomputable section
namespace KakeyaTwoScale

def euclideanCoordinateRename {σ τ : Type*} [Fintype σ] [Fintype τ]
    (e : σ ≃ τ) : EuclideanSpace ℝ σ ≃ₗᵢ[ℝ] EuclideanSpace ℝ τ :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

@[simp] theorem euclideanCoordinateRename_apply {σ τ : Type*} [Fintype σ] [Fintype τ]
    (e : σ ≃ τ) (x : EuclideanSpace ℝ σ) (i : τ) :
    euclideanCoordinateRename e x i=x (e.symm i) := rfl

theorem polynomialCoordinateRename_eval {σ τ : Type*} [Fintype σ] [Fintype τ]
    (e : σ ≃ τ) (P : MvPolynomial σ ℝ) (x : EuclideanSpace ℝ σ) :
    eval (euclideanCoordinateRename e x) (rename e P)=eval x P := by
  rw [eval_rename]
  have hh : (euclideanCoordinateRename e x).ofLp ∘ e=x.ofLp := by
    funext i
    simp
  rw [hh]

theorem polynomialCoordinateRename_degree {σ τ : Type*} (e : σ ≃ τ)
    (P : MvPolynomial σ ℝ) : (rename e P).totalDegree=P.totalDegree :=
  totalDegree_renameEquiv e P

theorem rectangularPolynomialMap_rename {σ τ κ : Type*}
    [Fintype σ] [Fintype τ] [Fintype κ]
    (e : σ ≃ τ) (P : κ → MvPolynomial σ ℝ) (x : EuclideanSpace ℝ σ) :
    rectangularPolynomialMap (fun i => rename e (P i)) (euclideanCoordinateRename e x)=
      rectangularPolynomialMap P x := by
  apply PiLp.ext
  intro i
  exact polynomialCoordinateRename_eval e (P i) x

theorem polynomialCoordinateRename_regular {σ τ κ : Type*}
    [Fintype σ] [Fintype τ] [Fintype κ]
    (e : σ ≃ τ) (P : κ → MvPolynomial σ ℝ)
    (hr : ∀ x, rectangularPolynomialMap P x=0 →
      (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤) :
    ∀ y, rectangularPolynomialMap (fun i => rename e (P i)) y=0 →
      (fderiv ℝ (rectangularPolynomialMap (fun i => rename e (P i))) y).range=⊤ := by
  intro y hy
  let E := euclideanCoordinateRename e
  have heq : rectangularPolynomialMap (fun i => rename e (P i))=
      rectangularPolynomialMap P ∘ E.symm := by
    funext y
    have hh := rectangularPolynomialMap_rename e P (E.symm y)
    change rectangularPolynomialMap (fun i => rename e (P i)) (E (E.symm y))=_ at hh
    simpa only [E.apply_symm_apply,Function.comp_apply] using hh
  rw [heq] at hy ⊢
  have hd := ((rectangularPolynomialMap_contDiff P 1).differentiable (by norm_num) (E.symm y)).hasFDerivAt.comp y
    E.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  rw [hd.fderiv]
  apply LinearMap.range_eq_top.mpr
  intro z
  obtain ⟨v,hv⟩ := LinearMap.range_eq_top.mp (hr (E.symm y) hy) z
  exact ⟨E v,by simpa using hv⟩

theorem polynomialCoordinateRename_zero_thickening {σ τ κ : Type*}
    [Fintype σ] [Fintype τ] [Fintype κ]
    (e : σ ≃ τ) (P : κ → MvPolynomial σ ℝ)
    (x : EuclideanSpace ℝ σ) (r : ℝ) :
    euclideanCoordinateRename e x ∈ Metric.thickening r
      {y | rectangularPolynomialMap (fun i => rename e (P i)) y=0} ↔
    x ∈ Metric.thickening r {y | rectangularPolynomialMap P y=0} := by
  let E := euclideanCoordinateRename e
  constructor
  · intro hx
    obtain ⟨y,hy,hxy⟩ := Metric.mem_thickening_iff.mp hx
    apply Metric.mem_thickening_iff.mpr
    refine ⟨E.symm y,?_,?_⟩
    · have hh := rectangularPolynomialMap_rename e P (E.symm y)
      change rectangularPolynomialMap (fun i => rename e (P i)) (E (E.symm y))=_ at hh
      rw [E.apply_symm_apply] at hh
      exact hh.symm.trans hy
    · have hd := E.dist_map x (E.symm y)
      rw [E.apply_symm_apply] at hd
      exact hd ▸ hxy
  · intro hx
    obtain ⟨y,hy,hxy⟩ := Metric.mem_thickening_iff.mp hx
    apply Metric.mem_thickening_iff.mpr
    refine ⟨E y,?_,?_⟩
    · exact (rectangularPolynomialMap_rename e P y).trans hy
    · exact (E.dist_map x y).trans_lt hxy

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomialCoordinateRename_eval
#print axioms KakeyaTwoScale.polynomialCoordinateRename_degree
#print axioms KakeyaTwoScale.polynomialCoordinateRename_regular
#print axioms KakeyaTwoScale.polynomialCoordinateRename_zero_thickening
