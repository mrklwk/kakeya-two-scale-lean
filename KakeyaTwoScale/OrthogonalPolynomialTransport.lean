module
public import KakeyaTwoScale.PolynomialRegularGaussCapture
public import KakeyaTwoScale.PolynomialBaseSpecialization

@[expose] public section

open Set MvPolynomial
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 800000
namespace KakeyaTwoScale

/-- Pull back an actual polynomial by a linear Euclidean coordinate map. -/
def polynomialLinearPullback {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ σ)
    (P : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  eval₂Hom C (fun i => ∑ j, C (A (EuclideanSpace.single j 1) i) * X j) P

theorem polynomialLinearPullback_eval {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ σ)
    (P : MvPolynomial σ ℝ) (x : EuclideanSpace ℝ σ) :
    eval x (polynomialLinearPullback A P)=eval (A x) P := by
  have hx : ∑ j, x j • EuclideanSpace.single j (1:ℝ)=x := by
    simpa using (EuclideanSpace.basisFun σ ℝ).toBasis.sum_repr x
  have hcoord (i : σ) : (∑ j, A (EuclideanSpace.single j 1) i * x j)=A x i := by
    have hh := congrArg (fun y => A y i) hx
    simpa [map_sum,map_smul,mul_comm] using hh
  change (eval₂Hom (RingHom.id ℝ) x)
    (P.eval₂ C (fun i => ∑ j, C (A (EuclideanSpace.single j 1) i) * X j)) = _
  rw [eval₂_comp_left]
  have hc : (eval₂Hom (RingHom.id ℝ) x).comp C=RingHom.id ℝ := by ext r; simp
  rw [hc]
  congr 1
  funext i
  simpa using hcoord i

theorem polynomialLinearPullback_degree {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ σ)
    (P : MvPolynomial σ ℝ) :
    (polynomialLinearPullback A P).totalDegree ≤ P.totalDegree := by
  classical
  let f : σ → MvPolynomial σ ℝ := fun i => ∑ j, C (A (EuclideanSpace.single j 1) i) * X j
  have hf (i) : (f i).totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro j hj
    exact (totalDegree_mul _ _).trans (by simp)
  change (P.eval₂ C f).totalDegree ≤ _
  rw [eval₂_eq]
  apply totalDegree_finsetSum_le
  intro s hs
  apply le_trans (totalDegree_mul _ _)
  simp only [totalDegree_C,zero_add]
  apply le_trans (totalDegree_finsetProd _ _)
  apply le_trans _ (le_totalDegree hs)
  apply Finset.sum_le_sum
  intro i hi
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hf i))

theorem rectangularPolynomialMap_pullback {σ κ : Type*} [Fintype σ] [DecidableEq σ]
    [Fintype κ] (A : EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ σ)
    (P : κ → MvPolynomial σ ℝ) :
    rectangularPolynomialMap (fun i => polynomialLinearPullback A (P i))=
      rectangularPolynomialMap P ∘ A := by
  funext x
  apply PiLp.ext
  intro i
  exact polynomialLinearPullback_eval A (P i) x

theorem rectangularPolynomialMap_pullback_fderiv {σ κ : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype κ]
    (A : EuclideanSpace ℝ σ →L[ℝ] EuclideanSpace ℝ σ)
    (P : κ → MvPolynomial σ ℝ) (x : EuclideanSpace ℝ σ) :
    fderiv ℝ (rectangularPolynomialMap (fun i => polynomialLinearPullback A (P i))) x=
      (fderiv ℝ (rectangularPolynomialMap P) (A x)).comp A := by
  rw [rectangularPolynomialMap_pullback]
  exact ((rectangularPolynomialMap_contDiff P 1).differentiable (by norm_num) _).hasFDerivAt.comp x
    A.hasFDerivAt |>.fderiv

theorem orthogonal_polynomial_pullback_regular {σ κ : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype κ]
    (e : EuclideanSpace ℝ σ ≃ₗᵢ[ℝ] EuclideanSpace ℝ σ)
    (P : κ → MvPolynomial σ ℝ)
    (hreg : ∀ x, rectangularPolynomialMap P x=0 →
      (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤) :
    ∀ x, rectangularPolynomialMap (fun i => polynomialLinearPullback e.toContinuousLinearEquiv.toContinuousLinearMap (P i)) x=0 →
      (fderiv ℝ (rectangularPolynomialMap
        (fun i => polynomialLinearPullback e.toContinuousLinearEquiv.toContinuousLinearMap (P i))) x).range=⊤ := by
  intro x hx
  rw [rectangularPolynomialMap_pullback] at hx
  rw [rectangularPolynomialMap_pullback_fderiv]
  apply LinearMap.range_eq_top.mpr
  intro y
  obtain ⟨v,hv⟩ := LinearMap.range_eq_top.mp (hreg (e x) hx) y
  refine ⟨e.symm v,?_⟩
  simpa using hv

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomialLinearPullback_eval
#print axioms KakeyaTwoScale.polynomialLinearPullback_degree
#print axioms KakeyaTwoScale.rectangularPolynomialMap_pullback_fderiv
#print axioms KakeyaTwoScale.orthogonal_polynomial_pullback_regular
