module
public import KakeyaTwoScale.RegularPolynomialFibers
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

open MvPolynomial
noncomputable section
namespace KakeyaTwoScale

/-- Rectangular polynomial constraint map in genuine Euclidean norms. -/
def rectangularPolynomialMap {σ κ : Type*} [Fintype σ] [Fintype κ]
    (P : κ → MvPolynomial σ ℝ) (x : EuclideanSpace ℝ σ) : EuclideanSpace ℝ κ :=
  WithLp.toLp 2 (fun i => eval x (P i))

theorem finite_polynomial_eval_contDiff {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (fun x : EuclideanSpace ℝ σ => eval x P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ r (fun _ : EuclideanSpace ℝ σ => a))
  | add P Q hP hQ => simpa using hP.add hQ
  | mul_X P j hP =>
    simpa using hP.mul (contDiff_piLp_apply (𝕜 := ℝ) (p := (2 : ENNReal)) (i := j))

theorem rectangularPolynomialMap_contDiff {σ κ : Type*} [Fintype σ] [Fintype κ]
    (P : κ → MvPolynomial σ ℝ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (rectangularPolynomialMap P) := by
  apply (contDiff_piLp 2).mpr
  intro i
  exact finite_polynomial_eval_contDiff (P i) r

theorem finite_polynomial_euclidean_fderiv_coordinate {σ : Type*}
    [Fintype σ] [DecidableEq σ] (P : MvPolynomial σ ℝ)
    (x : EuclideanSpace ℝ σ) (j : σ) :
    fderiv ℝ (fun y : EuclideanSpace ℝ σ => eval y P) x
      (EuclideanSpace.single j 1) = eval x (pderiv j P) := by
  have hd := ((finite_polynomial_eval_contDiff P 1).differentiable (by norm_num) x).hasFDerivAt
  have hut := PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (Function.update (WithLp.ofLp x) j (x j))
  have hu := hut.comp_hasDerivAt (x j) (hasDerivAt_update (WithLp.ofLp x) j (x j))
  have hd' : HasFDerivAt (fun y : EuclideanSpace ℝ σ => eval y P)
      (fderiv ℝ (fun y : EuclideanSpace ℝ σ => eval y P) x)
      ((WithLp.toLp 2 ∘ Function.update (WithLp.ofLp x) j) (x j)) := by
    simpa using hd
  have hc := hd'.comp_hasDerivAt (x j) hu
  have he : HasDerivAt (fun t => eval (Function.update (WithLp.ofLp x) j t) P)
      (fderiv ℝ (fun y : EuclideanSpace ℝ σ => eval y P) x
        (EuclideanSpace.single j 1)) (x j) := by
    simpa [Function.comp_def] using hc
  exact he.unique (by simpa using polynomial_coordinate_hasDerivAt P (WithLp.ofLp x) j (x j))

/-- The actual Frechet derivative is exactly the evaluated rectangular
polynomial Jacobian matrix, including Euclidean domain and codomain norms. -/
theorem rectangularPolynomialMap_fderiv {σ κ : Type*}
    [Fintype σ] [Fintype κ] [DecidableEq σ] [DecidableEq κ]
    (P : κ → MvPolynomial σ ℝ) (x : EuclideanSpace ℝ σ) :
    fderiv ℝ (rectangularPolynomialMap P) x =
      (show Matrix κ σ ℝ from fun i j => eval x (pderiv j (P i))).toEuclideanLin.toContinuousLinearMap := by
  have hd := ((rectangularPolynomialMap_contDiff P 1).differentiable (by norm_num) x).hasFDerivAt
  have hcoordinate (i : κ) (j : σ) :
      fderiv ℝ (rectangularPolynomialMap P) x (EuclideanSpace.single j 1) i =
        eval x (pderiv j (P i)) := by
    have hh := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (rectangularPolynomialMap P x) i).comp x hd
    have he : fderiv ℝ (fun y : EuclideanSpace ℝ σ => eval y (P i)) x =
        (PiLp.proj 2 (fun _ : κ => ℝ) i).comp (fderiv ℝ (rectangularPolynomialMap P) x) :=
      hh.fderiv
    rw [← finite_polynomial_euclidean_fderiv_coordinate (P i) x j, he]
    rfl
  have heq : (fderiv ℝ (rectangularPolynomialMap P) x).toLinearMap =
      (show Matrix κ σ ℝ from fun i j => eval x (pderiv j (P i))).toEuclideanLin := by
    apply (EuclideanSpace.basisFun σ ℝ).toBasis.ext
    intro j
    apply PiLp.ext
    intro i
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    change fderiv ℝ (rectangularPolynomialMap P) x (EuclideanSpace.single j 1) i =
      ((show Matrix κ σ ℝ from fun i j => eval x (pderiv j (P i))).mulVec (Pi.single j 1)) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hcoordinate i j
  ext v i
  exact congrArg (fun L : EuclideanSpace ℝ σ →ₗ[ℝ] EuclideanSpace ℝ κ => L v i) heq

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_polynomial_eval_contDiff
#print axioms KakeyaTwoScale.rectangularPolynomialMap_contDiff
#print axioms KakeyaTwoScale.finite_polynomial_euclidean_fderiv_coordinate
#print axioms KakeyaTwoScale.rectangularPolynomialMap_fderiv
