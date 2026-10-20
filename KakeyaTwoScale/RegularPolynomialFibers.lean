module
public import KakeyaTwoScale.PolynomialCriticalBridge
public import KakeyaTwoScale.IsolatedPolynomialZeros
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

open Set Metric MvPolynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

def polynomialMap {n : ℕ} (P : Fin n → MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => eval x (P j))

theorem polynomial_eval_contDiff {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (r : WithTop ℕ∞) :
    ContDiff ℝ r (fun x : EuclideanSpace ℝ (Fin n) => eval x P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ r (fun _ : EuclideanSpace ℝ (Fin n) => a))
  | add P Q hP hQ => simpa using hP.add hQ
  | mul_X P j hP =>
    simpa using hP.mul (contDiff_piLp_apply (𝕜 := ℝ) (p := (2 : ENNReal)) (i := j))

theorem polynomialMap_contDiff {n : ℕ} (P : Fin n → MvPolynomial (Fin n) ℝ)
    (r : WithTop ℕ∞) : ContDiff ℝ r (polynomialMap P) := by
  apply (contDiff_piLp 2).mpr
  intro j
  exact polynomial_eval_contDiff (P j) r

/-- A nonsingular derivative isolates its fiber in an actual closed ball.
No global injectivity, properness, or finite-fiber premise is used. -/
theorem contDiff_det_ne_zero_isolates_fiber {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → E)
    (x : E) (hf : ContDiff ℝ 1 f)
    (hdet : LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ z, dist z x ≤ r → f z = f x → z = x := by
  let e := (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hdet)).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] E) = fderiv ℝ f x := by
    ext z
    simp [e]
  have hd : HasFDerivAt f (e : E →L[ℝ] E) x := by
    rw [he]
    exact (hf.differentiable (by norm_num) x).hasFDerivAt
  let h := hf.contDiffAt.toOpenPartialHomeomorph f hd (by norm_num)
  have hx : x ∈ h.source := hf.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by norm_num)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (h.open_source.mem_nhds hx)
  refine ⟨r/2,by positivity,?_⟩
  intro z hz heq
  apply h.injOn (hball (by change dist z x < r; linarith)) hx
  exact heq

theorem regular_polynomial_fiber_isolated {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hdet : LinearMap.det (fderiv ℝ (polynomialMap P) x).toLinearMap ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ z, dist z x ≤ r → polynomialMap P z = polynomialMap P x → z=x :=
  contDiff_det_ne_zero_isolates_fiber (polynomialMap P) x (polynomialMap_contDiff P 1) hdet

def polynomialMapPi {n : ℕ} (P : Fin n → MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ := fun j => eval x (P j)

theorem polynomialMapPi_contDiff {n : ℕ} (P : Fin n → MvPolynomial (Fin n) ℝ)
    (r : WithTop ℕ∞) : ContDiff ℝ r (polynomialMapPi P) := by
  apply contDiff_pi.mpr
  intro j
  exact (polynomial_eval_contDiff (P j) r).comp (PiLp.contDiff_toLp (p := (2 : ENNReal)))

def polynomialFiberSquares {n : ℕ} (P : Fin n → MvPolynomial (Fin n) ℝ)
    (y : Fin n → ℝ) : MvPolynomial (Fin n) ℝ := ∑ j, (P j-C (y j))^2

theorem polynomialFiberSquares_degree {n D : ℕ}
    (P : Fin n → MvPolynomial (Fin n) ℝ) (y : Fin n → ℝ)
    (hdeg : ∀ j, (P j).totalDegree ≤ D) : (polynomialFiberSquares P y).totalDegree ≤ 2*D := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  apply (totalDegree_pow _ 2).trans
  apply Nat.mul_le_mul_left
  exact (totalDegree_sub _ _).trans (by simpa using hdeg j)

theorem polynomialFiberSquares_nonneg {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n) ℝ) (y x : Fin n → ℝ) :
    0 ≤ eval x (polynomialFiberSquares P y) := by
  simp only [polynomialFiberSquares,map_sum,map_pow,map_sub,eval_C]
  exact Finset.sum_nonneg (fun j _ => sq_nonneg _)

theorem polynomialFiberSquares_eq_zero {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n) ℝ) (y x : Fin n → ℝ) :
    eval x (polynomialFiberSquares P y)=0 ↔ polynomialMapPi P x=y := by
  simp only [polynomialFiberSquares,map_sum,map_pow,map_sub,eval_C]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (eval x (P j)-y j))]
  simp [polynomialMapPi,funext_iff,sub_eq_zero]

/-- Any finite collection of regular points in one polynomial fiber has a
degree-uniform bound. Singular points elsewhere in the fiber are unrestricted. -/
theorem regular_polynomial_fiber_card_le {n D : ℕ} {I : Type*} [Fintype I]
    (P : Fin n → MvPolynomial (Fin n) ℝ) (hdeg : ∀ j, (P j).totalDegree ≤ D)
    (y : Fin n → ℝ) (x : I → (Fin n → ℝ)) (hxinj : Function.Injective x)
    (hfiber : ∀ i, polynomialMapPi P (x i)=y)
    (hregular : ∀ i, LinearMap.det (fderiv ℝ (polynomialMapPi P) (x i)).toLinearMap ≠ 0) :
    Fintype.card I ≤ (4*D+1)^n := by
  let xE : I → EuclideanSpace ℝ (Fin n) := fun i => WithLp.toLp 2 (x i)
  have hinj : Function.Injective xE := by
    intro i j hij
    apply hxinj
    exact congrArg WithLp.ofLp hij
  have hz (i : I) : eval (fun j => xE i j) (polynomialFiberSquares P y)=0 :=
    (polynomialFiberSquares_eq_zero P y (x i)).mpr (hfiber i)
  have hi (i : I) : ∃ r : ℝ, 0 < r ∧ ∀ z : EuclideanSpace ℝ (Fin n),
      dist z (xE i) ≤ r → eval (fun j => z j) (polynomialFiberSquares P y)=0 → z=xE i := by
    obtain ⟨r,hr,hiso⟩ := contDiff_det_ne_zero_isolates_fiber (polynomialMapPi P) (x i)
      (polynomialMapPi_contDiff P 1) (hregular i)
    have hc : ContinuousAt (fun z : EuclideanSpace ℝ (Fin n) => (fun j => z j)) (xE i) :=
      (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).continuousAt
    obtain ⟨s,hs,hsmall⟩ := Metric.continuousAt_iff.mp hc r hr
    refine ⟨s/2,by positivity,?_⟩
    intro z hdist hzero
    have hdist' : dist (fun j => z j) (x i) ≤ r :=
      (hsmall (show dist z (xE i) < s by linarith)).le
    have hmap : polynomialMapPi P (fun j => z j)=polynomialMapPi P (x i) :=
      ((polynomialFiberSquares_eq_zero P y _).mp hzero).trans (hfiber i).symm
    have heq := hiso (fun j => z j) hdist' hmap
    ext j
    exact congrFun heq j
  have hh := isolated_nonnegative_polynomial_zeros_card_le (polynomialFiberSquares P y)
    (polynomialFiberSquares_degree P y hdeg)
    (fun z => polynomialFiberSquares_nonneg P y (fun j => z j)) xE hinj hz hi
  have he : 2*(2*D)+1=4*D+1 := by omega
  simpa only [he] using hh

/-- The regular part of a polynomial fiber is finite even when its singular
part is positive-dimensional or unbounded. -/
theorem regular_polynomial_fiber_finite_ncard_le {n D : ℕ}
    (P : Fin n → MvPolynomial (Fin n) ℝ) (hdeg : ∀ j, (P j).totalDegree ≤ D)
    (y : Fin n → ℝ) :
    let S := {x : Fin n → ℝ | polynomialMapPi P x=y ∧
      LinearMap.det (fderiv ℝ (polynomialMapPi P) x).toLinearMap ≠ 0}
    S.Finite ∧ S.ncard ≤ (4*D+1)^n := by
  dsimp only
  apply finite_ncard_le_of_finset_bound
  intro A hA
  have hh := regular_polynomial_fiber_card_le P hdeg y (fun x : A => x.val)
    Subtype.val_injective (fun x => (hA x.property).1) (fun x => (hA x.property).2)
  simpa using hh

theorem regular_polynomial_fiber_encard_le {n D : ℕ}
    (P : Fin n → MvPolynomial (Fin n) ℝ) (hdeg : ∀ j, (P j).totalDegree ≤ D)
    (y : Fin n → ℝ) :
    Set.encard {x : Fin n → ℝ | polynomialMapPi P x=y ∧
      LinearMap.det (fderiv ℝ (polynomialMapPi P) x).toLinearMap ≠ 0} ≤ ((4*D+1)^n : ℕ) :=
  Set.encard_le_coe_iff_finite_ncard_le.mpr (regular_polynomial_fiber_finite_ncard_le P hdeg y)

/-- Area-formula interface: any supplied derivative and any domain subset.
The singular part of the fiber is deliberately not counted. -/
theorem regular_polynomial_restricted_fiber_encard_le {n D : ℕ}
    (P : Fin n → MvPolynomial (Fin n) ℝ) (hdeg : ∀ j, (P j).totalDegree ≤ D)
    (Df : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
    (hDf : ∀ x, HasFDerivAt (polynomialMapPi P) (Df x) x)
    (S : Set (Fin n → ℝ)) (y : Fin n → ℝ) :
    Set.encard {x : Fin n → ℝ | x ∈ S ∧ LinearMap.det (Df x).toLinearMap ≠ 0 ∧
      polynomialMapPi P x=y} ≤ ((4*D+1)^n : ℕ) := by
  apply (Set.encard_le_encard ?_).trans (regular_polynomial_fiber_encard_le P hdeg y)
  intro x hx
  exact ⟨hx.2.2,by rw [(hDf x).fderiv]; exact hx.2.1⟩

end KakeyaTwoScale

#print axioms KakeyaTwoScale.contDiff_det_ne_zero_isolates_fiber
#print axioms KakeyaTwoScale.regular_polynomial_fiber_isolated
#print axioms KakeyaTwoScale.polynomialMapPi_contDiff
#print axioms KakeyaTwoScale.polynomialFiberSquares_degree
#print axioms KakeyaTwoScale.polynomialFiberSquares_eq_zero
#print axioms KakeyaTwoScale.regular_polynomial_fiber_card_le
#print axioms KakeyaTwoScale.regular_polynomial_fiber_finite_ncard_le
#print axioms KakeyaTwoScale.regular_polynomial_fiber_encard_le
#print axioms KakeyaTwoScale.regular_polynomial_restricted_fiber_encard_le
