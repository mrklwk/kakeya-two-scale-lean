module
public import KakeyaTwoScale.PolynomialGaussBarrier
public import KakeyaTwoScale.NormalGramSurjectivity
public import KakeyaTwoScale.RegularRatioLevel
public import KakeyaTwoScale.SmoothFiberRegularValues

@[expose] public section

open Set MvPolynomial
open scoped ContDiff
noncomputable section
namespace KakeyaTwoScale

theorem polynomialNormalGram_pos_on_regular_fiber {b c : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (x : EuclideanSpace ℝ (Fin b ⊕ Fin c))
    (hx : (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤) :
    0 < eval x (polynomialNormalGram P) := by
  rw [polynomialNormalGram_eval]
  apply normalGram_det_pos_of_range
  rwa [rectangularPolynomialMap_fderiv_blocks] at hx

/-- A genuinely selected regular Gauss barrier on the entire original
regular fiber; neither regularity of the ratio level nor a preferred
invertible vertical minor is an input. -/
theorem exists_regular_polynomialGaussBarrier {b c D : ℕ}
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ)
    (hP : ∀ i, (P i).totalDegree ≤ D)
    (hreg : ∀ x : EuclideanSpace ℝ (Fin b ⊕ Fin c),
      rectangularPolynomialMap P x=0 →
      (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤) :
    ∃ τ ∈ Ioo ((3:ℝ)/4) ((7:ℝ)/8),
      (polynomialGaussBarrier P τ).totalDegree ≤ 2*c*(D-1) ∧
      (∀ x : EuclideanSpace ℝ (Fin b ⊕ Fin c),
        rectangularPolynomialMap P x=0 → eval x (polynomialGaussBarrier P τ)=0 →
        (fderiv ℝ (fun y => (rectangularPolynomialMap P y,
          eval y (polynomialGaussBarrier P τ))) x).range=⊤) ∧
      (∀ x : EuclideanSpace ℝ (Fin b ⊕ Fin c),
        rectangularPolynomialMap P x=0 →
        (7:ℝ)/8 < (polynomialNormalJacobianAt P x).det^2 /
          eval x (polynomialNormalGram P) →
        0 < eval x (polynomialGaussBarrier P τ)) := by
  let f := rectangularPolynomialMap P
  let N : EuclideanSpace ℝ (Fin b ⊕ Fin c) → ℝ :=
    fun x => eval x ((polynomialNormalJacobian P).det^2)
  let G : EuclideanSpace ℝ (Fin b ⊕ Fin c) → ℝ :=
    fun x => eval x (polynomialNormalGram P)
  have hN : ContDiff ℝ ∞ N := finite_polynomial_eval_contDiff _ ∞
  have hG : ContDiff ℝ ∞ G := finite_polynomial_eval_contDiff _ ∞
  have hpos : ∀ x, f x=0 → 0 < G x := fun x hx =>
    polynomialNormalGram_pos_on_regular_fiber P x (hreg x hx)
  have hratio : ∀ x, f x=0 → ContDiffAt ℝ ∞ (fun y => N y/G y) x := by
    intro x hx
    exact hN.contDiffAt.div hG.contDiffAt (ne_of_gt (hpos x hx))
  obtain ⟨τ,hτ,hτreg⟩ := smooth_fiber_exists_relative_regular_value f
    (fun y => N y/G y) 0
    (fun x _ => (rectangularPolynomialMap_contDiff P ∞).contDiffAt)
    hratio hreg (by norm_num : (3:ℝ)/4 < 7/8)
  have hNeval (x : EuclideanSpace ℝ (Fin b ⊕ Fin c)) :
      N x=(polynomialNormalJacobianAt P x).det^2 := by
    dsimp [N]
    rw [map_pow,(eval x).map_det]
    rfl
  have hbar : (fun y : EuclideanSpace ℝ (Fin b ⊕ Fin c) =>
      eval y (polynomialGaussBarrier P τ)) = fun y => N y-τ*G y := by
    funext y
    rw [polynomialGaussBarrier_eval, hNeval]
  refine ⟨τ,hτ,polynomialGaussBarrier_degree P hP τ,?_,?_⟩
  · intro x hx hzero
    have hlevel : N x/G x=τ := by
      have hz : N x-τ*G x=0 := by
        change (fun y : EuclideanSpace ℝ (Fin b ⊕ Fin c) => eval y (polynomialGaussBarrier P τ)) x=0 at hzero
        rwa [hbar] at hzero
      apply (div_eq_iff (ne_of_gt (hpos x hx))).mpr
      linarith
    obtain ⟨v,hvf,hvg⟩ := hτreg x hx hlevel
    have hd := cleared_ratio_level_fderiv N G x τ
      (hN.differentiable (by simp) x) (hG.differentiable (by simp) x)
      (ne_of_gt (hpos x hx)) hlevel
    have hvbar : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin b ⊕ Fin c) => eval y (polynomialGaussBarrier P τ)) x v ≠ 0 := by
      rw [hbar,hd]
      simpa only [smul_apply,smul_eq_mul] using
        mul_ne_zero (ne_of_gt (hpos x hx)) hvg
    have hp := constraint_pair_surjective (fderiv ℝ f x)
      (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin b ⊕ Fin c) => eval y (polynomialGaussBarrier P τ)) x)
      (hreg x hx) v hvf hvbar
    have hdf := (rectangularPolynomialMap_contDiff P ∞).differentiable (by simp) x
    have hdb := (finite_polynomial_eval_contDiff (polynomialGaussBarrier P τ) ∞).differentiable (by simp) x
    rw [(hdf.hasFDerivAt.prodMk hdb.hasFDerivAt).fderiv]
    exact hp
  · intro x hx htag
    rw [polynomialGaussBarrier_eval]
    have hh := (lt_div_iff₀ (hpos x hx)).mp htag
    have hmul := mul_lt_mul_of_pos_right hτ.2 (hpos x hx)
    change τ * G x < (7:ℝ)/8 * G x at hmul
    change (7:ℝ)/8 * G x < _ at hh
    change 0 < _-τ*G x
    linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomialNormalGram_pos_on_regular_fiber
#print axioms KakeyaTwoScale.exists_regular_polynomialGaussBarrier
