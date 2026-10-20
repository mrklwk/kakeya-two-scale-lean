module
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic

@[expose] public section

open Filter
open scoped Topology
noncomputable section
namespace KakeyaTwoScale

/-- Clearing a nonzero denominator preserves the actual level differential,
up to multiplication by that denominator. -/
theorem cleared_ratio_level_fderiv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N G : E → ℝ) (x : E) (τ : ℝ)
    (hN : DifferentiableAt ℝ N x) (hG : DifferentiableAt ℝ G x)
    (hne : G x ≠ 0) (hlevel : N x / G x = τ) :
    fderiv ℝ (fun y => N y-τ*G y) x =
      G x • fderiv ℝ (fun y => N y/G y) x := by
  have hh : DifferentiableAt ℝ (fun y => N y/G y) x := by
    simpa only [div_eq_mul_inv, Pi.mul_def, Function.comp_def] using hN.mul ((hasDerivAt_inv hne).differentiableAt.comp x hG)
  have hmul := hG.hasFDerivAt.mul (hh.hasFDerivAt.sub_const τ)
  have hder : HasFDerivAt (fun y => G y*(N y/G y-τ))
      (G x • fderiv ℝ (fun y => N y/G y) x) x := by
    simpa [hlevel, Pi.mul_def] using hmul
  have heq : (fun y => N y-τ*G y) =ᶠ[𝓝 x] (fun y => G y*(N y/G y-τ)) := by
    filter_upwards [hG.continuousAt.eventually_ne hne] with y hy
    field_simp
  exact (hder.congr_of_eventuallyEq heq).fderiv

end KakeyaTwoScale
#print axioms KakeyaTwoScale.cleared_ratio_level_fderiv
