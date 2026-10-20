module
public import KakeyaTwoScale.PolynomialZeroNull
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

@[expose] public section

open MvPolynomial MeasureTheory Set Metric
open scoped RealInnerProductSpace BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Homogeneous quadratic containing a spherical latitude's radial cone. -/
def capConePolynomial {d : ℕ} (p : EuclideanSpace ℝ (Fin d)) (a : ℝ) :
    MvPolynomial (Fin d) ℝ :=
  (∑ i, C (p i) * X i)^2 - C (a^2) * ∑ i : Fin d, (X i)^2

theorem eval_capConePolynomial {d : ℕ} (p x : EuclideanSpace ℝ (Fin d)) (a : ℝ) :
    eval (WithLp.ofLp x) (capConePolynomial p a) = ⟪p,x⟫^2 - a^2 * ‖x‖^2 := by
  have hi : (∑ i : Fin d, p i * x i) = ⟪p,x⟫ := by
    simp [PiLp.inner_apply,mul_comm]
  have hn : (∑ i : Fin d, (x i)^2) = ‖x‖^2 := by
    calc
      _ = ⟪x,x⟫ := by simp only [PiLp.inner_apply,Real.inner_apply,pow_two]
      _ = _ := real_inner_self_eq_norm_sq x
  simp only [capConePolynomial,map_sub,map_pow,map_sum,map_mul,eval_C,eval_X,hi,hn]

theorem capConePolynomial_nonzero {d : ℕ} (p : EuclideanSpace ℝ (Fin d))
    (hp : ‖p‖ = 1) (a : ℝ) (ha : |a| < 1) : capConePolynomial p a ≠ 0 := by
  intro hz
  have he := eval_capConePolynomial p p a
  rw [hz,map_zero,real_inner_self_eq_norm_sq,hp] at he
  have hsq : a^2 < 1 := by nlinarith [sq_abs a,abs_nonneg a]
  norm_num at he
  linarith

/-- The actual latitude cone is Lebesgue null by polynomial zero-set nullity. -/
theorem capCone_zero_volume {d : ℕ} (p : EuclideanSpace ℝ (Fin d))
    (hp : ‖p‖ = 1) (a : ℝ) (ha : |a| < 1) :
    volume {x : EuclideanSpace ℝ (Fin d) | ⟪p,x⟫^2 - a^2 * ‖x‖^2 = 0} = 0 := by
  simpa only [eval_capConePolynomial] using
    polynomial_zero_volume_euclidean (capConePolynomial p a) (capConePolynomial_nonzero p hp a ha)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.eval_capConePolynomial
#print axioms KakeyaTwoScale.capConePolynomial_nonzero
#print axioms KakeyaTwoScale.capCone_zero_volume
