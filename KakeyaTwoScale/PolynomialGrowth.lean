module
public import KakeyaTwoScale.PerturbedPolynomialCritical
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

open MvPolynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

def polynomialCoefficientNorm {n : ℕ} (P : MvPolynomial (Fin n) ℝ) : ℝ :=
  ∑ s ∈ P.support, ‖P.coeff s‖

/-- Explicit coefficient-norm growth bound for arbitrary multivariate
polynomials on coordinate boxes, retaining the total-degree exponent. -/
theorem polynomial_eval_norm_le {n D : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ D) (x : Fin n → ℝ) (R : ℝ) (hR : 1 ≤ R)
    (hx : ∀ i, ‖x i‖ ≤ R) :
    ‖eval x P‖ ≤ polynomialCoefficientNorm P * R^D := by
  classical
  rw [eval_eq']
  calc
    _ ≤ ∑ s ∈ P.support, ‖P.coeff s * ∏ i, x i ^ s i‖ := norm_sum_le _ _
    _ = ∑ s ∈ P.support, ‖P.coeff s‖ * ∏ i, ‖x i‖ ^ s i := by
      simp only [norm_mul,norm_prod,norm_pow]
    _ ≤ ∑ s ∈ P.support, ‖P.coeff s‖ * R^D := by
      apply Finset.sum_le_sum
      intro s hs
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ ∏ i, R ^ s i := Finset.prod_le_prod₀ (by intros; positivity)
          (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hx i) _)
        _ = R ^ (∑ i, s i) := by rw [Finset.prod_pow_eq_pow_sum]
        _ ≤ R^D := by
          apply pow_le_pow_right₀ hR
          have hd := (le_totalDegree hs).trans hP
          have he : s.sum (fun _ e => e) = ∑ i, s i :=
            Finsupp.sum_fintype _ _ (fun _ => rfl)
          rwa [he] at hd
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- On a nonempty coordinate space, one even-power sum dominates the matching
power of the sup norm, with no dimension loss. -/
theorem even_power_sum_ge_norm {n k : ℕ} (hn : 0 < n) (hk : Even k) (x : Fin n → ℝ) :
    ‖x‖^k ≤ ∑ i, x i ^ k := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨⟨i,hi⟩,_⟩ := IsGreatest.pi_norm x
  change ‖x i‖ = ‖x‖ at hi
  calc
    ‖x‖^k = x i ^ k := by rw [← hi,Real.norm_eq_abs,hk.pow_abs]
    _ ≤ ∑ j, x j ^ k := Finset.single_le_sum (fun j _ => hk.pow_nonneg _) (Finset.mem_univ i)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomial_eval_norm_le
#print axioms KakeyaTwoScale.even_power_sum_ge_norm
