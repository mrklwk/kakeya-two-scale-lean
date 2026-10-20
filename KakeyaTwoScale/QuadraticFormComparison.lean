module
public import KakeyaTwoScale.ConvexCoordinateEllipsoid

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

/-- The actual quadratic polynomial associated to real matrix coefficients. -/
def matrixQuadraticValue {N : ℕ} (Q : Fin N → Fin N → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, Q i j * x i * x j

/-- Entrywise perturbations control the entire quadratic form, with a deliberately
nonoptimal dimension-only factor N². No positivity or symmetry is needed. -/
theorem matrixQuadraticValue_error {N : ℕ} (Q P : Fin N → Fin N → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hQP : ∀ i j, |Q i j-P i j| ≤ δ) (x : Fin N → ℝ) :
    |matrixQuadraticValue Q x-matrixQuadraticValue P x| ≤
      (N:ℝ)^2 * δ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖^2 := by
  let r := ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖
  have hr : 0 ≤ r := norm_nonneg _
  have hx (i) : |x i| ≤ r := by
    simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N)) i)
  have he : matrixQuadraticValue Q x-matrixQuadraticValue P x =
      ∑ i, ∑ j, (Q i j-P i j)*x i*x j := by
    simp only [matrixQuadraticValue,Finset.sum_sub_distrib,sub_mul]
  rw [he]
  calc
    _ ≤ ∑ i, |∑ j, (Q i j-P i j)*x i*x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, |(Q i j-P i j)*x i*x j| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, δ*r*r := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      exact mul_le_mul (mul_le_mul (hQP i j) (hx i) (abs_nonneg _) hδ)
        (hx j) (abs_nonneg _) (mul_nonneg hδ hr)
    _ = _ := by simp [r]; ring

/-- Closeness in the fixed coefficient norm implies multiplicative comparison
for coercive quadratic forms. The radius depends only on N and the common
coercivity a, and is independent of either form. -/
theorem close_coercive_quadratic_forms {N : ℕ} (a : ℝ) (ha : 0<a)
    (Q P : Fin N → Fin N → ℝ)
    (hQ : ∀ x, a*‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖^2 ≤ matrixQuadraticValue Q x)
    (hP : ∀ x, a*‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖^2 ≤ matrixQuadraticValue P x)
    (hd : dist Q P ≤ a/((N:ℝ)^2+1)) :
    ∀ x, matrixQuadraticValue Q x ≤ 2*matrixQuadraticValue P x ∧
      matrixQuadraticValue P x ≤ 2*matrixQuadraticValue Q x := by
  have hδ : 0 ≤ a/((N:ℝ)^2+1) := by positivity
  have hc (i j) : |Q i j-P i j| ≤ a/((N:ℝ)^2+1) := by
    exact (show |Q i j-P i j| ≤ dist Q P from by
      simpa only [Real.dist_eq] using
        (dist_le_pi_dist (Q i) (P i) j).trans (dist_le_pi_dist Q P i)).trans hd
  intro x
  have he := matrixQuadraticValue_error Q P _ hδ hc x
  have hcoef : (N:ℝ)^2*(a/((N:ℝ)^2+1)) ≤ a := by
    have heq : (a/((N:ℝ)^2+1))*((N:ℝ)^2+1)=a :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith
  have hb := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖)
  have hab := abs_le.mp (he.trans hb)
  constructor <;> nlinarith [hQ x,hP x]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.matrixQuadraticValue_error
#print axioms KakeyaTwoScale.close_coercive_quadratic_forms
