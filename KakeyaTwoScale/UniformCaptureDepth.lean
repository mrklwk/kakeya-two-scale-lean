module
public import KakeyaTwoScale.UniversalCaptureSweep

@[expose] public section

open Set Metric MeasureTheory MvPolynomial
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- One positive constant works BEFORE early-stop depth, chart choice, outer
level, coefficients, finite original population and every real scale. Finite
maximization is implemented as a dominating finite sum. -/
theorem uniform_capture_depth_volume (n e D R : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℕ, r ≤ R → ∀ (h : Fin (n+1)) (outer : Fin r),
      ∀ (P : Fin r → Fin e → MvPolynomial (Fin (n+1)) ℝ),
      (∀ i j, (P i j).totalDegree ≤ D) →
      ∀ (center : EuclideanSpace ℝ (Fin (n+1))) (L : Fin r → ℝ),
      (∀ i, 0 < L i) → ∀ rho s ell : ℝ, 0 < rho → 0 < ell →
      volume {v | ∃ a, universalEligibleLine D C h outer (captureParameters P center L rho s ell) v a} *
        ENNReal.ofReal (ell^(n+1)) ≤
        ENNReal.ofReal K * (volume.prod volume)
          {z : (Fin n → ℝ) × ℝ | center+euclideanUnsplit h (z.2,z.1) ∈
            thickening rho (captureZeroSet (P outer) ∩ closedBall center ((C+4)*L outer))} := by
  classical
  let B := Σ r : Fin (R+1), Fin (n+1) × Fin r.val
  have hb (j : B) := universal_capture_sweep_volume n j.1.val e D C hC j.2.1 j.2.2
  choose K hK M hvol using hb
  let w : B → ℝ := fun j => K j*((M j:ℝ)+1)
  have hw (j : B) : 0 ≤ w j := mul_nonneg (hK j).le (by positivity)
  let total : ℝ := 1+∑ j : B, w j
  have htotal : 0 < total := by
    have hs := Finset.sum_nonneg (fun j (_ : j∈(Finset.univ : Finset B)) => hw j)
    dsimp [total]
    linarith
  refine ⟨total,htotal,?_⟩
  intro r hr h outer P hP center L hL rho s ell hrho hell
  let j : B := ⟨⟨r,by omega⟩,h,outer⟩
  have hs := Finset.single_le_sum (fun i (_ : i∈(Finset.univ : Finset B)) => hw i)
    (Finset.mem_univ j)
  have hreal : K j*(M j:ℝ) ≤ total := by
    have hh := hK j
    dsimp [w,total] at hs ⊢
    linarith
  have hcoef : ENNReal.ofReal (K j)*(M j:ℝ≥0∞) ≤ ENNReal.ofReal total := by
    rw [← ENNReal.ofReal_natCast (M j),← ENNReal.ofReal_mul (hK j).le]
    exact ENNReal.ofReal_le_ofReal hreal
  exact (hvol j P hP center L hL rho s ell hrho hell).trans
    (mul_le_mul hcoef le_rfl zero_le zero_le)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_capture_depth_volume
