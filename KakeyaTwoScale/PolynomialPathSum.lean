module
public import KakeyaTwoScale.CoordinateBallVolume

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

def polynomialPathSum {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (z : (Fin (n+1) → ℝ) × (Fin (n+1) → ℝ)) : ℝ≥0∞ :=
  ∑ j : Fin (n+1), ballCoordinateCount (fun v => MvPolynomial.eval v.ofLp P) j
    (coordinateHybrid (WithLp.toLp 2 z.1) (WithLp.toLp 2 z.2) j.val)

theorem measurable_polynomial_path_term {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ) (j : Fin (n+1)) :
    Measurable (fun z : (Fin (n+1) → ℝ) × (Fin (n+1) → ℝ) =>
      ballCoordinateCount (fun v => MvPolynomial.eval v.ofLp P) j
        (coordinateHybrid (WithLp.toLp 2 z.1) (WithLp.toLp 2 z.2) j.val)) := by
  have hmap : Continuous (fun z : (Fin (n+1) → ℝ) × (Fin (n+1) → ℝ) =>
      ((WithLp.toLp 2 z.1 : EuclideanSpace ℝ (Fin (n+1))), (WithLp.toLp 2 z.2 : EuclideanSpace ℝ (Fin (n+1))))) :=
    ((PiLp.continuous_toLp 2 _).comp continuous_fst).prodMk ((PiLp.continuous_toLp 2 _).comp continuous_snd)
  have hh := (measurable_path_count (fun v : EuclideanSpace ℝ (Fin (n+1)) => MvPolynomial.eval v.ofLp P) (P.continuous_eval.comp (PiLp.continuous_ofLp 2 _)) j).comp hmap.measurable
  simpa only [Function.comp_def] using hh

theorem measurable_polynomialPathSum {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ) :
    Measurable (polynomialPathSum P) := by
  unfold polynomialPathSum
  exact Finset.measurable_sum _ (fun j _ => measurable_polynomial_path_term P j)

/-- The exact finite sum of actual path integrals is controlled by the actual
sum of coordinate areas with their geometric interval factors. -/
theorem polynomialPathSum_box_bound {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (A : DisjointChartAtlas n {x | MvPolynomial.eval x P=0}) (α b : ℝ) :
    (∫⁻ z, polynomialPathSum P z
      ∂((Measure.pi (fun _ : Fin (n+1) => intervalVolume α)).prod (Measure.pi (fun _ : Fin (n+1) => intervalVolume b)))) ≤
      ∑ j : Fin (n+1),
        (ENNReal.ofReal (2*α))^(j.val+1) * (ENNReal.ofReal (2*b))^(n+1-j.val) *
        (A.restrict (coordinateEuclideanBall (n+1) 1) (coordinateEuclideanBall_open _ _).measurableSet).directionalArea (Pi.single j 1) := by
  unfold polynomialPathSum
  rw [lintegral_finsetSum _ (fun j _ => measurable_polynomial_path_term P j)]
  apply Finset.sum_le_sum
  intro j _
  have h := polynomial_box_crossing_area_bound P A α b j
  rw [crossing_box_factor] at h
  exact h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.measurable_polynomialPathSum
#print axioms KakeyaTwoScale.polynomialPathSum_box_bound
