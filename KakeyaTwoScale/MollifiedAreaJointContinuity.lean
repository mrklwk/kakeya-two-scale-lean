module
public import KakeyaTwoScale.MollifiedAreaSeminorm

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal
noncomputable section
namespace KakeyaTwoScale

/-- Actual averaged area is jointly continuous in coefficient center and direction
for each fixed positive smoothing radius below two. The directional Lipschitz
constant is uniform in the center and smoothing radius. -/
theorem continuous_mollifiedArea_joint {d n D : ℕ}
    (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (hdegree : ∀ i, (m i).sum (fun _ e => e) ≤ D)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U) (hreg : IsOpen U ∨ IsClosed U)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 2) :
    Continuous (fun z : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × EuclideanSpace ℝ (Fin (n+1)) =>
      mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hbound ε z.1 z.2) := by
  let C : ℝ≥0 := ⟨((D : ℝ≥0∞) * volume (closedBall (0 : Fin n → ℝ) r)).toReal,ENNReal.toReal_nonneg⟩
  apply continuous_prod_of_continuous_lipschitzWith' _ C
  · intro p
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [dist_eq_norm,dist_eq_norm]
    change _ ≤ ((D : ℝ≥0∞) * volume (closedBall (0 : Fin n → ℝ) r)).toReal * ‖v-w‖
    exact mollifiedAreaSeminorm_sub_le m hm hdegree U hU hreg r hr hbound ε hε p v w
  · intro v
    simp only [mollifiedAreaSeminorm_apply]
    exact continuous_mollifiedCoefficientArea m hm hdegree U hU hreg r hr hbound ε hε hε2 v

end KakeyaTwoScale
#print axioms KakeyaTwoScale.continuous_mollifiedArea_joint
