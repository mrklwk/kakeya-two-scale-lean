module
public import KakeyaTwoScale.VisibilityBodyComparison

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal NNReal
noncomputable section
namespace KakeyaTwoScale

section ActualBody
variable {d n D : ℕ}
variable (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
variable (hdegree : ∀ i, (m i).sum (fun _ e => e) ≤ D)
variable (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U) (hreg : IsOpen U ∨ IsClosed U)
variable (r : ℝ) (hr : 0 ≤ r)
variable (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)

/-- Visibility body of the actual mollified area, with the unit-norm cutoff. -/
def mollifiedVisibilityBody (ε : ℝ) (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    Set (EuclideanSpace ℝ (Fin (n+1))) :=
  seminormVisibilityBody (mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hbound ε p)

include hdegree hreg

theorem mollifiedVisibilityBody_convex (ε : ℝ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    Convex ℝ (mollifiedVisibilityBody m hm hdegree U hU hreg r hr hbound ε p) :=
  seminormVisibilityBody_convex _

theorem mollifiedVisibilityBody_compact (ε : ℝ) (hε : 0 < ε)
    (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    IsCompact (mollifiedVisibilityBody m hm hdegree U hU hreg r hr hbound ε p) := by
  apply seminormVisibilityBody_compact
  let C : ℝ≥0 := ⟨((D : ℝ≥0∞) * volume (closedBall (0 : Fin n → ℝ) r)).toReal,ENNReal.toReal_nonneg⟩
  have hl : LipschitzWith C (mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hbound ε p) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [dist_eq_norm,dist_eq_norm]
    change _ ≤ ((D : ℝ≥0∞) * volume (closedBall (0 : Fin n → ℝ) r)).toReal * ‖v-w‖
    exact mollifiedAreaSeminorm_sub_le m hm hdegree U hU hreg r hr hbound ε hε p v w
  exact hl.continuous

theorem mollifiedVisibilityBody_volume_bounds (ε : ℝ) (hε : 0 < ε)
    (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    0 < volume (mollifiedVisibilityBody m hm hdegree U hU hreg r hr hbound ε p) ∧
    volume (mollifiedVisibilityBody m hm hdegree U hU hreg r hr hbound ε p) < ∞ := by
  have h := seminormVisibilityBody_volume_bounds
    (mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hbound ε p)
    _ ENNReal.toReal_nonneg
    (mollifiedAreaSeminorm_le m hm hdegree U hU hreg r hr hbound ε hε p)
  exact h.2

end ActualBody
end KakeyaTwoScale
#print axioms KakeyaTwoScale.mollifiedVisibilityBody
#print axioms KakeyaTwoScale.mollifiedVisibilityBody_convex
#print axioms KakeyaTwoScale.mollifiedVisibilityBody_compact
#print axioms KakeyaTwoScale.mollifiedVisibilityBody_volume_bounds
