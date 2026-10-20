module
public import KakeyaTwoScale.ActualMollifiedVisibilityBody
public import KakeyaTwoScale.VisibilityBodyVolumeComparison

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal Pointwise
noncomputable section
namespace KakeyaTwoScale
section Stability
variable {d n D : ℕ}
variable (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
variable (hdegree : ∀ i, (m i).sum (fun _ e => e) ≤ D)
variable (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U) (hreg : IsOpen U ∨ IsClosed U)
variable (r : ℝ) (hr : 0 ≤ r)
variable (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)

include hdegree hreg

/-- Uniform coefficient perturbations control actual visibility bodies and their
volumes. The modulus is uniform over the entire coefficient sphere. -/
theorem mollifiedVisibilityBody_uniform_stability
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 2) (δ : ℝ) (hδ : 0 < δ) :
    ∃ τ > 0, ∀ p q : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, dist p q < τ →
      ((1+δ)⁻¹ • mollifiedVisibilityBody m hm hdegree U hU hreg r hr hbound ε p ⊆
        mollifiedVisibilityBody m hm hdegree U hU hreg r hr hbound ε q) ∧
      (mollifiedVisibilityBody m hm hdegree U hU hreg r hr hbound ε q ⊆
        (1+δ) • mollifiedVisibilityBody m hm hdegree U hU hreg r hr hbound ε p) ∧
      (ENNReal.ofReal (((1+δ)⁻¹)^(n+1)) * volume (mollifiedVisibilityBody m hm hdegree U hU hreg r hr hbound ε p) ≤
        volume (mollifiedVisibilityBody m hm hdegree U hU hreg r hr hbound ε q)) ∧
      (volume (mollifiedVisibilityBody m hm hdegree U hU hreg r hr hbound ε q) ≤
        ENNReal.ofReal ((1+δ)^(n+1)) * volume (mollifiedVisibilityBody m hm hdegree U hU hreg r hr hbound ε p)) := by
  let s := mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hbound ε
  have hc : Continuous (fun z : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × EuclideanSpace ℝ (Fin (n+1)) => s z.1 z.2) :=
    continuous_mollifiedArea_joint m hm hdegree U hU hreg r hr hbound ε hε hε2
  obtain ⟨τ,hτ,ht⟩ := uniform_seminorm_family_error s hc δ hδ
  refine ⟨τ,hτ,?_⟩
  intro p q hpq
  have hb := visibilityBody_comparison (s p) (s q) δ hδ.le (ht p q hpq)
  have hv := visibilityBody_volume_comparison (s p) (s q) δ hδ.le (ht p q hpq)
  exact ⟨hb.1,hb.2,hv⟩

end Stability
end KakeyaTwoScale
#print axioms KakeyaTwoScale.mollifiedVisibilityBody_uniform_stability
