module
public import KakeyaTwoScale.CentralHubBudget

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The pointwise geometric inequality integrates without suppressing infinite
exceptional fibers. All three domains and their geometric/sign hypotheses are
actual measurable sets; no area lower bound is supplied. -/
theorem integrated_central_hub_crossing {N : ℕ}
    (f : EuclideanSpace ℝ (Fin N) → ℝ) (hf : Continuous f)
    (α b : ℝ) (hα : 0 ≤ α) (hb : 0 ≤ b) (hsmall : α^2+N*b^2 < 1)
    (S T Z : Set (EuclideanSpace ℝ (Fin N)))
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hZ : MeasurableSet Z)
    (hs : ∀ x ∈ S, ‖x‖ ≤ α ∧ 0 < f x)
    (ht : ∀ y ∈ T, ‖y‖ ≤ α ∧ f y < 0)
    (hz : ∀ z ∈ Z, ∀ i, |z i| ≤ b) :
    volume S * volume T * volume Z ≤
      ∫⁻ x in S, ∫⁻ y in T, ∫⁻ z in Z,
        (∑ j : Fin N, ballCoordinateCount f j (coordinateHybrid x z j.val)) +
          ∑ j : Fin N, ballCoordinateCount f j (coordinateHybrid y z j.val) := by
  calc
    volume S * volume T * volume Z =
        ∫⁻ _x in S, ∫⁻ _y in T, ∫⁻ _z in Z, (1 : ℝ≥0∞) := by
      simp [mul_comm,mul_left_comm]
    _ ≤ _ := by
      apply setLIntegral_mono' hS
      intro x hx
      apply setLIntegral_mono' hT
      intro y hy
      apply setLIntegral_mono' hZ
      intro z hzz
      exact central_hub_count_lower f hf α b hα hb hsmall x y z
        (hs x hx).1 (ht y hy).1 (hz z hzz) (hs x hx).2 (ht y hy).2

/-- The integrated crossing result applies to literal polynomial evaluation,
including repeated factors, without any chosen smooth boundary model. -/
theorem polynomial_integrated_central_hub_crossing {N : ℕ}
    (P : MvPolynomial (Fin N) ℝ)
    (α b : ℝ) (hα : 0 ≤ α) (hb : 0 ≤ b) (hsmall : α^2+N*b^2 < 1)
    (S T Z : Set (EuclideanSpace ℝ (Fin N)))
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hZ : MeasurableSet Z)
    (hs : ∀ x ∈ S, ‖x‖ ≤ α ∧ 0 < MvPolynomial.eval x.ofLp P)
    (ht : ∀ y ∈ T, ‖y‖ ≤ α ∧ MvPolynomial.eval y.ofLp P < 0)
    (hz : ∀ z ∈ Z, ∀ i, |z i| ≤ b) :
    volume S * volume T * volume Z ≤
      ∫⁻ x in S, ∫⁻ y in T, ∫⁻ z in Z,
        (∑ j : Fin N, ballCoordinateCount (fun v => MvPolynomial.eval v.ofLp P) j (coordinateHybrid x z j.val)) +
          ∑ j : Fin N, ballCoordinateCount (fun v => MvPolynomial.eval v.ofLp P) j (coordinateHybrid y z j.val) :=
  integrated_central_hub_crossing _ (P.continuous_eval.comp (PiLp.continuous_ofLp 2 _))
    α b hα hb hsmall S T Z hS hT hZ hs ht hz

end KakeyaTwoScale
#print axioms KakeyaTwoScale.integrated_central_hub_crossing
#print axioms KakeyaTwoScale.polynomial_integrated_central_hub_crossing
