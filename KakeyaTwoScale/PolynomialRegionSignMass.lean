module
public import KakeyaTwoScale.SignedPolynomialMass
public import KakeyaTwoScale.MollifiedCoefficientArea
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

open Set MeasureTheory Metric Filter
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Literal signed volume on the spatial region, in the same Pi coordinates as area. -/
def polynomialRegionSignMass {N : ℕ} (Q : MvPolynomial (Fin N) ℝ)
    (E : Set (Fin N → ℝ)) : ℝ :=
  ∫ x in E, realSign (MvPolynomial.eval x Q)

theorem continuous_metric_polynomialRegionSignMass {d N : ℕ}
    (m : Fin d → (Fin N →₀ ℕ)) (hm : Function.Injective m)
    (E : Set (Fin N → ℝ)) (hEf : volume E < ∞) :
    Continuous (fun c : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      polynomialRegionSignMass (coefficientPolynomial m c.val) E) := by
  apply continuous_iff_continuousAt.mpr
  intro c
  have hQ := coefficientPolynomial_nonzero m hm c.val (coefficientSphere_nonzero (metricCoefficient c))
  have hz : ∀ᵐ x ∂volume, MvPolynomial.eval x (coefficientPolynomial m c.val) ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using polynomial_zero_volume _ hQ
  have hc := continuousAt_signed_mass (volume.restrict E)
    (fun (q : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) x =>
      MvPolynomial.eval x (coefficientPolynomial m q.val)) (fun _ => (1:ℝ)) c
    (fun q => (coefficientPolynomial m q.val).continuous_eval.measurable)
    (integrableOn_const hEf.ne)
    (fun x => ((coefficientPolynomial_eval_continuous m x).comp continuous_subtype_val).continuousAt)
    (ae_restrict_of_ae hz)
  simpa only [mul_one,polynomialRegionSignMass] using hc

/-- Actual strict-sign volumes sum to the full region volume for a nonzero
polynomial, and their difference is the literal signed integral. -/
theorem polynomialRegionSignMass_identities {N : ℕ}
    (Q : MvPolynomial (Fin N) ℝ) (hQ : Q ≠ 0)
    (E : Set (Fin N → ℝ)) (hEf : volume E < ∞) :
    volume.real (E ∩ {x | 0 < MvPolynomial.eval x Q}) +
      volume.real (E ∩ {x | MvPolynomial.eval x Q < 0}) = volume.real E ∧
    volume.real (E ∩ {x | 0 < MvPolynomial.eval x Q}) -
      volume.real (E ∩ {x | MvPolynomial.eval x Q < 0}) = polynomialRegionSignMass Q E := by
  let μ := volume.restrict E
  let f := fun x => MvPolynomial.eval x Q
  have hf : Measurable f := Q.continuous_eval.measurable
  have hw : Integrable (fun _ : Fin N → ℝ => (1:ℝ)) μ := integrableOn_const hEf.ne
  have hp : MeasurableSet {x | 0 < f x} := measurableSet_lt measurable_const hf
  have hn : MeasurableSet {x | f x < 0} := measurableSet_lt hf measurable_const
  have hz : ∀ᵐ x ∂μ, f x ≠ 0 := by
    apply ae_restrict_of_ae
    apply ae_iff.mpr
    simpa only [not_not] using polynomial_zero_volume Q hQ
  have he : (fun x => ({x | 0 < f x} : Set (Fin N → ℝ)).indicator (fun _ => (1:ℝ)) x +
      ({x | f x < 0} : Set (Fin N → ℝ)).indicator (fun _ => (1:ℝ)) x) =ᵐ[μ] (fun _ => 1) := by
    filter_upwards [hz] with x hx
    rcases lt_or_gt_of_ne hx with hh | hh
    · simp [hh,show ¬0 < f x by linarith]
    · simp [hh,show ¬f x < 0 by linarith]
  have hs := integral_congr_ae he
  rw [integral_add (hw.indicator hp) (hw.indicator hn),integral_indicator hp,integral_indicator hn] at hs
  have hd := signed_mass_eq_positive_sub_negative μ f (fun _ => 1) hf hw
  simp only [mul_one] at hd
  have hpos : (∫ _x in {x | 0 < f x}, (1:ℝ) ∂μ) = volume.real (E ∩ {x | 0 < f x}) := by
    simp [μ,Measure.real,Measure.restrict_apply hp,inter_comm]
  have hneg : (∫ _x in {x | f x < 0}, (1:ℝ) ∂μ) = volume.real (E ∩ {x | f x < 0}) := by
    simp [μ,Measure.real,Measure.restrict_apply hn,inter_comm]
  rw [hpos,hneg] at hs hd
  refine ⟨?_,hd.symm⟩
  simpa [μ,Measure.real] using hs

/-- Signed-mass tolerance V/5 implies both actual strict signs have mass >=2V/5. -/
theorem polynomialRegionSignMass_robust_bisection {N : ℕ}
    (Q : MvPolynomial (Fin N) ℝ) (hQ : Q ≠ 0)
    (E : Set (Fin N → ℝ)) (hEf : volume E < ∞)
    (h : |polynomialRegionSignMass Q E| ≤ volume.real E / 5) :
    (2/5:ℝ)*volume.real E ≤ volume.real (E ∩ {x | 0 < MvPolynomial.eval x Q}) ∧
    (2/5:ℝ)*volume.real E ≤ volume.real (E ∩ {x | MvPolynomial.eval x Q < 0}) := by
  obtain ⟨hs,hd⟩ := polynomialRegionSignMass_identities Q hQ E hEf
  obtain ⟨hl,hu⟩ := abs_le.mp h
  constructor <;> linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.continuous_metric_polynomialRegionSignMass
#print axioms KakeyaTwoScale.polynomialRegionSignMass_identities
#print axioms KakeyaTwoScale.polynomialRegionSignMass_robust_bisection
