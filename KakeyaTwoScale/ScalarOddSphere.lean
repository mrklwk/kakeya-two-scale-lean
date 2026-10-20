module
public import KakeyaTwoScale.PolynomialMassSphere
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

noncomputable section
namespace KakeyaTwoScale

/-- The scalar case follows from connectedness and IVT. This is not the
general vector-valued Borsuk–Ulam theorem. -/
theorem scalar_odd_sphere_zero {ι : Type*} [Fintype ι]
    (hd : 1 < Fintype.card ι) (f : CoefficientSphere ι → ℝ)
    (hf : Continuous f) (ho : ∀ c, f (coefficientAntipode c) = -f c) :
    ∃ c, f c = 0 := by
  have hr : 1 < Module.rank ℝ (EuclideanSpace ℝ ι) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace]
    exact_mod_cast hd
  have hs : IsConnected {c : EuclideanSpace ℝ ι | ‖c‖ = 1} := by
    simpa [Metric.sphere, dist_zero_right] using
      isConnected_sphere hr (0 : EuclideanSpace ℝ ι) (by norm_num : (0:ℝ)≤1)
  have : ConnectedSpace (CoefficientSphere ι) := Subtype.connectedSpace hs
  obtain ⟨c⟩ := (inferInstance : Nonempty (CoefficientSphere ι))
  by_cases h : f c ≤ 0
  · exact intermediate_value_univ c (coefficientAntipode c) hf
      ⟨h, by rw [ho]; linarith⟩
  · exact intermediate_value_univ (coefficientAntipode c) c hf
      ⟨by rw [ho]; linarith, by linarith⟩

/-- Unconditional existence for one density and any injective monomial
family with at least two coefficients. -/
theorem exists_scalar_polynomial_bisector {ι : Type*} [Fintype ι] {n D : ℕ}
    (hd : 1 < Fintype.card ι) (m : ι → (Fin n →₀ ℕ))
    (hm : Function.Injective m) (hdeg : ∀ i, (m i).sum (fun _ e => e) ≤ D)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : MeasureTheory.Integrable w) :
    ∃ p : MvPolynomial (Fin n) ℝ, p ≠ 0 ∧ p.totalDegree ≤ D ∧
      (∫ x in {x : EuclideanSpace ℝ (Fin n) | 0 < MvPolynomial.eval (fun i => x i) p}, w x) =
        (∫ x, w x)/2 ∧
      (∫ x in {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun i => x i) p < 0}, w x) =
        (∫ x, w x)/2 := by
  obtain ⟨c,hc⟩ := scalar_odd_sphere_zero hd (sphereSignedMass m w)
    (continuous_sphereSignedMass m hm w hw) (sphereSignedMass_odd m w)
  have hp := coefficientPolynomial_nonzero m hm c.val (coefficientSphere_nonzero c)
  exact ⟨coefficientPolynomial m c.val, hp, coefficientPolynomial_degree m hdeg c.val,
    euclideanSignedPolynomialMass_zero_bisects _ hp w hw hc⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.scalar_odd_sphere_zero
#print axioms KakeyaTwoScale.exists_scalar_polynomial_bisector
