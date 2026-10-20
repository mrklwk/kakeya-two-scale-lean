module
public import KakeyaTwoScale.PolynomialRegionSignMass
public import KakeyaTwoScale.PolynomialEllipsoidBisection

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- A single radius, chosen before both coefficient centers, controls all actual
normalized signed masses in a fixed finite family of ellipsoids. Empty families
and empty coefficient spheres need no special selection convention. -/
theorem finite_ellipsoid_uniform_sign_mass {ι : Type*} [Fintype ι] {d N : ℕ}
    (m : Fin d → (Fin N →₀ ℕ)) (hm : Function.Injective m)
    (B : ι → ((Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ))) (b : ι → Fin N → ℝ) :
    ∃ δ > 0, δ < 2 ∧ ∀ p q : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      dist p q < δ → ∀ i,
      polynomialRegionSignMass (coefficientPolynomial m p.val) (affineEllipsoid (B i) (b i)) = 0 →
      |polynomialRegionSignMass (coefficientPolynomial m q.val) (affineEllipsoid (B i) (b i))| ≤
        volume.real (affineEllipsoid (B i) (b i)) / 5 := by
  let f (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) (i : ι) :=
    polynomialRegionSignMass (coefficientPolynomial m p.val) (affineEllipsoid (B i) (b i)) /
      volume.real (affineEllipsoid (B i) (b i))
  have hf : Continuous f := continuous_pi (fun i =>
    (continuous_metric_polynomialRegionSignMass m hm _ (affineEllipsoid_finite _ _)).div_const _)
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) (1/5) (by norm_num)
  refine ⟨min δ 1,lt_min hδ zero_lt_one,(min_le_right _ _).trans_lt (by norm_num),?_⟩
  intro p q hpq i hz
  have hh := hmod (a:=p) (b:=q) (hpq.trans_le (min_le_left _ _))
  have hi : dist (f p i) (f q i) < (1/5:ℝ) := lt_of_le_of_lt (dist_le_pi_dist _ _ i) hh
  have hV : 0 < volume.real (affineEllipsoid (B i) (b i)) :=
    ENNReal.toReal_pos (affineEllipsoid_positive _ _).ne' (affineEllipsoid_finite _ _).ne
  simp only [f,hz,zero_div,dist_zero_left,Real.norm_eq_abs,abs_div,
    abs_of_pos hV] at hi
  exact (div_le_iff₀ hV).mp hi.le |>.trans_eq (by ring)

/-- Uniform robust bisection for all members of a finite actual ellipsoid family.
The radius is independent of the subsequently selected center and bisected subset. -/
theorem finite_ellipsoid_uniform_bisection {ι : Type*} [Fintype ι] {d N : ℕ}
    (m : Fin d → (Fin N →₀ ℕ)) (hm : Function.Injective m)
    (B : ι → ((Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ))) (b : ι → Fin N → ℝ) :
    ∃ δ > 0, δ < 2 ∧ ∀ p q : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      dist p q < δ → ∀ i,
      polynomialRegionSignMass (coefficientPolynomial m p.val) (affineEllipsoid (B i) (b i)) = 0 →
      (2/5:ℝ)*volume.real (affineEllipsoid (B i) (b i)) ≤
        volume.real (affineEllipsoid (B i) (b i) ∩ {x | 0 < MvPolynomial.eval x (coefficientPolynomial m q.val)}) ∧
      (2/5:ℝ)*volume.real (affineEllipsoid (B i) (b i)) ≤
        volume.real (affineEllipsoid (B i) (b i) ∩ {x | MvPolynomial.eval x (coefficientPolynomial m q.val) < 0}) := by
  obtain ⟨δ,hδ,hδ2,h⟩ := finite_ellipsoid_uniform_sign_mass m hm B b
  refine ⟨δ,hδ,hδ2,?_⟩
  intro p q hpq i hz
  exact polynomialRegionSignMass_robust_bisection _
    (coefficientPolynomial_nonzero m hm q.val (coefficientSphere_nonzero (metricCoefficient q)))
    _ (affineEllipsoid_finite _ _) (h p q hpq i hz)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_ellipsoid_uniform_sign_mass
#print axioms KakeyaTwoScale.finite_ellipsoid_uniform_bisection
