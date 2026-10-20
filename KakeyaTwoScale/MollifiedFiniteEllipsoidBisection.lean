module
public import KakeyaTwoScale.FiniteEllipsoidAreaBudget
public import KakeyaTwoScale.SphericalCapAreaLower

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal Function
noncomputable section
namespace KakeyaTwoScale

/-- Complete finite-family smoothing transfer for actual polynomial area.
Dimension chooses c first. Fixed coefficient/test-region data choose one delta
before the center, radius and any selected subset of exactly bisected ellipsoids.
All area is charged once to U in the common transported coordinate directions. -/
theorem mollified_finite_ellipsoid_bisection (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ι : Type) [Fintype ι] (d D : ℕ)
      (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
      (_hdegree : ∀ i, (m i).sum (fun _ e => e) ≤ D)
      (B : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ)) (b : ι → Fin (n+1) → ℝ)
      (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U) (_hreg : IsOpen U ∨ IsClosed U)
      (r : ℝ) (hr : 0 ≤ r)
      (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r),
      Pairwise (Disjoint on fun i => affineEllipsoid B (b i)) →
      (∀ i, affineEllipsoid B (b i) ⊆ U) →
      ∃ δ > 0, δ < 2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) (s : Finset ι),
      (∀ i ∈ s, polynomialRegionSignMass (coefficientPolynomial m p.val) (affineEllipsoid B (b i))=0) →
      c * (∑ i ∈ s, volume.real (affineEllipsoid B (b i))) ≤
        ∑ j : Fin (n+1), mollifiedCoefficientArea m hm U hU r hr hbound ε p
          (WithLp.toLp 2 (B (Pi.single j 1))) := by
  classical
  obtain ⟨c,hc,hraw⟩ := finite_translated_ellipsoid_bisection n
  refine ⟨c,hc,?_⟩
  intro ι _ d D m hm hdegree B b U hU hreg r hr hbound hd hEU
  obtain ⟨δ,hδ,hδ2,hmod⟩ := finite_ellipsoid_uniform_bisection m hm (fun _ : ι => B) b
  refine ⟨δ,hδ,hδ2,?_⟩
  intro ε hε hεδ p s hs
  change c * (∑ i ∈ s, volume.real (affineEllipsoid B (b i))) ≤
    ∑ j : Fin (n+1), sphereCapAverage ε
      (fun q => coefficientAreaSeminorm m hm U hU r hr hbound (metricCoefficient q)
        (WithLp.toLp 2 (B (Pi.single j 1)))) p
  apply sphereCapAverage_sum_lower ε hε p _
    (fun j => integrable_metricCoefficientArea m hm hdegree U hU hreg r hr hbound _ _)
  intro q hq
  have hpq : dist p q < δ := by
    exact (show dist p q < ε from by simpa only [mem_ball,dist_comm] using hq).trans_le hεδ
  have hsign (i : s) := hmod p q hpq i (hs i i.property)
  have hQ := coefficientPolynomial_nonzero m hm q.val (coefficientSphere_nonzero (metricCoefficient q))
  have hb := hraw s (coefficientPolynomial m q.val) hQ
    (coefficientSphereAtlas m hm (metricCoefficient q)) B (fun i : s => b i) U hU
    (fun i j hij => hd (fun he => hij (Subtype.ext he))) (fun i => hEU i)
    (fun i => (hsign i).1) (fun i => (hsign i).2)
  have hfinite (j : Fin (n+1)) :
      coefficientSphereArea m hm U hU (metricCoefficient q) (B (Pi.single j 1)) ≠ ∞ :=
    (coefficientSphereArea_lt_top m hm U hU r hr hbound (metricCoefficient q) _).ne
  have hreal := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun j _ => hfinite j)) hb
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc.le,
    ENNReal.toReal_sum (fun (i : s) _ => (affineEllipsoid_finite B (b (i : ι))).ne),
    ENNReal.toReal_sum (fun j _ => hfinite j)] at hreal
  rw [Finset.sum_coe_sort s (fun i : ι => (volume (affineEllipsoid B (b i))).toReal)] at hreal
  simpa only [Measure.real,coefficientAreaSeminorm_apply] using hreal

end KakeyaTwoScale
#print axioms KakeyaTwoScale.mollified_finite_ellipsoid_bisection
