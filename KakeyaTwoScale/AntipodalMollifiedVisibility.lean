module
public import KakeyaTwoScale.SphericalAntipodalAverage
public import KakeyaTwoScale.PolynomialRegionSignMass
public import KakeyaTwoScale.AffineEllipsoidArea
public import KakeyaTwoScale.ActualMollifiedVisibilityBody

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The actual sign labels reverse under the same coefficient antipode. -/
theorem polynomialRegionSignMass_antipodal {d N : ℕ}
    (m : Fin d → (Fin N →₀ ℕ)) (E : Set (Fin N → ℝ))
    (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    polynomialRegionSignMass (coefficientPolynomial m (metricSphereAntipode d p).val) E =
      -polynomialRegionSignMass (coefficientPolynomial m p.val) E := by
  change polynomialRegionSignMass (coefficientPolynomial m (-p.val)) E = _
  rw [coefficientPolynomial_neg]
  simp only [polynomialRegionSignMass,map_neg,realSign_neg,integral_neg]

/-- Raw actual area is even in the polynomial coefficients. Zero-set equality
and all-direction atlas independence compare the independently chosen atlases. -/
theorem coefficientSphereArea_antipodal {d n : ℕ}
    (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U)
    (q : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) (v : Fin (n+1) → ℝ) :
    coefficientSphereArea m hm U hU (metricCoefficient (metricSphereAntipode d q)) v =
      coefficientSphereArea m hm U hU (metricCoefficient q) v := by
  apply DisjointChartAtlas.directionalArea_eq_of_set_eq
  have hp : coefficientPolynomial m (metricCoefficient (metricSphereAntipode d q)).val =
      -coefficientPolynomial m (metricCoefficient q).val := coefficientPolynomial_neg m q.val
  ext x
  simp only [mem_inter_iff,mem_ofPred_eq,hp,map_neg,neg_eq_zero]

section ActualEvenness
variable {d n D : ℕ}
variable (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
variable (hdegree : ∀ i, (m i).sum (fun _ e => e) ≤ D)
variable (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U) (hreg : IsOpen U ∨ IsClosed U)
variable (r : ℝ) (hr : 0 ≤ r)
variable (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)

/-- The existing literal intrinsic cap average is antipodally even. -/
theorem mollifiedCoefficientArea_antipodal (ε : ℝ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) (v : EuclideanSpace ℝ (Fin (n+1))) :
    mollifiedCoefficientArea m hm U hU r hr hbound ε (metricSphereAntipode d p) v =
      mollifiedCoefficientArea m hm U hU r hr hbound ε p v := by
  apply sphereCapAverage_antipodal
  intro q
  simp only [coefficientAreaSeminorm_apply,coefficientSphereArea_antipodal]

theorem mollifiedAreaSeminorm_antipodal (ε : ℝ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hbound ε (metricSphereAntipode d p) =
      mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hbound ε p := by
  ext v
  simp only [mollifiedAreaSeminorm_apply,mollifiedCoefficientArea_antipodal]

/-- Actual visibility bodies agree at opposite coefficient centers, so the
future antipodal covering argument needs no assumed symmetry of body choice. -/
theorem mollifiedVisibilityBody_antipodal (ε : ℝ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    mollifiedVisibilityBody m hm hdegree U hU hreg r hr hbound ε (metricSphereAntipode d p) =
      mollifiedVisibilityBody m hm hdegree U hU hreg r hr hbound ε p := by
  unfold mollifiedVisibilityBody
  rw [mollifiedAreaSeminorm_antipodal]

end ActualEvenness
end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomialRegionSignMass_antipodal
#print axioms KakeyaTwoScale.coefficientSphereArea_antipodal
#print axioms KakeyaTwoScale.mollifiedCoefficientArea_antipodal
#print axioms KakeyaTwoScale.mollifiedAreaSeminorm_antipodal
#print axioms KakeyaTwoScale.mollifiedVisibilityBody_antipodal
