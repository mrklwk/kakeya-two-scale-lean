module
public import KakeyaTwoScale.CoefficientLocalizedCounts
public import KakeyaTwoScale.PolynomialMassSphere
public import KakeyaTwoScale.LocalizedAreaSeminorm

@[expose] public section

open Set MeasureTheory MvPolynomial Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- An actual full atlas for each normalized coefficient vector. No regularity
of this choice as coefficients vary is assumed. -/
def coefficientSphereAtlas {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m) (c : CoefficientSphere ι) :
    DisjointChartAtlas n {x | eval x (coefficientPolynomial m c.val)=0} :=
  (polynomial_disjoint_chart_atlas (coefficientPolynomial m c.val)
    (coefficientPolynomial_nonzero m hm c.val (coefficientSphere_nonzero c))).some

/-- Actual localized cofactor area on the coefficient sphere. -/
def coefficientSphereArea {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U)
    (c : CoefficientSphere ι) (v : Fin (n+1) → ℝ) : ℝ≥0∞ :=
  ((coefficientSphereAtlas m hm c).restrict U hU).directionalArea v

/-- The actual chosen-atlas area equals the jointly measurable geometric count.
The frame is fixed before the coefficients. -/
theorem coefficientSphereArea_frame {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U)
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (c : CoefficientSphere ι) :
    coefficientSphereArea m hm U hU c (orthogonalCoordinates R (Pi.single 0 1)) =
      ∫⁻ y, coefficientLocalizedCount m R U (c.val,y) :=
  ((coefficientSphereAtlas m hm c).restrict U hU).frame_identity R

/-- Coefficient measurability in every fixed direction. Infinite areas are
retained here; no boundedness assumption or measurable atlas choice is needed. -/
theorem measurable_coefficientSphereArea {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U)
    (hreg : IsOpen U ∨ IsClosed U) (v : Fin (n+1) → ℝ) :
    Measurable (fun c => coefficientSphereArea m hm U hU c v) := by
  have hunit (u : EuclideanSpace ℝ (Fin (n+1))) (hu : ‖u‖ = 1) :
      Measurable (fun c => coefficientSphereArea m hm U hU c (WithLp.ofLp u)) := by
    obtain ⟨R,hR⟩ := exists_axis_isometry (0 : Fin (n+1)) u hu
    have hcount : Measurable (coefficientLocalizedCount m R U) :=
      hreg.elim (measurable_coefficientLocalizedCount_open m R U)
        (measurable_coefficientLocalizedCount_closed m R U)
    have hh := (hcount.lintegral_prod_right' (ν := volume)).comp (measurable_subtype_coe : Measurable (fun c : CoefficientSphere ι => c.val))
    have he (c : CoefficientSphere ι) := coefficientSphereArea_frame m hm U hU R c
    rw [orthogonalCoordinates_first_axis,hR] at he
    change Measurable (fun c : CoefficientSphere ι => ∫⁻ y, coefficientLocalizedCount m R U (c.val,y)) at hh
    simpa only [← he] using hh
  by_cases hv : v = 0
  · subst v
    simp only [coefficientSphereArea,DisjointChartAtlas.directionalArea_zero]
    exact measurable_const
  · obtain ⟨u,hu,he⟩ := coordinate_euclidean_normalization v hv
    have hh := (hunit u hu).const_mul
      (ENNReal.ofReal |‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (n+1)))‖|)
    have hscale (c : CoefficientSphere ι) :=
      ((coefficientSphereAtlas m hm c).restrict U hU).directionalArea_smul
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (n+1)))‖ (WithLp.ofLp u)
    rw [he] at hscale
    simpa only [coefficientSphereArea,← hscale] using hh

/-- Uniform bound: monomial degree, region and radius are fixed before all
coefficient-sphere points and all directions. -/
theorem coefficientSphereArea_uniform_bound {ι : Type*} [Fintype ι] {n D : ℕ}
    (m : ι → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (hdegree : ∀ i, (m i).sum (fun _ e => e) ≤ D)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (c : CoefficientSphere ι) (v : Fin (n+1) → ℝ) :
    coefficientSphereArea m hm U hU c v ≤
      ENNReal.ofReal ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (n+1)))‖ *
        ((D : ℝ≥0∞) * volume (closedBall (0 : Fin n → ℝ) r)) := by
  apply (polynomial_bounded_area_norm_le (coefficientPolynomial m c.val)
    (coefficientPolynomial_nonzero m hm c.val (coefficientSphere_nonzero c))
    (coefficientSphereAtlas m hm c) U hU r hr hbound v).trans
  have hd : ((coefficientPolynomial m c.val).totalDegree : ℝ≥0∞) ≤ D := by
    exact_mod_cast coefficientPolynomial_degree m hdegree c.val
  gcongr

/-- Finiteness is proved from the actual polynomial geometry, not supplied. -/
theorem coefficientSphereArea_lt_top {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ x ∈ U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖ ≤ r)
    (c : CoefficientSphere ι) (v : Fin (n+1) → ℝ) :
    coefficientSphereArea m hm U hU c v < ∞ :=
  polynomial_bounded_area_lt_top (coefficientPolynomial m c.val)
    (coefficientPolynomial_nonzero m hm c.val (coefficientSphere_nonzero c))
    (coefficientSphereAtlas m hm c) U hU r hr hbound v

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coefficientSphereAtlas
#print axioms KakeyaTwoScale.coefficientSphereArea_frame
#print axioms KakeyaTwoScale.measurable_coefficientSphereArea
#print axioms KakeyaTwoScale.coefficientSphereArea_uniform_bound
#print axioms KakeyaTwoScale.coefficientSphereArea_lt_top
