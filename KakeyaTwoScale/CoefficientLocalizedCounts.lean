module
public import KakeyaTwoScale.OpenLocalizedFiberCounts
public import KakeyaTwoScale.PolynomialCoefficients
public import KakeyaTwoScale.FramedHypersurfaceArea

@[expose] public section

open Set MeasureTheory MvPolynomial
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Polynomial evaluation is jointly continuous in finite coefficients and spatial coordinates. -/
theorem coefficientPolynomial_eval_joint_continuous {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin n →₀ ℕ)) :
    Continuous (fun z : EuclideanSpace ℝ ι × (Fin n → ℝ) => eval z.2 (coefficientPolynomial m z.1)) := by
  classical
  simp only [coefficientPolynomial,map_sum,MvPolynomial.eval_monomial,Finsupp.prod]
  fun_prop

/-- Exact localized geometric line count, including zero polynomials and infinite fibers. -/
def coefficientLocalizedCount {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin (n+1) →₀ ℕ))
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (U : Set (Fin (n+1) → ℝ)) (z : EuclideanSpace ℝ ι × (Fin n → ℝ)) : ℝ≥0∞ :=
  framedLineCount ({x | eval x (coefficientPolynomial m z.1)=0} ∩ U) R z.2

private theorem continuous_coefficient_frame {ι : Type*} [Fintype ι] {n : ℕ}
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    Continuous (fun z : (EuclideanSpace ℝ ι × (Fin n → ℝ)) × ℝ =>
      orthogonalCoordinates R (Fin.cons z.2 z.1.2)) := by
  apply (orthogonalCoordinates R).continuous.comp
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact continuous_snd
  · exact (continuous_apply i).comp (continuous_snd.comp continuous_fst)

/-- Coefficient/base joint measurability in an actual closed spatial region. -/
theorem measurable_coefficientLocalizedCount_closed {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin (n+1) →₀ ℕ))
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (U : Set (Fin (n+1) → ℝ)) (hU : IsClosed U) :
    Measurable (coefficientLocalizedCount m R U) := by
  have hg := continuous_coefficient_frame (ι := ι) R
  change Measurable (fun z : EuclideanSpace ℝ ι × (Fin n → ℝ) =>
    ({t : ℝ | eval (orthogonalCoordinates R (Fin.cons t z.2)) (coefficientPolynomial m z.1) = 0 ∧
       orthogonalCoordinates R (Fin.cons t z.2) ∈ U} : Set ℝ).encard.toENNReal)
  apply measurable_closed_localized_fiber_count
    (E := EuclideanSpace ℝ ι × (Fin n → ℝ)) (X := Fin (n+1) → ℝ)
    (fun z => eval (orthogonalCoordinates R (Fin.cons z.2 z.1.2)) (coefficientPolynomial m z.1.1)) _
    (fun z => orthogonalCoordinates R (Fin.cons z.2 z.1.2)) hg U hU
  classical
  simp only [coefficientPolynomial,map_sum,MvPolynomial.eval_monomial,Finsupp.prod]
  fun_prop

/-- Coefficient/base joint measurability in every open spatial region. -/
theorem measurable_coefficientLocalizedCount_open {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → (Fin (n+1) →₀ ℕ))
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (U : Set (Fin (n+1) → ℝ)) (hU : IsOpen U) :
    Measurable (coefficientLocalizedCount m R U) := by
  have hg := continuous_coefficient_frame (ι := ι) R
  change Measurable (fun z : EuclideanSpace ℝ ι × (Fin n → ℝ) =>
    ({t : ℝ | eval (orthogonalCoordinates R (Fin.cons t z.2)) (coefficientPolynomial m z.1) = 0 ∧
       orthogonalCoordinates R (Fin.cons t z.2) ∈ U} : Set ℝ).encard.toENNReal)
  apply measurable_open_localized_fiber_count
    (E := EuclideanSpace ℝ ι × (Fin n → ℝ)) (X := Fin (n+1) → ℝ)
    (fun z => eval (orthogonalCoordinates R (Fin.cons z.2 z.1.2)) (coefficientPolynomial m z.1.1)) _
    (fun z => orthogonalCoordinates R (Fin.cons z.2 z.1.2)) hg U hU
  classical
  simp only [coefficientPolynomial,map_sum,MvPolynomial.eval_monomial,Finsupp.prod]
  fun_prop

end KakeyaTwoScale
#print axioms KakeyaTwoScale.coefficientPolynomial_eval_joint_continuous
#print axioms KakeyaTwoScale.measurable_coefficientLocalizedCount_closed
#print axioms KakeyaTwoScale.measurable_coefficientLocalizedCount_open
