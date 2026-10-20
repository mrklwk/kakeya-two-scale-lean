module
public import KakeyaTwoScale.AtlasAmbientTransport
public import KakeyaTwoScale.OrthogonalCoordinateTransport

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Literal line intersections in an orthonormal frame, at unit speed. -/
def framedLineCount {n : ℕ} (Z : Set (Fin (n+1) → ℝ))
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (y : Fin n → ℝ) : ℝ≥0∞ :=
  ({t : ℝ | orthogonalCoordinates R (Fin.cons t y) ∈ Z} : Set ℝ).encard.toENNReal

theorem chartLineCount_inverse_frame {n : ℕ} (Z : Set (Fin (n+1) → ℝ))
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (y : Fin n → ℝ) :
    chartLineCount ((orthogonalCoordinates R).symm '' Z) y = framedLineCount Z R y := by
  unfold chartLineCount framedLineCount
  congr 2
  ext t
  constructor
  · rintro ⟨z,hz,he⟩
    change orthogonalCoordinates R (Fin.cons t y) ∈ Z
    rw [← he]
    simpa using hz
  · intro hz
    exact ⟨orthogonalCoordinates R (Fin.cons t y),hz,(orthogonalCoordinates R).symm_apply_apply _⟩

/-- Arbitrary-frame slicing for the SAME atlas functional. Ambient orthogonal
transport keeps its parameter pieces, so no chart-count or source-Jacobian loss occurs. -/
theorem DisjointChartAtlas.frame_identity {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z)
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    A.directionalArea (orthogonalCoordinates R (Pi.single 0 1)) = ∫⁻ y, framedLineCount Z R y := by
  let e := orthogonalCoordinates R
  have hd : ENNReal.ofReal |e.symm.toContinuousLinearMap.det| = 1 := by
    dsimp only [e]
    rw [orthogonalCoordinates_symm,orthogonalCoordinates_abs_det]
    norm_num
  have hh := A.directionalArea_ambientMap e.symm (e (Pi.single 0 1))
  rw [e.symm_apply_apply,hd,one_mul] at hh
  calc
    A.directionalArea (e (Pi.single 0 1)) = (A.ambientMap e.symm).directionalArea (Pi.single 0 1) := hh.symm
    _ = ∫⁻ y, chartLineCount (e.symm '' Z) y := (A.ambientMap e.symm).first_axis_identity
    _ = ∫⁻ y, framedLineCount Z R y := by
      apply lintegral_congr
      exact chartLineCount_inverse_frame Z R

theorem DisjointChartAtlas.aemeasurable_framedLineCount {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z)
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    AEMeasurable (framedLineCount Z R) volume := by
  have h := (A.ambientMap (orthogonalCoordinates R).symm).aemeasurable_lineCount
  have he : chartLineCount ((orthogonalCoordinates R).symm '' Z) = framedLineCount Z R :=
    funext (chartLineCount_inverse_frame Z R)
  rwa [he] at h

/-- The unit-direction identity uses a constructed orthogonal frame. -/
theorem DisjointChartAtlas.exists_unit_direction_identity {n : ℕ}
    {Z : Set (Fin (n+1) → ℝ)} (A : DisjointChartAtlas n Z)
    (u : EuclideanSpace ℝ (Fin (n+1))) (hu : ‖u‖ = 1) :
    ∃ R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)),
      R (EuclideanSpace.single 0 1) = u ∧
      A.directionalArea (WithLp.ofLp u) = ∫⁻ y, framedLineCount Z R y := by
  obtain ⟨R,hR⟩ := exists_axis_isometry (0 : Fin (n+1)) u hu
  refine ⟨R,hR,?_⟩
  have hh := A.frame_identity R
  rwa [orthogonalCoordinates_first_axis,hR] at hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.chartLineCount_inverse_frame
#print axioms KakeyaTwoScale.DisjointChartAtlas.frame_identity
#print axioms KakeyaTwoScale.DisjointChartAtlas.aemeasurable_framedLineCount
#print axioms KakeyaTwoScale.DisjointChartAtlas.exists_unit_direction_identity
