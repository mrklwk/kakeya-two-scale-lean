module
public import KakeyaTwoScale.CrossingBoxConstants

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Tonelli separates the two path contributions and exposes the two unused
endpoint masses. Extended values are retained throughout. -/
theorem two_path_integral_separation {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) (κ : Measure Y) [SFinite κ]
    (F : X × Y → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, ∫⁻ y, ∫⁻ z, F (x,z)+F (y,z) ∂κ ∂ν ∂μ) =
      ν univ * (∫⁻ x, ∫⁻ z, F (x,z) ∂κ ∂μ) +
      μ univ * (∫⁻ y, ∫⁻ z, F (y,z) ∂κ ∂ν) := by
  let G (x : X) := ∫⁻ z, F (x,z) ∂κ
  have hG : Measurable G := hF.lintegral_prod_right'
  have hinner (x y : X) : (∫⁻ z, F (x,z)+F (y,z) ∂κ) = G x+G y :=
    lintegral_add_left (hF.comp (measurable_const.prodMk measurable_id)) _
  simp_rw [hinner]
  have hmid (x : X) : (∫⁻ y, G x+G y ∂ν) = G x*ν univ+∫⁻ y, G y ∂ν := by
    rw [lintegral_add_left measurable_const,lintegral_const]
  simp_rw [hmid]
  rw [lintegral_add_left (hG.mul_const _),lintegral_mul_const _ hG,lintegral_const]
  simp only [G,mul_comm]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.two_path_integral_separation
