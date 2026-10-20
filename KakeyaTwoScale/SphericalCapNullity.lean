module
public import KakeyaTwoScale.SphericalCapPolynomial

@[expose] public section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace Pointwise
noncomputable section
namespace KakeyaTwoScale

/-- A nondegenerate latitude has zero intrinsic spherical measure. -/
theorem sphere_latitude_measure_zero {d : ℕ}
    (p : EuclideanSpace ℝ (Fin d)) (hp : ‖p‖ = 1) (a : ℝ) (ha : |a| < 1) :
    (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
      {q : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 | ⟪p,q.val⟫ = a} = 0 := by
  have hm : MeasurableSet {q : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 | ⟪p,q.val⟫ = a} :=
    (isClosed_eq (continuous_const.inner continuous_subtype_val) continuous_const).measurableSet
  rw [Measure.toSphere_apply' _ hm]
  have hz : (volume : Measure (EuclideanSpace ℝ (Fin d))) (Ioo (0 : ℝ) 1 •
      ((fun q : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 => q.val) '' {q : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 | ⟪p,q.val⟫ = a})) = 0 := by
    apply measure_mono_null _ (capCone_zero_volume p hp a ha)
    rintro x ⟨t,ht,z,⟨q,hq,rfl⟩,rfl⟩
    change ⟪p,t • q.val⟫^2 - a^2 * ‖t • q.val‖^2 = 0
    have hn : ‖q.val‖ = 1 := mem_sphere_zero_iff_norm.mp q.property
    change ⟪p,q.val⟫ = a at hq
    rw [inner_smul_right,hq,norm_smul,hn,mul_one,Real.norm_eq_abs]
    nlinarith [sq_abs t]
  rw [hz,mul_zero]

/-- Every positive cap radius below the diameter has a null distance level.
This includes the two-point sphere; no coefficient dimension lower bound is needed. -/
theorem sphere_cap_distance_level_null {d : ℕ}
    (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1)
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere {q | dist p q = ε} = 0 := by
  have hp : ‖p.val‖ = 1 := mem_sphere_zero_iff_norm.mp p.property
  have ha : |1 - ε^2/2| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith
  apply measure_mono_null _ (sphere_latitude_measure_zero p.val hp (1 - ε^2/2) ha)
  intro q hq
  change ⟪p.val,q.val⟫ = 1 - ε^2/2
  have hn : ‖q.val‖ = 1 := mem_sphere_zero_iff_norm.mp q.property
  have hd : ‖p.val-q.val‖ = ε := by
    change dist p.val q.val = ε at hq
    rwa [dist_eq_norm] at hq
  have hh := norm_sub_sq_real p.val q.val
  rw [hp,hn,hd] at hh
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.sphere_latitude_measure_zero
#print axioms KakeyaTwoScale.sphere_cap_distance_level_null
