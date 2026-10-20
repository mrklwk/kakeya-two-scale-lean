module
public import KakeyaTwoScale.ContinuousCapAverage
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

open Set MeasureTheory Metric
open scoped Pointwise
noncomputable section
namespace KakeyaTwoScale

/-- The actual antipodal homeomorphism of the intrinsic coefficient sphere. -/
def metricSphereAntipode (d : ℕ) :
    sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 where
  toFun p := ⟨-p.val,by simpa only [mem_sphere_zero_iff_norm,norm_neg] using p.property⟩
  invFun p := ⟨-p.val,by simpa only [mem_sphere_zero_iff_norm,norm_neg] using p.property⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by apply Subtype.ext; simp
  continuous_toFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _

theorem metricSphereAntipode_ball {d : ℕ}
    (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) (ε : ℝ) :
    metricSphereAntipode d ⁻¹' ball (metricSphereAntipode d p) ε = ball p ε := by
  ext q
  change dist (-q.val) (-p.val) < ε ↔ dist q.val p.val < ε
  rw [dist_neg_neg]

/-- Intrinsic spherical measure is antipodally invariant, proved from its
radial-cone definition and ambient Haar negation invariance. -/
theorem metricSphereAntipode_measurePreserving (d : ℕ) :
    MeasurePreserving (metricSphereAntipode d)
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  let e := metricSphereAntipode d
  have hee (q) : e (e q) = q := by
    apply Subtype.ext
    exact neg_neg q.val
  have hcone (S : Set (sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) :
      Ioo (0:ℝ) 1 • (Subtype.val '' (e ⁻¹' S)) =
        Neg.neg ⁻¹' (Ioo (0:ℝ) 1 • (Subtype.val '' S)) := by
    ext x
    constructor
    · rintro ⟨t,ht,z,⟨q,hq,rfl⟩,rfl⟩
      exact ⟨t,ht,-q.val,⟨e q,hq,rfl⟩,smul_neg t q.val⟩
    · rintro ⟨t,ht,z,⟨q,hq,rfl⟩,he⟩
      refine ⟨t,ht,-q.val,⟨e q,?_,rfl⟩,?_⟩
      · change e (e q) ∈ S
        rwa [hee]
      · change t • (-q.val) = x
        change t • q.val = -x at he
        simpa only [smul_neg,neg_neg] using congrArg Neg.neg he
  refine ⟨e.continuous.measurable,?_⟩
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply e.continuous.measurable hS,
    Measure.toSphere_apply' _ (e.continuous.measurable hS),Measure.toSphere_apply' _ hS,
    hcone,Measure.measure_preimage_neg]

/-- Cap averaging preserves an actual even function for every radius. This
uses the same intrinsic measure and exact cap transport, not an assumed symmetry. -/
theorem sphereCapAverage_antipodal {d : ℕ}
    (F : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ)
    (hF : ∀ q, F (metricSphereAntipode d q)=F q) (ε : ℝ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    sphereCapAverage ε F (metricSphereAntipode d p) = sphereCapAverage ε F p := by
  let e := metricSphereAntipode d
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
  have hi (q) : (ball (e p) ε).indicator F (e q) = (ball p ε).indicator F q := by
    have hq : e q ∈ ball (e p) ε ↔ q ∈ ball p ε := by
      change q ∈ e ⁻¹' ball (e p) ε ↔ _
      rw [metricSphereAntipode_ball]
    by_cases h : q ∈ ball p ε
    · simp only [indicator_of_mem h,indicator_of_mem (hq.mpr h)]
      exact hF q
    · simp only [indicator_of_notMem h,indicator_of_notMem (not_iff_not.mpr hq |>.mpr h)]
  have hint := (metricSphereAntipode_measurePreserving d).integral_comp
    e.measurableEmbedding ((ball (e p) ε).indicator F)
  change (∫ q, (ball (e p) ε).indicator F (e q) ∂μ) =
    ∫ q, (ball (e p) ε).indicator F q ∂μ at hint
  simp_rw [hi] at hint
  rw [integral_indicator measurableSet_ball,integral_indicator measurableSet_ball] at hint
  have hm := (metricSphereAntipode_measurePreserving d).measure_preimage
    (s := ball (e p) ε) measurableSet_ball.nullMeasurableSet
  rw [metricSphereAntipode_ball] at hm
  change (∫ q in ball (e p) ε, F q ∂μ) / (μ (ball (e p) ε)).toReal =
    (∫ q in ball p ε, F q ∂μ) / (μ (ball p ε)).toReal
  rw [← hint,← hm]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.metricSphereAntipode_ball
#print axioms KakeyaTwoScale.metricSphereAntipode_measurePreserving
#print axioms KakeyaTwoScale.sphereCapAverage_antipodal
