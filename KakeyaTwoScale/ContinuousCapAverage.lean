module
public import KakeyaTwoScale.SphericalCapNullity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped Topology
noncomputable section
namespace KakeyaTwoScale

/-- A bounded measurable function has a continuous moving-ball integral when
all distance levels at that radius are null. No continuity of the function is assumed. -/
theorem continuous_ball_integral_of_null_levels
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (F : X → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ q, ‖F q‖ ≤ C)
    (ε : ℝ) (hnull : ∀ p, μ {q | dist p q = ε} = 0) :
    Continuous (fun p => ∫ q in ball p ε, F q ∂μ) := by
  let G (p q : X) : ℝ := if dist p q < ε then F q else 0
  have he (p : X) : G p = (ball p ε).indicator F := by
    funext q
    by_cases h : dist p q < ε
    · rw [Set.indicator_of_mem (show q ∈ ball p ε by simpa only [mem_ball,dist_comm] using h)]
      simp [G,h]
    · rw [Set.indicator_of_notMem (show q ∉ ball p ε by simpa only [mem_ball,dist_comm] using h)]
      simp [G,h]
  have hh : Continuous (fun p => ∫ q, G p q ∂μ) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    apply continuousAt_of_dominated (bound := fun _ => C)
    · exact Eventually.of_forall (fun p => ((hF.indicator measurableSet_ball).aestronglyMeasurable.congr
        (Eventually.of_forall (fun q => congrFun (he p).symm q))))
    · exact Eventually.of_forall (fun p => Eventually.of_forall (fun q => by
        dsimp only [G]
        split_ifs
        · exact hbound q
        · simpa using hC))
    · exact integrable_const C
    · have hn : ∀ᵐ q ∂μ, dist p q ≠ ε := by
        rw [ae_iff]
        simpa only [not_not] using hnull p
      filter_upwards [hn] with q hq
      rcases lt_or_gt_of_ne hq with hl | hg
      · apply (continuousAt_const (y := F q)).congr_of_eventuallyEq
        filter_upwards [(isOpen_lt (continuous_id.dist continuous_const) continuous_const).mem_nhds hl] with z hz
        change dist z q < ε at hz
        simp [G,hz]
      · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [(isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hg] with z hz
        change ε < dist z q at hz
        simp [G,not_lt_of_gt hz]
  simpa only [he,integral_indicator measurableSet_ball] using hh

/-- Literal normalized spherical-cap average with intrinsic spherical measure. -/
def sphereCapAverage {d : ℕ}
    (ε : ℝ) (F : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) : ℝ :=
  (∫ q in ball p ε, F q ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) /
    (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.real (ball p ε)

/-- Source-aligned cap averaging is continuous in the coefficient center for
every bounded measurable raw function, for 0<epsilon<2. -/
theorem continuous_sphereCapAverage {d : ℕ}
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 2)
    (F : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ q, ‖F q‖ ≤ C) :
    Continuous (sphereCapAverage ε F) := by
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
  have hn := continuous_ball_integral_of_null_levels μ F hF C hC hbound ε
    (fun p => sphere_cap_distance_level_null p ε hε hε2)
  have hd := continuous_ball_integral_of_null_levels μ (fun _ => (1 : ℝ)) measurable_const
    1 zero_le_one (fun _ => by simp) ε (fun p => sphere_cap_distance_level_null p ε hε hε2)
  have he (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
      (∫ _q in ball p ε, (1 : ℝ) ∂μ) = μ.real (ball p ε) := by simp
  simp_rw [he] at hd
  apply hn.div hd
  intro p
  have hz : μ (ball p ε) ≠ 0 := isOpen_ball.measure_ne_zero μ (Metric.nonempty_ball.mpr hε)
  exact ENNReal.toReal_ne_zero.mpr ⟨hz,measure_ne_top μ _⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.continuous_ball_integral_of_null_levels
#print axioms KakeyaTwoScale.continuous_sphereCapAverage
