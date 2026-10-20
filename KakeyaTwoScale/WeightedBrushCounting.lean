module
public import KakeyaTwoScale.BrushGeometry
public import KakeyaTwoScale.MeasureSelection

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical
variable {X J : Type*} [MeasurableSpace X]

def weightedOverlap (family : Finset J) (sets : J → Set X) (w : J → ℝ) (x : X) : ℝ :=
  ∑ j ∈ family, (sets j).indicator (fun _ => w j) x

theorem measurable_weightedOverlap (family : Finset J) (sets : J → Set X) (w : J → ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (sets j)) :
    Measurable (weightedOverlap family sets w) :=
  Finset.measurable_sum _ fun j hj => measurable_const.indicator (hm j hj)

theorem integrable_weightedOverlap (μ : Measure X) [IsFiniteMeasure μ]
    (family : Finset J) (sets : J → Set X) (w : J → ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (sets j)) :
    Integrable (weightedOverlap family sets w) μ :=
  integrable_finsetSum _ fun j hj => (integrable_const _).indicator (hm j hj)

theorem integral_weightedOverlap (μ : Measure X) [IsFiniteMeasure μ]
    (family : Finset J) (sets : J → Set X) (w : J → ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (sets j)) :
    (∫ x, weightedOverlap family sets w x ∂μ) = ∑ j ∈ family, w j * μ.real (sets j) := by
  unfold weightedOverlap
  rw [integral_finsetSum _ (fun j hj => (integrable_const _).indicator (hm j hj))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_indicator_const _ (hm j hj)]
  simp [smul_eq_mul, mul_comm]

/-- Bounded weighted multiplicity converts counted volume to union volume. -/
theorem weighted_union_volume (μ : Measure X) [IsFiniteMeasure μ]
    (family : Finset J) (sets : J → Set X) (w : J → ℝ) (B : ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (sets j))
    (hB : ∀ x, weightedOverlap family sets w x ≤ B) :
    (∑ j ∈ family, w j * μ.real (sets j)) ≤ B * μ.real (⋃ j ∈ family, sets j) := by
  have hU : MeasurableSet (⋃ j ∈ family, sets j) := Finset.measurableSet_biUnion _ hm
  rw [← integral_weightedOverlap μ family sets w hm]
  calc
    _ ≤ ∫ x, (⋃ j ∈ family, sets j).indicator (fun _ => B) x ∂μ := by
      apply integral_mono (integrable_weightedOverlap μ family sets w hm)
        ((integrable_const B).indicator hU)
      intro x
      by_cases hx : x ∈ ⋃ j ∈ family, sets j
      · simpa [Set.indicator_of_mem hx] using hB x
      · have hn : ∀ j ∈ family, x ∉ sets j := by simpa using hx
        rw [Set.indicator_of_notMem hx]
        have hz : weightedOverlap family sets w x = 0 :=
          Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem (hn j hj) _
        rw [hz]
    _ = _ := by rw [integral_indicator_const B hU]; simp [smul_eq_mul, mul_comm]

/-- The first brush incidence step, with an explicit overlap constant B.
No angular separation or overlap assertion is hidden in the measure argument. -/
theorem brush_counted_volume_lower (μ : Measure X) [IsFiniteMeasure μ]
    (family : Finset J) (pieces : J → Set X) (w : J → ℝ) (v B : ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (pieces j))
    (hw : ∀ j ∈ family, 0 ≤ w j)
    (hv : ∀ j ∈ family, v ≤ μ.real (pieces j))
    (hB : ∀ x, weightedOverlap family pieces w x ≤ B) :
    v * (∑ j ∈ family, w j) ≤ B * μ.real (⋃ j ∈ family, pieces j) := by
  calc
    _ = ∑ j ∈ family, w j*v := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ ∑ j ∈ family, w j*μ.real (pieces j) :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hv j hj) (hw j hj)
    _ ≤ _ := weighted_union_volume μ family pieces w B hm hB

/-- High overlap on a measurable union forces an integral on every containing
plane neighborhood. F is nonnegative on that neighborhood. -/
theorem high_overlap_plane_integral (μ : Measure X) [IsFiniteMeasure μ]
    (F : X → ℝ) (hF : Integrable F μ) (hn : ∀ x, 0 ≤ F x)
    (U H : Set X) (hU : MeasurableSet U) (hH : MeasurableSet H)
    (hsub : U ⊆ H) (M : ℝ) (hM : ∀ x ∈ U, M ≤ F x) :
    M * μ.real U ≤ ∫ x in H, F x ∂μ := by
  have hi : Integrable (U.indicator (fun _ => M)) μ := (integrable_const M).indicator hU
  calc
    _ = ∫ x, U.indicator (fun _ => M) x ∂μ := by
      rw [integral_indicator_const M hU]; simp [smul_eq_mul, mul_comm]
    _ ≤ ∫ x, H.indicator F x ∂μ := by
      apply integral_mono hi (hF.indicator hH)
      intro x
      by_cases hx : x ∈ U
      · simpa [Set.indicator_of_mem hx, Set.indicator_of_mem (hsub hx)] using hM x hx
      · by_cases hh : x ∈ H
        · simpa [Set.indicator_of_notMem hx, Set.indicator_of_mem hh] using hn x
        · simp [hx, hh]
    _ = _ := integral_indicator hH

omit [MeasurableSpace X] in
theorem weightedOverlap_nonneg (family : Finset J) (sets : J → Set X) (w : J → ℝ)
    (hw : ∀ j ∈ family, 0 ≤ w j) (x : X) : 0 ≤ weightedOverlap family sets w x := by
  apply Finset.sum_nonneg
  intro j hj
  exact Set.indicator_nonneg (fun _ _ => hw j hj) x

/-- Each incident tube contributes at most its full-volume cap to the plane
integral. Incidence is literal nonempty intersection, not a substituted count. -/
theorem plane_integral_le_incident_weight (μ : Measure X) [IsFiniteMeasure μ]
    (family : Finset J) (tubes : J → Set X) (w : J → ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (tubes j))
    (hw : ∀ j ∈ family, 0 ≤ w j) (H : Set X) (V : ℝ)
    (hV : ∀ j ∈ family, μ.real (tubes j) ≤ V) :
    (∫ x in H, weightedOverlap family tubes w x ∂μ) ≤
      V * ∑ j ∈ family.filter (fun j => (tubes j ∩ H).Nonempty), w j := by
  rw [integral_weightedOverlap (μ.restrict H) family tubes w hm]
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro j hj
  have he : (μ.restrict H).real (tubes j) = μ.real (tubes j ∩ H) := by
    rw [Measure.real, Measure.restrict_apply (hm j hj)]; rfl
  rw [he]
  split_ifs with hn
  · have hv : μ.real (tubes j ∩ H) ≤ V :=
      (measureReal_mono Set.inter_subset_left).trans (hV j hj)
    nlinarith [mul_le_mul_of_nonneg_left hv (hw j hj)]
  · rw [Set.not_nonempty_iff_eq_empty.mp hn]
    simp

/-- The brush's plane-incidence inequality, including every multiplicity and
volume constant. Geometric localization must supply hB and the pieces. -/
theorem brush_plane_incidence (μ : Measure X) [IsFiniteMeasure μ]
    (family brush : Finset J) (tubes pieces : J → Set X) (w : J → ℝ)
    (H : Set X) (hH : MeasurableSet H) (v B M V : ℝ)
    (hm : ∀ j ∈ family, MeasurableSet (tubes j))
    (hpm : ∀ j ∈ brush, MeasurableSet (pieces j))
    (hw : ∀ j ∈ family, 0 ≤ w j) (hpw : ∀ j ∈ brush, 0 ≤ w j)
    (hv : ∀ j ∈ brush, v ≤ μ.real (pieces j))
    (hB0 : 0 ≤ B) (hM0 : 0 ≤ M)
    (hB : ∀ x, weightedOverlap brush pieces w x ≤ B)
    (hsub : ∀ j ∈ brush, pieces j ⊆ H)
    (hhigh : ∀ j ∈ brush, ∀ x ∈ pieces j, M ≤ weightedOverlap family tubes w x)
    (hV : ∀ j ∈ family, μ.real (tubes j) ≤ V) :
    M*v*(∑ j ∈ brush, w j) ≤
      B*V*(∑ j ∈ family.filter (fun j => (tubes j ∩ H).Nonempty), w j) := by
  let U := ⋃ j ∈ brush, pieces j
  have hU : MeasurableSet U := Finset.measurableSet_biUnion _ hpm
  have hUH : U ⊆ H := by
    intro x hx
    obtain ⟨j,hj,hx⟩ := Set.mem_iUnion₂.mp hx
    exact hsub j hj hx
  have hHU : ∀ x ∈ U, M ≤ weightedOverlap family tubes w x := by
    intro x hx
    obtain ⟨j,hj,hx⟩ := Set.mem_iUnion₂.mp hx
    exact hhigh j hj x hx
  have harea := brush_counted_volume_lower μ brush pieces w v B hpm hpw hv hB
  have hi := high_overlap_plane_integral μ (weightedOverlap family tubes w)
    (integrable_weightedOverlap μ family tubes w hm) (weightedOverlap_nonneg family tubes w hw)
    U H hU hH hUH M hHU
  have hu := plane_integral_le_incident_weight μ family tubes w hm hw H V hV
  calc
    _ = M*(v*∑ j ∈ brush, w j) := by ring
    _ ≤ M*(B*μ.real U) := mul_le_mul_of_nonneg_left harea hM0
    _ = B*(M*μ.real U) := by ring
    _ ≤ B*(∫ x in H, weightedOverlap family tubes w x ∂μ) :=
      mul_le_mul_of_nonneg_left hi hB0
    _ ≤ B*(V*∑ j ∈ family.filter (fun j => (tubes j ∩ H).Nonempty), w j) :=
      mul_le_mul_of_nonneg_left hu hB0
    _ = _ := by ring

/-- Uniform two-height localization yields a weighted overlap bound from a
precisely stated slope-neighborhood weight cap. The cap is still geometric input. -/
theorem weighted_two_height_overlap {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (family : Finset J) (b v : J → Y) (w : J → ℝ)
    (s t r h B : ℝ) (p x : Y) (hh : 0 < h) (hsep : h ≤ |t-s|)
    (hw : ∀ j ∈ family, 0 ≤ w j)
    (hs : ∀ j ∈ family, dist (segmentPoint (b j) (v j) s) p ≤ r)
    (hcap : ∀ v₀ : Y, (∑ j ∈ family.filter (fun j => dist (v j) v₀ ≤ 4*r/h), w j) ≤ B)
    (hB : 0 ≤ B) :
    (∑ j ∈ family.filter (fun j => dist (segmentPoint (b j) (v j) t) x ≤ r), w j) ≤ B := by
  let S := family.filter (fun j => dist (segmentPoint (b j) (v j) t) x ≤ r)
  by_cases hne : S.Nonempty
  · obtain ⟨j₀,hj₀⟩ := hne
    have hj₀' := Finset.mem_filter.mp hj₀
    have hsub : S ⊆ family.filter (fun j => dist (v j) (v j₀) ≤ 4*r/h) := by
      intro j hj
      obtain ⟨hj,hjt⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_filter.mpr ⟨hj,?_⟩
      have hdist (z z' c : Y) (hz : dist z c ≤ r) (hz' : dist z' c ≤ r) : dist z z' ≤ 2*r := by
        have hh := dist_triangle z c z'
        rw [dist_comm c z'] at hh
        linarith
      have hloc := slope_dist_of_two_encounters (b j) (v j) (b j₀) (v j₀)
        s t (2*r) h hh hsep (hdist _ _ p (hs j hj) (hs j₀ hj₀'.1))
        (hdist _ _ x hjt hj₀'.2)
      convert hloc using 1; ring
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun j hj _ => hw j (Finset.mem_filter.mp hj).1)).trans (hcap (v j₀))
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change (∑ j ∈ S, w j) ≤ B
    simpa [he] using hB
end KakeyaTwoScale
#print axioms KakeyaTwoScale.weighted_union_volume
#print axioms KakeyaTwoScale.brush_counted_volume_lower
#print axioms KakeyaTwoScale.high_overlap_plane_integral
#print axioms KakeyaTwoScale.weighted_two_height_overlap

#print axioms KakeyaTwoScale.brush_plane_incidence
