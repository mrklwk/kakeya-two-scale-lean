module
public import KakeyaTwoScale.AtlasLocalization
public import KakeyaTwoScale.DisjointLineCounts

@[expose] public section

open MvPolynomial MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Directional chart area summed over exact disjoint image pieces. -/
def DisjointChartAtlas.directionalArea {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z) (u : Fin (n+1) → ℝ) : ℝ≥0∞ :=
  ∑' i, ∫⁻ x in A.piece i, ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart i).map x) u|

/-- A whole-set slicing identity. Disjoint IMAGE pieces ensure every geometric
intersection is counted once, independently of the number or overlap of containing charts. -/
theorem DisjointChartAtlas.first_axis_identity {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z) :
    A.directionalArea (Pi.single 0 1) = ∫⁻ y, chartLineCount Z y := by
  have hchart (i : ℕ) := chart_cofactor_integral_eq_crossings (A.chart i).map
    (A.chart i).source (A.chart i).isOpen_source ((A.chart i).smooth.of_le (by simp))
    (A.piece i) (A.measurable_piece i) (A.piece_subset i)
    ((A.chart i).injective.mono (A.piece_subset i))
  unfold DisjointChartAtlas.directionalArea
  calc
    (∑' i, ∫⁻ x in A.piece i,
        ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart i).map x) (Pi.single 0 1)|) =
        ∑' i, ∫⁻ y, chartLineCount ((A.chart i).map '' A.piece i) y :=
      tsum_congr (fun i => (hchart i).2)
    _ = ∫⁻ y, ∑' i, chartLineCount ((A.chart i).map '' A.piece i) y :=
      (lintegral_tsum (fun i => (hchart i).1)).symm
    _ = ∫⁻ y, chartLineCount Z y := by
      apply lintegral_congr
      intro y
      rw [← chartLineCount_iUnion _ A.measurable_image A.disjoint_image, A.cover]

/-- The exact whole-set line count is AE measurable, including Borel localizations
and infinite exceptional fibers. -/
theorem DisjointChartAtlas.aemeasurable_lineCount {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z) : AEMeasurable (chartLineCount Z) volume := by
  have hm (i : ℕ) := (chart_cofactor_integral_eq_crossings (A.chart i).map
    (A.chart i).source (A.chart i).isOpen_source ((A.chart i).smooth.of_le (by simp))
    (A.piece i) (A.measurable_piece i) (A.piece_subset i)
    ((A.chart i).injective.mono (A.piece_subset i))).1
  have he : chartLineCount Z = fun y => ∑' i, chartLineCount ((A.chart i).map '' A.piece i) y := by
    funext y
    have hh := chartLineCount_iUnion _ A.measurable_image A.disjoint_image y
    rw [A.cover] at hh
    exact hh
  rw [he]
  exact AEMeasurable.tsum hm

/-- First-axis area is independent of the actual atlas used to represent Z. -/
theorem DisjointChartAtlas.first_axis_independent {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A B : DisjointChartAtlas n Z) :
    A.directionalArea (Pi.single 0 1) = B.directionalArea (Pi.single 0 1) := by
  rw [A.first_axis_identity, B.first_axis_identity]

/-- The same whole-set identity after arbitrary Borel localization. -/
theorem DisjointChartAtlas.localized_first_axis_identity {n : ℕ}
    {Z : Set (Fin (n+1) → ℝ)} (A : DisjointChartAtlas n Z)
    (B : Set (Fin (n+1) → ℝ)) (hB : MeasurableSet B) :
    (A.restrict B hB).directionalArea (Pi.single 0 1) = ∫⁻ y, chartLineCount (Z ∩ B) y :=
  (A.restrict B hB).first_axis_identity

/-- Localizing an entire polynomial zero set to a transverse cylinder preserves
exactly the original root count on its base and gives zero outside the base. -/
theorem polynomial_transverse_cylinder_count {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (D : Set (Fin n → ℝ)) (y : Fin n → ℝ) :
    chartLineCount ({x | eval x P = 0} ∩ (transverseProjection n) ⁻¹' D) y =
      D.indicator (coordinateCrossingCount P) y := by
  classical
  by_cases hy : y ∈ D
  · rw [Set.indicator_of_mem hy]
    unfold chartLineCount coordinateCrossingCount coordinateZeroFiber
    congr 2
    ext t
    exact ⟨fun h => h.1, fun h => ⟨h,hy⟩⟩
  · rw [Set.indicator_of_notMem hy]
    have he : {t : ℝ | Fin.cons t y ∈
        {x | eval x P = 0} ∩ (transverseProjection n) ⁻¹' D} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hy ht.2
    unfold chartLineCount
    rw [he]
    simp

/-- Actual whole-hypersurface first-axis budget. The degree is paid once, not
once per chart. All singular and repeated-factor zeros remain in the atlas. -/
theorem polynomial_atlas_first_axis_budget {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P ≠ 0)
    (A : DisjointChartAtlas n {x | eval x P = 0})
    (D : Set (Fin n → ℝ)) (hD : MeasurableSet D) :
    (A.restrict ((transverseProjection n) ⁻¹' D)
      (hD.preimage (transverseProjection n).measurable)).directionalArea (Pi.single 0 1) ≤
      (P.totalDegree : ℝ≥0∞) * volume D := by
  rw [DisjointChartAtlas.localized_first_axis_identity]
  simp_rw [polynomial_transverse_cylinder_count]
  rw [lintegral_indicator hD]
  exact coordinate_crossing_integral_le P hP D

/-- Construct the actual full atlas before all base sets, then derive the uniform
whole-hypersurface slicing budget. No atlas or area estimate is supplied as a premise. -/
theorem exists_polynomial_whole_area_budget {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℝ) (hP : P ≠ 0) :
    ∃ A : DisjointChartAtlas n {x | eval x P = 0},
      ∀ (D : Set (Fin n → ℝ)) (hD : MeasurableSet D),
      (A.restrict ((transverseProjection n) ⁻¹' D)
        (hD.preimage (transverseProjection n).measurable)).directionalArea (Pi.single 0 1) ≤
        (P.totalDegree : ℝ≥0∞) * volume D := by
  obtain ⟨A⟩ := polynomial_disjoint_chart_atlas P hP
  exact ⟨A,fun D hD => polynomial_atlas_first_axis_budget P hP A D hD⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.DisjointChartAtlas.first_axis_identity
#print axioms KakeyaTwoScale.DisjointChartAtlas.localized_first_axis_identity
#print axioms KakeyaTwoScale.polynomial_transverse_cylinder_count
#print axioms KakeyaTwoScale.polynomial_atlas_first_axis_budget
#print axioms KakeyaTwoScale.exists_polynomial_whole_area_budget
#print axioms KakeyaTwoScale.DisjointChartAtlas.aemeasurable_lineCount
#print axioms KakeyaTwoScale.DisjointChartAtlas.first_axis_independent
