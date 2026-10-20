module
public import KakeyaTwoScale.WholeHypersurfaceArea
public import KakeyaTwoScale.ChartCofactorLinearity

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- The actual cofactor integrand is AE measurable on each parameter piece;
continuity of the derivative is used only on the chart's open source. -/
theorem DisjointChartAtlas.aemeasurable_cofactor {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z) (i : ℕ) (u : Fin (n+1) → ℝ) :
    AEMeasurable (fun x => ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart i).map x) u|)
      (volume.restrict (A.piece i)) := by
  have hc := (A.chart i).smooth.continuousOn_fderiv_of_isOpen (A.chart i).isOpen_source (by simp)
  have hh := ENNReal.continuous_ofReal.comp_continuousOn
    ((continuous_chartCofactor u).comp_continuousOn hc).abs
  exact (hh.mono (A.piece_subset i)).aemeasurable (A.measurable_piece i)

theorem DisjointChartAtlas.directionalArea_zero {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z) : A.directionalArea 0 = 0 := by
  simp [DisjointChartAtlas.directionalArea, chartCofactor_zero]

theorem DisjointChartAtlas.directionalArea_neg {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z) (u : Fin (n+1) → ℝ) :
    A.directionalArea (-u) = A.directionalArea u := by
  simp only [DisjointChartAtlas.directionalArea, chartCofactor_neg, abs_neg]

/-- Absolute homogeneity, including zero scalars and infinite area. -/
theorem DisjointChartAtlas.directionalArea_smul {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z) (c : ℝ) (u : Fin (n+1) → ℝ) :
    A.directionalArea (c • u) = ENNReal.ofReal |c| * A.directionalArea u := by
  simp only [DisjointChartAtlas.directionalArea, chartCofactor_smul, abs_mul,
    ENNReal.ofReal_mul (abs_nonneg c)]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.tsum_mul_left

/-- The whole chart functional is subadditive as an extended-valued function.
No finiteness or visibility conclusion is included in this theorem. -/
theorem DisjointChartAtlas.directionalArea_add_le {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z) (u v : Fin (n+1) → ℝ) :
    A.directionalArea (u+v) ≤ A.directionalArea u + A.directionalArea v := by
  have hi (i : ℕ) :
      (∫⁻ x in A.piece i, ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart i).map x) (u+v)|) ≤
      (∫⁻ x in A.piece i, ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart i).map x) u|) +
      (∫⁻ x in A.piece i, ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart i).map x) v|) := by
    rw [← lintegral_add_left' (A.aemeasurable_cofactor i u)]
    apply lintegral_mono
    intro x
    dsimp only
    rw [chartCofactor_add, ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_add_le _ _)
  unfold DisjointChartAtlas.directionalArea
  calc
    _ ≤ (∑' i, ((∫⁻ x in A.piece i, ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart i).map x) u|) +
        (∫⁻ x in A.piece i, ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart i).map x) v|))) :=
      ENNReal.tsum_le_tsum hi
    _ = _ := ENNReal.tsum_add

end KakeyaTwoScale
#print axioms KakeyaTwoScale.DisjointChartAtlas.aemeasurable_cofactor
#print axioms KakeyaTwoScale.DisjointChartAtlas.directionalArea_zero
#print axioms KakeyaTwoScale.DisjointChartAtlas.directionalArea_neg
#print axioms KakeyaTwoScale.DisjointChartAtlas.directionalArea_smul
#print axioms KakeyaTwoScale.DisjointChartAtlas.directionalArea_add_le
