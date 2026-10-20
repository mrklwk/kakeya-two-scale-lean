module
public import KakeyaTwoScale.PolynomialEllipsoidBisection

@[expose] public section

open Set MeasureTheory
open scoped ENNReal Function
noncomputable section
namespace KakeyaTwoScale

/-- Monotonicity for literal restrictions of the same actual atlas. -/
theorem DisjointChartAtlas.restrict_area_mono {n : ℕ} {Z : Set (Fin (n+1) → ℝ)}
    (A : DisjointChartAtlas n Z) (E U : Set (Fin (n+1) → ℝ))
    (hE : MeasurableSet E) (hU : MeasurableSet U) (hEU : E ⊆ U) (v : Fin (n+1) → ℝ) :
    (A.restrict E hE).directionalArea v ≤ (A.restrict U hU).directionalArea v := by
  apply ENNReal.tsum_le_tsum
  intro k
  change (∫⁻ x in A.piece k ∩ (A.chart k).map ⁻¹' E,
    ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart k).map x) v|) ≤
    ∫⁻ x in A.piece k ∩ (A.chart k).map ⁻¹' U,
    ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart k).map x) v|
  exact lintegral_mono' (Measure.restrict_mono
    (show A.piece k ∩ (A.chart k).map ⁻¹' E ⊆ A.piece k ∩ (A.chart k).map ⁻¹' U from
      fun _ hx => ⟨hx.1,hEU hx.2⟩) le_rfl) le_rfl

/-- Disjoint spatial localizations add exactly, including infinite area. -/
theorem DisjointChartAtlas.sum_restrict_area {ι : Type*} [Fintype ι]
    {n : ℕ} {Z : Set (Fin (n+1) → ℝ)} (A : DisjointChartAtlas n Z)
    (E : ι → Set (Fin (n+1) → ℝ)) (hE : ∀ i, MeasurableSet (E i))
    (hd : Pairwise (Disjoint on E)) (v : Fin (n+1) → ℝ) :
    (∑ i, (A.restrict (E i) (hE i)).directionalArea v) =
      (A.restrict (⋃ i, E i) (MeasurableSet.iUnion hE)).directionalArea v := by
  classical
  have hk (k : ℕ) :
      (∫⁻ x in A.piece k ∩ (A.chart k).map ⁻¹' (⋃ i, E i),
        ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart k).map x) v|) =
      ∑ i, ∫⁻ x in A.piece k ∩ (A.chart k).map ⁻¹' E i,
        ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart k).map x) v| := by
    rw [preimage_iUnion,inter_iUnion,lintegral_iUnion]
    · exact tsum_fintype _
    · intro i
      exact (A.restrict (E i) (hE i)).measurable_piece k
    · intro i j hij
      exact ((hd hij).preimage (A.chart k).map).mono inter_subset_right inter_subset_right
  change (∑ i, ∑' k, ∫⁻ x in A.piece k ∩ (A.chart k).map ⁻¹' E i,
    ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart k).map x) v|) = _
  calc
    _ = ∑' i, ∑' k, ∫⁻ x in A.piece k ∩ (A.chart k).map ⁻¹' E i,
        ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart k).map x) v| := (tsum_fintype _).symm
    _ = ∑' k, ∑' i, ∫⁻ x in A.piece k ∩ (A.chart k).map ⁻¹' E i,
        ENNReal.ofReal |chartCofactor (fderiv ℝ (A.chart k).map x) v| := ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro k
      exact (tsum_fintype _).trans (hk k).symm

/-- Each direction is charged once to the containing region. -/
theorem DisjointChartAtlas.sum_restrict_area_le {ι : Type*} [Fintype ι]
    {n : ℕ} {Z : Set (Fin (n+1) → ℝ)} (A : DisjointChartAtlas n Z)
    (E : ι → Set (Fin (n+1) → ℝ)) (hE : ∀ i, MeasurableSet (E i))
    (hd : Pairwise (Disjoint on E)) (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U)
    (hEU : ∀ i, E i ⊆ U) (v : Fin (n+1) → ℝ) :
    (∑ i, (A.restrict (E i) (hE i)).directionalArea v) ≤ (A.restrict U hU).directionalArea v := by
  rw [A.sum_restrict_area E hE hd v]
  exact A.restrict_area_mono _ _ _ _ (iUnion_subset hEU) v

end KakeyaTwoScale
#print axioms KakeyaTwoScale.DisjointChartAtlas.restrict_area_mono
#print axioms KakeyaTwoScale.DisjointChartAtlas.sum_restrict_area
#print axioms KakeyaTwoScale.DisjointChartAtlas.sum_restrict_area_le
