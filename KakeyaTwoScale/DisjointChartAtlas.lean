module
public import KakeyaTwoScale.CountablePolynomialCharts

@[expose] public section

open MvPolynomial MeasureTheory Set
open scoped ENNReal ContDiff Function
noncomputable section
namespace KakeyaTwoScale

/-- Borel localization of a chart needs only continuity on its open source. -/
theorem SmoothCoordinateChart.measurable_source_preimage {n : ℕ}
    (C : SmoothCoordinateChart n) {B : Set (Fin (n+1) → ℝ)} (hB : MeasurableSet B) :
    MeasurableSet (C.source ∩ C.map ⁻¹' B) := by
  classical
  have hm := C.smooth.continuousOn.measurable_piecewise
    (g := fun _ => (0 : Fin (n+1) → ℝ)) continuousOn_const C.isOpen_source.measurableSet
  have he : C.source ∩ C.map ⁻¹' B =
      C.source ∩ (C.source.piecewise C.map (fun _ => 0)) ⁻¹' B := by
    ext x
    by_cases hx : x ∈ C.source <;> simp [hx]
  rw [he]
  exact C.isOpen_source.measurableSet.inter (hm hB)

/-- A countable atlas whose actual image pieces form an exact disjoint measurable
partition. Parameter pieces may be lower-dimensional subsets of the chart sources. -/
structure DisjointChartAtlas (n : ℕ) (Z : Set (Fin (n+1) → ℝ)) where
  chart : ℕ → SmoothCoordinateChart n
  piece : ℕ → Set (Fin n → ℝ)
  measurable_piece : ∀ i, MeasurableSet (piece i)
  piece_subset : ∀ i, piece i ⊆ (chart i).source
  measurable_image : ∀ i, MeasurableSet ((chart i).map '' piece i)
  disjoint_image : Pairwise (Disjoint on fun i => (chart i).map '' piece i)
  cover : (⋃ i, (chart i).map '' piece i) = Z

/-- Construct disjoint image pieces, then pull those exact pieces back into the
charts. Extra points of containing hypersurfaces are removed by intersection with Z. -/
theorem exists_disjoint_chart_atlas {n : ℕ} (Z : Set (Fin (n+1) → ℝ))
    (hZ : MeasurableSet Z) (C : ℕ → SmoothCoordinateChart n)
    (hcover : Z ⊆ ⋃ i, (C i).map '' (C i).source) :
    Nonempty (DisjointChartAtlas n Z) := by
  classical
  let E := disjointed (fun i => Z ∩ (C i).map '' (C i).source)
  have hE (i : ℕ) : MeasurableSet (E i) :=
    MeasurableSet.disjointed (fun j => hZ.inter (C j).measurable_image) i
  have hsub (i : ℕ) : E i ⊆ (C i).map '' (C i).source :=
    (disjointed_le _ i).trans inter_subset_right
  let S (i : ℕ) := (C i).source ∩ (C i).map ⁻¹' E i
  have him (i : ℕ) : (C i).map '' S i = E i := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ht.2
    · intro hx
      obtain ⟨t,ht,rfl⟩ := hsub i hx
      exact ⟨t,⟨ht,hx⟩,rfl⟩
  refine ⟨⟨C,S,(fun i => (C i).measurable_source_preimage (hE i)),
    (fun _ => inter_subset_left),?_,?_,?_⟩⟩
  · intro i
    rw [him]
    exact hE i
  · intro i j hij
    change Disjoint ((C i).map '' S i) ((C j).map '' S j)
    rw [him,him]
    exact disjoint_disjointed _ hij
  · simp_rw [him]
    rw [show E = disjointed (fun i => Z ∩ (C i).map '' (C i).source) from rfl,
      iUnion_disjointed, ← inter_iUnion, inter_eq_self_of_subset_left hcover]

/-- An actual full polynomial atlas, with no supplied cover premise. -/
theorem polynomial_disjoint_chart_atlas {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (hP : P ≠ 0) : Nonempty (DisjointChartAtlas n {x | eval x P = 0}) := by
  obtain ⟨C,hC⟩ := polynomial_zero_countable_charts P hP
  exact exists_disjoint_chart_atlas _
    (isClosed_eq P.continuous_eval continuous_const).measurableSet C hC

end KakeyaTwoScale
#print axioms KakeyaTwoScale.SmoothCoordinateChart.measurable_source_preimage
#print axioms KakeyaTwoScale.exists_disjoint_chart_atlas
#print axioms KakeyaTwoScale.polynomial_disjoint_chart_atlas
