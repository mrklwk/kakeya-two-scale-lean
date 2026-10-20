module
public import KakeyaTwoScale.ParametricFiberCounts
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Topology.Compactness.SigmaCompact

@[expose] public section

open Set MeasureTheory Metric
noncomputable section
namespace KakeyaTwoScale

/-- Compact exhaustion inside an open set, including the empty and whole spaces. -/
theorem open_monotone_compact_cover {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (U : Set X) (hU : IsOpen U) :
    ∃ K : ℕ → Set X, (∀ j, IsCompact (K j)) ∧ Monotone K ∧ ⋃ j, K j = U := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  refine ⟨fun j => Subtype.val '' compactCovering U j,
    fun j => (isCompact_compactCovering U j).image continuous_subtype_val,?_,?_⟩
  · intro i j hij
    exact image_mono (compactCovering_subset U hij)
  · rw [← image_iUnion,iUnion_compactCovering,image_univ,Subtype.range_coe]

/-- Counts in increasing measurable localizations converge exactly, including
infinite fibers. Counting measure is not assumed sigma-finite. -/
theorem localized_fiber_count_iUnion
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (f : E × ℝ → ℝ) (hf : Continuous f)
    (g : E × ℝ → X) (hg : Continuous g)
    (K : ℕ → Set X) (hK : ∀ j, MeasurableSet (K j)) (hmono : Monotone K) (y : E) :
    ({t : ℝ | f (y,t)=0 ∧ g (y,t) ∈ ⋃ j, K j} : Set ℝ).encard.toENNReal =
      ⨆ j, ({t : ℝ | f (y,t)=0 ∧ g (y,t) ∈ K j} : Set ℝ).encard.toENNReal := by
  let S (j : ℕ) : Set ℝ := {t | f (y,t)=0 ∧ g (y,t) ∈ K j}
  have hm (j : ℕ) : MeasurableSet (S j) :=
    (isClosed_eq (hf.comp (continuous_const.prodMk continuous_id)) continuous_const).measurableSet.inter
      ((hK j).preimage (hg.comp (continuous_const.prodMk continuous_id)).measurable)
  have hsm : Monotone S := fun i j hij t ht => ⟨ht.1,hmono hij ht.2⟩
  have hh := hsm.measure_iUnion (μ := (Measure.count : Measure ℝ))
  simp_rw [Measure.count_apply (MeasurableSet.iUnion hm),Measure.count_apply (hm _)] at hh
  have he : {t : ℝ | f (y,t)=0 ∧ g (y,t) ∈ ⋃ j, K j} = ⋃ j, S j := by
    ext t
    simp only [mem_ofPred_eq,mem_iUnion,S]
    aesop
  rw [he]
  exact hh

/-- Literal localized continuous-fiber counts are jointly Borel on finite-dimensional
parameter spaces for every open spatial localization. -/
theorem measurable_open_localized_fiber_count
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    (f : E × ℝ → ℝ) (hf : Continuous f)
    (g : E × ℝ → X) (hg : Continuous g) (U : Set X) (hU : IsOpen U) :
    Measurable (fun y => ({t : ℝ | f (y,t)=0 ∧ g (y,t) ∈ U} : Set ℝ).encard.toENNReal) := by
  obtain ⟨K,hK,hm,hcov⟩ := open_monotone_compact_cover U hU
  have hh := Measurable.iSup (fun j => measurable_closed_localized_fiber_count f hf g hg (K j) (hK j).isClosed)
  have he (y : E) := localized_fiber_count_iUnion f hf g hg K (fun j => (hK j).measurableSet) hm y
  rw [hcov] at he
  simpa only [← he] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.open_monotone_compact_cover
#print axioms KakeyaTwoScale.localized_fiber_count_iUnion
#print axioms KakeyaTwoScale.measurable_open_localized_fiber_count
