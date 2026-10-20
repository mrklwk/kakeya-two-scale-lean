module
public import KakeyaTwoScale.ClosedFiberCountMeasurable
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

open Set MeasureTheory Metric
noncomputable section
namespace KakeyaTwoScale

/-- Exact continuous-fiber counts with any finite-dimensional real parameter space. -/
theorem measurable_finiteDimensional_fiber_count
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (f : E × ℝ → ℝ) (hf : Continuous f) :
    Measurable (fun y => ({t : ℝ | f (y,t) = 0} : Set ℝ).encard.toENNReal) := by
  let e := (Module.finBasis ℝ E).equivFunL
  have h := measurable_continuous_fiber_count
    (fun z => f (e.symm z.1,z.2))
    (hf.comp ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd))
  have hh := h.comp e.continuous.measurable
  change Measurable (fun y => ({t : ℝ | f (e.symm (e y),t) = 0} : Set ℝ).encard.toENNReal) at hh
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh

/-- Closed localization is encoded by squared distance. Empty localization is
handled separately, since real infDist to the empty set is zero. -/
theorem measurable_closed_localized_fiber_count
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [PseudoMetricSpace X]
    (f : E × ℝ → ℝ) (hf : Continuous f)
    (g : E × ℝ → X) (hg : Continuous g) (K : Set X) (hK : IsClosed K) :
    Measurable (fun y => ({t : ℝ | f (y,t)=0 ∧ g (y,t) ∈ K} : Set ℝ).encard.toENNReal) := by
  by_cases hne : K.Nonempty
  · have hh := measurable_finiteDimensional_fiber_count
      (fun z => (f z)^2 + (infDist (g z) K)^2)
      ((hf.pow 2).add (((continuous_infDist_pt (s := K)).comp hg).pow 2))
    have he (y : E) : {t : ℝ | (f (y,t))^2 + (infDist (g (y,t)) K)^2 = 0} =
        {t : ℝ | f (y,t)=0 ∧ g (y,t) ∈ K} := by
      ext t
      simp only [mem_ofPred_eq,hK.mem_iff_infDist_zero hne]
      constructor
      · intro hz
        have h1 := sq_nonneg (f (y,t))
        have h2 := sq_nonneg (infDist (g (y,t)) K)
        constructor <;> nlinarith
      · rintro ⟨h1,h2⟩
        simp [h1,h2]
    simpa only [he] using hh
  · have he : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [he,mem_empty_iff_false,and_false,ofPred_false,encard_empty,ENat.toENNReal_zero]
    exact measurable_const

end KakeyaTwoScale
#print axioms KakeyaTwoScale.measurable_finiteDimensional_fiber_count
#print axioms KakeyaTwoScale.measurable_closed_localized_fiber_count
