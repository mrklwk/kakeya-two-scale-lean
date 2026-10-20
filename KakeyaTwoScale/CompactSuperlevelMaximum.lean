module
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.LocalExtr

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- A point strictly above a compact superlevel threshold has an ambient local
maximum in the same superlevel component. No smoothness or semialgebraicity is
assumed: a small convex ball supplies the local neighborhood at the maximizer. -/
theorem exists_localMax_in_compact_superlevel_component {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (hf : Continuous f)
    (a : ℝ) (hcompact : IsCompact {z | a ≤ f z}) (x : E) (hx : a < f x) :
    ∃ y, y ∈ connectedComponentIn {z | a ≤ f z} x ∧ IsLocalMax f y ∧ f x ≤ f y := by
  let S := {z | a ≤ f z}
  have hxS : x ∈ S := hx.le
  have hc : IsCompact (connectedComponentIn S x) := by
    rw [connectedComponentIn_eq_image hxS]
    let : CompactSpace S := isCompact_iff_compactSpace.mp hcompact
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  have hxc : x ∈ connectedComponentIn S x := mem_connectedComponentIn hxS
  obtain ⟨y,hy,hmax⟩ := hc.exists_isMaxOn ⟨x,hxc⟩ hf.continuousOn
  have hxy : f x ≤ f y := hmax hxc
  have hay : a < f y := hx.trans_le hxy
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp ((isOpen_lt continuous_const hf).mem_nhds hay)
  have hballS : ball y r ⊆ S := by
    intro z hz
    show a ≤ f z
    exact le_of_lt (hball hz)
  have hballC : ball y r ⊆ connectedComponentIn S x := by
    rw [connectedComponentIn_eq hy]
    exact (convex_ball y r).isPreconnected.subset_connectedComponentIn
      (mem_ball_self hr) hballS
  refine ⟨y,hy,?_,hxy⟩
  exact Filter.Eventually.mono (Metric.ball_mem_nhds y hr) (fun z hz => hmax (hballC hz))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_localMax_in_compact_superlevel_component
