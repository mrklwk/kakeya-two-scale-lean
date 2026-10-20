module
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- A quantitative wall bridge for an actual local graph. The buffer coverage
premise is essential: a small tangent angle alone does not give this domain.
The ambient space can carry its genuine Euclidean metric; no product-norm
identification is used. -/
theorem graph_wall_bridge {E V : Type*} [PseudoMetricSpace E] [PseudoMetricSpace V]
    (π : E → V) (g : V → E) (U₀ U Z : Set V) (A : Set E) (L : NNReal)
    (hπ : LipschitzWith 1 π) (hg : LipschitzOnWith L g U)
    (hcore : U₀ ⊆ U) (hsection : ∀ v ∈ U, π (g v) = v)
    (hgraph : ∀ v ∈ U, g v ∈ A) (η r : ℝ)
    (hbuffer : ∀ v ∈ U₀, ball v (η+r) ⊆ U)
    {x : E} (hx : x ∈ thickening η (g '' U₀))
    (hwall : π x ∈ thickening r Z) :
    x ∈ thickening (η + (L:ℝ)*(η+r)) (A ∩ π ⁻¹' Z) := by
  obtain ⟨z,⟨v,hv,rfl⟩,hxv⟩ := mem_thickening_iff.mp hx
  obtain ⟨u,hu,hxu⟩ := mem_thickening_iff.mp hwall
  have hvU := hcore hv
  have hproj : dist (π x) v ≤ dist x (g v) := by
    simpa [hsection v hvU] using hπ.dist_le_mul x (g v)
  have huv : dist u v < η+r := by
    calc
      dist u v ≤ dist u (π x) + dist (π x) v := dist_triangle _ _ _
      _ < r + η := add_lt_add_of_lt_of_le (by simpa [dist_comm] using hxu)
        (le_of_lt (lt_of_le_of_lt hproj hxv))
      _ = η+r := by ring
  have huU : u ∈ U := hbuffer v hv (by simpa only [mem_ball] using huv)
  apply mem_thickening_iff.mpr
  refine ⟨g u,⟨hgraph u huU,?_⟩,?_⟩
  · change π (g u) ∈ Z
    simpa [hsection u huU] using hu
  · calc
      dist x (g u) ≤ dist x (g v) + dist (g v) (g u) := dist_triangle _ _ _
      _ ≤ dist x (g v) + (L:ℝ)*dist v u :=
        add_le_add le_rfl ((lipschitzOnWith_iff_dist_le_mul.mp hg) v hvU u huU)
      _ < η + (L:ℝ)*(η+r) := add_lt_add_of_lt_of_le hxv
        (mul_le_mul_of_nonneg_left (by simpa [dist_comm] using le_of_lt huv) L.coe_nonneg)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.graph_wall_bridge
