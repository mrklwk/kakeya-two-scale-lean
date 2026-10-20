module
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic

@[expose] public section

open Metric
namespace KakeyaTwoScale
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def segmentPoint (b v : E) (t : ℝ) : E := b+t • v

/-- Rounding the intercept and slope perturbs every point of the segment
by at most twice the parameter error. -/
theorem segmentPoint_dist_le (b v bP vP : E) (r t : ℝ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hb : dist b bP ≤ r) (hv : dist v vP ≤ r) :
    dist (segmentPoint b v t) (segmentPoint bP vP t) ≤ 2*r := by
  have hr : 0 ≤ r := (dist_nonneg).trans hb
  have hmul : |t| *dist v vP ≤ r := by
    rw [abs_of_nonneg ht.1]
    have hm := mul_le_mul_of_nonneg_right ht.2 (dist_nonneg (x:=v) (y:=vP))
    linarith
  calc
    _ ≤ dist b bP + dist (t • v) (t • vP) := dist_add_add_le _ _ _ _
    _ = dist b bP + |t| *dist v vP := by rw [dist_smul₀]; rfl
    _ ≤ 2*r := by linarith

/-- A whole horizontal cell near a child axis lies near its parent axis.
This is the geometric strengthening needed by the volume selection. -/
theorem whole_cell_parent_containment (b v bP vP : E) (r t : ℝ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hb : dist b bP ≤ r) (hv : dist v vP ≤ r)
    (cell : Set E) (hcell : ∀ x ∈ cell, dist x (segmentPoint b v t) ≤ r) :
    cell ⊆ Metric.closedBall (segmentPoint bP vP t) (3*r) := by
  intro x hx
  change dist x (segmentPoint bP vP t) ≤ 3*r
  calc
    _ ≤ dist x (segmentPoint b v t)+dist (segmentPoint b v t) (segmentPoint bP vP t) := dist_triangle _ _ _
    _ ≤ r+2*r := add_le_add (hcell x hx) (segmentPoint_dist_le b v bP vP r t ht hb hv)
    _ = 3*r := by ring

/-- An r-cover of a set gives a 2r-cover of its open r-neighborhood. -/
theorem thickening_cover {X : Type*} [PseudoMetricSpace X]
    (K : Set X) (centers : Finset X) (r : ℝ)
    (hcover : K ⊆ ⋃ c ∈ centers, Metric.ball c r) :
    Metric.thickening r K ⊆ ⋃ c ∈ centers, Metric.ball c (2*r) := by
  intro x hx
  obtain ⟨y,hy,hxy⟩ := Metric.mem_thickening_iff.mp hx
  obtain ⟨c,hc,hcy⟩ := Set.mem_iUnion₂.mp (hcover hy)
  apply Set.mem_iUnion₂.mpr
  refine ⟨c,hc,?_⟩
  change dist x c < 2*r
  have h := dist_triangle x y c
  have hc' : dist y c < r := hcy
  linarith
end KakeyaTwoScale
#print axioms KakeyaTwoScale.whole_cell_parent_containment
#print axioms KakeyaTwoScale.thickening_cover
