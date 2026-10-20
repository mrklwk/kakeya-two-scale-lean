module
public import KakeyaTwoScale.ChartProjectionCofactor

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Actual geometric intersections of a set with a coordinate line. -/
def chartLineCount {n : ℕ} (Z : Set (Fin (n+1) → ℝ)) (y : Fin n → ℝ) : ℝ≥0∞ :=
  ({t : ℝ | Fin.cons t y ∈ Z} : Set ℝ).encard.toENNReal

/-- Injectivity of the chart identifies projected parameter fibers with actual
geometric intersections, without counting parameterizations more than once. -/
theorem chart_projection_fiber_count {α : Type*} {n : ℕ}
    (φ : α → (Fin (n+1) → ℝ)) (S : Set α) (hinj : InjOn φ S)
    (y : Fin n → ℝ) :
    actualFiberCount (fun x => transverseProjection n (φ x)) S y =
      chartLineCount (φ '' S) y := by
  classical
  let F : Set α := {x | x ∈ S ∧ transverseProjection n (φ x) = y}
  let g : α → ℝ := fun x => φ x 0
  have hg : InjOn g F := by
    intro x hx z hz he
    apply hinj hx.1 hz.1
    funext i
    refine Fin.cases he (fun j => ?_) i
    have hxy := congrFun hx.2 j
    have hzy := congrFun hz.2 j
    exact hxy.trans hzy.symm
  have he : g '' F = {t : ℝ | Fin.cons t y ∈ φ '' S} := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx.1, ?_⟩
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      exact congrFun hx.2 j
    · rintro ⟨x, hx, he⟩
      refine ⟨x, ⟨hx, ?_⟩, ?_⟩
      · funext j
        exact congrFun he j.succ
      · exact congrFun he 0
  change F.encard.toENNReal = _
  rw [chartLineCount, ← he, hg.encard_image]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.chart_projection_fiber_count
