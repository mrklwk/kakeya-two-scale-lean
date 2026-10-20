module
public import KakeyaTwoScale.CoordinateHypersurfaceChart
public import Mathlib.Topology.Compactness.Lindelof

@[expose] public section

open MvPolynomial MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace KakeyaTwoScale

/-- Regular zeros of each defining polynomial have a countable family of actual
smooth coordinate charts. The open subcover is chosen within that fixed stratum. -/
theorem regular_zero_countable_charts {n : ℕ} (Q : MvPolynomial (Fin (n+1)) ℝ) :
    ∃ C : ℕ → SmoothCoordinateChart n,
      {x | eval x Q = 0 ∧ ∃ j, eval x (pderiv j Q) ≠ 0} ⊆
        ⋃ i, (C i).map '' (C i).source := by
  classical
  let R : Set (Fin (n+1) → ℝ) := {x | eval x Q = 0 ∧ ∃ j, eval x (pderiv j Q) ≠ 0}
  by_cases hR : R.Nonempty
  · let : Nonempty R := hR.to_subtype
    choose C W hW ha him using fun a : R => polynomial_coordinate_chart Q a a.property.1 a.property.2
    obtain ⟨f,hf⟩ := (HereditarilyLindelofSpace.isLindelof R).indexed_countable_subcover
      W hW (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,ha ⟨x,hx⟩⟩)
    refine ⟨fun i => C (f i), ?_⟩
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hf hx)
    apply mem_iUnion.mpr
    refine ⟨i,?_⟩
    rw [him]
    exact ⟨hi,hx.1⟩
  · refine ⟨fun _ => SmoothCoordinateChart.empty n, ?_⟩
    intro x hx
    exact (hR ⟨x,hx⟩).elim

/-- Every zero of a nonzero polynomial is covered by countably many constructed
smooth injective charts, including singular zeros and repeated polynomial factors.
The chart images may include extra points; subsequent restriction to Z(P) is essential. -/
theorem polynomial_zero_countable_charts {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (hP : P ≠ 0) :
    ∃ C : ℕ → SmoothCoordinateChart n,
      {x | eval x P = 0} ⊆ ⋃ i, (C i).map '' (C i).source := by
  classical
  let F := derivativeCoverFamily P P.totalDegree
  choose C hC using fun Q : MvPolynomial (Fin (n+1)) ℝ => regular_zero_countable_charts Q
  by_cases hF : F.Nonempty
  · let : Nonempty (↑F : Type _) := hF.to_subtype
    obtain ⟨f,hf⟩ := exists_surjective_nat (↑F × ℕ)
    refine ⟨fun i => C (f i).1 (f i).2, ?_⟩
    intro x hx
    obtain ⟨Q,hQ,hzero,hreg⟩ := derivativeCoverFamily_covers P hP le_rfl x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hC Q ⟨hzero,hreg⟩)
    obtain ⟨i,hi⟩ := hf (⟨Q,hQ⟩,j)
    apply mem_iUnion.mpr
    refine ⟨i,?_⟩
    simpa only [hi] using hj
  · refine ⟨fun _ => SmoothCoordinateChart.empty n, ?_⟩
    intro x hx
    obtain ⟨Q,hQ,-⟩ := derivativeCoverFamily_covers P hP le_rfl x hx
    exact (hF ⟨Q,hQ⟩).elim

end KakeyaTwoScale
#print axioms KakeyaTwoScale.regular_zero_countable_charts
#print axioms KakeyaTwoScale.polynomial_zero_countable_charts
