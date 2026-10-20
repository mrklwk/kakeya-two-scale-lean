module
public import KakeyaTwoScale.ActualGrainOriginalCount
public import KakeyaTwoScale.CalendarCountExponent

@[expose] public section

open Set Metric MeasureTheory
noncomputable section
namespace KakeyaTwoScale

/-- Actual original identifiers obey the exact delta^(1+r-d) exponent for a fixed calendar. -/
theorem actual_grain_original_count_exponent (n t J0 fuel A : ℕ) (K0 C0 : ℝ)
    (hK0 : 0≤K0) (hC0 : 0≤C0) :
    ∃ K : ℝ, 0<K ∧ ∀ (k B Lh a J s : ℕ)
      (T C O : Type) [DecidableEq T] [DecidableEq C] [DecidableEq O]
      (N : Fin k→ℝ) (I : AmbientBufferedStageData (n+1) 0 k A B Lh J s T C O)
      (P U : ℝ) (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel),
    J≤J0 → s=(n+1)*t → (∀ j∈Finset.range s, I.D j=partitionBoxDegree (n+1) j) → I.K≤K0 →
    (∀ j, I.W.length I.δ j≤1) →
    ∀ (direction : O→EuclideanSpace ℝ (Fin (n+1))),
    (∀ y∈I.W.tuples, ∀ j, I.W.axis j (I.W.parent y j)=direction (I.tube y j)) →
    (∀ o p, o≠p → I.δ/2≤dist (direction o) (direction p)) →
    ∀ (depth : Fin H.polynomialSnapshots.length), 0<depth.val → depth.val≤n+1 →
    let S := H.coordinateState (n+1) rfl depth
    ∀ y∈S.tuples, ∀ (family : Fin k),
    8*(max 1 (archiveRadiusCalendar A K0 fuel)*I.δ)≤S.length I.δ family →
    S.ballRadius≤C0*S.length I.δ family →
    let F := (S.grainRecords I.cube (S.grain (I.cube y)) family).image (S.original family)
    let L := H.prefixCaptureLengths depth family
    (F.card:ℝ)≤K*I.δ^((depth.val:ℤ)-(n:ℤ))/((List.finRange depth.val).map L).prod := by
  obtain ⟨K,hK,hcount⟩ := actual_grain_original_count n t J0 fuel A K0 C0 hK0 hC0
  let radius := max 1 (archiveRadiusCalendar A K0 fuel)
  refine ⟨K*(radius+1)^(fuel+1),by have := le_max_left 1 (archiveRadiusCalendar A K0 fuel); dsimp [radius]; positivity,?_⟩
  intro k B Lh a J s T C O _ _ _ N I P U H hJ hs hseq hIK hrootL direction hrootAxis hsep depth hdpos hd
  dsimp only
  intro y hy family hlong hradius
  have hh := hcount k B Lh a J s T C O N I P U H hJ hs hseq hIK hrootL direction hrootAxis hsep
    depth hdpos hd y hy family hlong hradius
  have hdepth : depth.val≤fuel+1 := by
    have hh := H.polynomialSnapshots_length_le
    have hi := depth.isLt
    omega
  have hprod : 0<((List.finRange depth.val).map (H.prefixCaptureLengths depth family)).prod := by
    apply List.prod_pos
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact H.prefixCaptureLengths_pos depth family i
  exact hh.trans (calendar_count_exponent n depth.val (fuel+1) K radius I.δ _ hK.le
    (le_max_left _ _) I.width_pos hprod hdepth)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.actual_grain_original_count_exponent
