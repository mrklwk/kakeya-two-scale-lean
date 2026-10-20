module
public import KakeyaTwoScale.ActualArchiveMassCalendar

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- A fixed polynomial-complexity hierarchy, chosen before the scale. -/
def archiveDegreeCalendar (n t J0 : ℕ) : ℕ → ℕ
  | 0 => J0
  | r+1 => 2*n*archiveDegreeCalendar n t J0 r+2*n^2*2^t

/-- The physical neighborhood hierarchy is also fixed before the scale. -/
def archiveRadiusCalendar (A : ℕ) (K0 : ℝ) : ℕ → ℝ
  | 0 => K0
  | r+1 => 3*archiveRadiusCalendar A K0 r+6*A+9

 theorem calendar_degree_step_le (b c n J t : ℕ) (hb : 0<b) (hn : b+c=n) :
    max J (max (2*c*(J-1)) (b*(∑ j ∈ Finset.range (b*t), partitionBoxDegree b j))) ≤
      2*n*J+2*n^2*2^t := by
  have hs := partitionBoxDegree_sum b hb t
  have hbN : b ≤ n := by omega
  have hcN : c ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hJ : J-1 ≤ J := Nat.sub_le _ _
  apply max_le
  · have h : J ≤ 2*n*J := by
      have htwo : 1 ≤ 2*n := by omega
      simpa using Nat.mul_le_mul_right J htwo
    exact h.trans (Nat.le_add_right _ _)
  · apply max_le
    · have h := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hcN) hJ
      omega
    · have hb2 : b^2 ≤ n^2 := Nat.pow_le_pow_left hbN 2
      have hm := Nat.mul_le_mul_right (2^t) hb2
      nlinarith

namespace AmbientBufferedStageData
variable {b c k A B Lh J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]

theorem successorDegree_le_calendar (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    (n t J0 r : ℕ) (hn : b+c=n) (hs : s=b*t)
    (hcalendar : ∀ j ∈ Finset.range s, I.D j=partitionBoxDegree b j)
    (hJ : J ≤ archiveDegreeCalendar n t J0 r) :
    I.successorDegree ≤ archiveDegreeCalendar n t J0 (r+1) := by
  have hsum : (∑ j ∈ Finset.range s, I.D j)=∑ j ∈ Finset.range (b*t), partitionBoxDegree b j := by
    rw [←hs]
    exact Finset.sum_congr rfl hcalendar
  unfold successorDegree
  rw [hsum]
  apply (calendar_degree_step_le b c n J t I.dimension_pos hn).trans
  simp only [archiveDegreeCalendar]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left (2*n) hJ) _

/-- Exact recurrence on the actual next raw geometric input. -/
theorem nextData_radius (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k → ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a) (hb : 1<b) (t : ℕ) (ht : 2 ≤ t) :
    (I.nextData Z hb t ht).K=3*I.K+6*A+9 := by
  rw [nextData,FixedAmbientBufferedData.toAmbient_K]
  change 3*(2*(A:ℝ)+I.K)+6+3=3*I.K+6*A+9
  ring

end AmbientBufferedStageData
end KakeyaTwoScale
#print axioms KakeyaTwoScale.calendar_degree_step_le
#print axioms KakeyaTwoScale.AmbientBufferedStageData.successorDegree_le_calendar
#print axioms KakeyaTwoScale.AmbientBufferedStageData.nextData_radius
