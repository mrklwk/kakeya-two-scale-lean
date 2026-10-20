module
public import KakeyaTwoScale.ActualPolynomialArchive
public import KakeyaTwoScale.ActualArchiveUpperEpsilon

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale
open PolynomialArchiveSnapshot

theorem archiveRadiusCalendar_nonneg (A : ℕ) (K0 : ℝ) (hK : 0≤K0) (r : ℕ) :
    0≤archiveRadiusCalendar A K0 r := by
  induction r with
  | zero => exact hK
  | succ r ih => simp only [archiveRadiusCalendar]; positivity

theorem archiveRadiusCalendar_monotone (A : ℕ) (K0 : ℝ) (hK : 0≤K0) :
    Monotone (archiveRadiusCalendar A K0) := by
  apply monotone_nat_of_le_succ
  intro r
  simp only [archiveRadiusCalendar]
  have hh := archiveRadiusCalendar_nonneg A K0 hK r
  nlinarith [Nat.cast_nonneg (α:=ℝ) A]

namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

/-- Polynomial degree and capture radius are bounded by fixed calendars at
every actual entry. The bound allows early stopping and uses requested fuel,
so no choice of stopping time enters the complexity constant. -/
theorem polynomialSnapshots_calendar
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n J0 : ℕ) (K0 : ℝ) (hK0 : 0≤K0) :
    ∀ r : ℕ, b+c=n → s=b*t →
      (∀ j∈Finset.range s, I.D j=partitionBoxDegree b j) →
      J≤archiveDegreeCalendar n t J0 r → I.K≤archiveRadiusCalendar A K0 r →
      ∀ S∈H.polynomialSnapshots,
        S.degree≤archiveDegreeCalendar n t J0 (r+fuel) ∧
        S.radius≤archiveRadiusCalendar A K0 (r+fuel) ∧
        S.codimension≤c+fuel := by
  induction H with
  | zero I P U =>
    intro r hn hs hc hJ hK S hS
    change S∈[ofData I] at hS
    rcases List.mem_singleton.mp hS with rfl
    exact ⟨hJ,hK,le_rfl⟩
  | short I P U hshort =>
    intro r hn hs hc hJ hK S hS
    change S∈[ofData I] at hS
    rcases List.mem_singleton.mp hS with rfl
    exact ⟨hJ.trans (archiveDegreeCalendar_mono n t J0 (by have hb := I.dimension_pos; omega) (by omega)),
      hK.trans (archiveRadiusCalendar_monotone A K0 hK0 (by omega)),by dsimp [ofData]; omega⟩
  | last I P U Z =>
    intro r hn hs hc hJ hK S hS
    change S∈[ofData I,ofStage I Z] at hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact ⟨hJ.trans (archiveDegreeCalendar_mono n t J0 (by have hb := I.dimension_pos; omega) (by omega)),
        hK.trans (archiveRadiusCalendar_monotone A K0 hK0 (by omega)),by dsimp [ofData]; omega⟩
    · rcases List.mem_singleton.mp hS with rfl
      refine ⟨I.successorDegree_le_calendar n t J0 r hn hs hc hJ,?_,le_rfl⟩
      change 3*(2*(A:ℝ)+I.K)+6+3 ≤ archiveRadiusCalendar A K0 (r+1)
      simp only [archiveRadiusCalendar]
      linarith
  | next I P U Z hb ht tail ih =>
    intro r hn hs hc hJ hK S hS
    change S∈ofData I::tail.polynomialSnapshots at hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact ⟨hJ.trans (archiveDegreeCalendar_mono n t J0 (by have hb := I.dimension_pos; omega) (by omega)),
        hK.trans (archiveRadiusCalendar_monotone A K0 hK0 (by omega)),by dsimp [ofData]; omega⟩
    · have hJ' := I.successorDegree_le_calendar n t J0 r hn hs hc hJ
      have hK' : (I.nextData Z hb t ht).K≤archiveRadiusCalendar A K0 (r+1) := by
        rw [I.nextData_radius Z hb t ht]
        simp only [archiveRadiusCalendar]
        linarith
      have hh := ih (r+1) (by omega) rfl (by
        intro j hj
        simp only [AmbientBufferedStageData.nextData,FixedAmbientBufferedData.toAmbient_D,AmbientBufferedStageData.nextFrame]) hJ' hK' S hS
      simpa only [show (2:ℕ)=1+1 from rfl,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.archiveRadiusCalendar_monotone
#print axioms KakeyaTwoScale.ActualBufferedArchive.polynomialSnapshots_calendar
