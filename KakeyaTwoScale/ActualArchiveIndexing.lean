module
public import KakeyaTwoScale.ActualPolynomialArchive

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive
open PolynomialArchiveSnapshot
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

/-- Actual list positions have exact codimension, including the initial
codimension-c entry at position zero. An upper calendar is not substituted for
this equality. -/
theorem polynomialSnapshots_codimension
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    ∀ j : ℕ, ∀ S, H.polynomialSnapshots[j]?=some S → S.codimension=c+j := by
  induction H with
  | zero I P U =>
    intro j S hS
    cases j with
    | zero => have he : ofData I=S := by simpa [polynomialSnapshots] using hS
              subst S; rfl
    | succ j => simp [polynomialSnapshots] at hS
  | short I P U hshort =>
    intro j S hS
    cases j with
    | zero => have he : ofData I=S := by simpa [polynomialSnapshots] using hS
              subst S; rfl
    | succ j => simp [polynomialSnapshots] at hS
  | last I P U Z =>
    intro j S hS
    cases j with
    | zero => have he : ofData I=S := by simpa [polynomialSnapshots] using hS
              subst S; rfl
    | succ j =>
      cases j with
      | zero => have he : ofStage I Z=S := by simpa [polynomialSnapshots] using hS
                subst S; rfl
      | succ j => simp [polynomialSnapshots] at hS
  | next I P U Z hb ht tail ih =>
    intro j S hS
    cases j with
    | zero => have he : ofData I=S := by simpa only [polynomialSnapshots,List.getElem?_cons_zero,Option.some.injEq] using hS
              subst S; rfl
    | succ j =>
      have hh := ih j S (by simpa only [polynomialSnapshots,List.getElem?_cons_succ] using hS)
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Every actual polynomial snapshot uses the original ambient dimension. -/
theorem polynomialSnapshots_dimension
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    ∀ S∈H.polynomialSnapshots, S.dimension=b+c := by
  intro S hS
  exact (H.polynomialSnapshots_ancestry.1 S hS).choose

/-- Actual depth is bounded before finite data and early-stopping choices. -/
theorem polynomialSnapshots_length_le
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.polynomialSnapshots.length ≤ fuel+1 := by
  induction H with
  | zero => simp [polynomialSnapshots]
  | short => simp [polynomialSnapshots]
  | last => simp [polynomialSnapshots]
  | next I P U Z hb ht tail ih =>
    simpa only [polynomialSnapshots,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Nat.add_le_add_right ih 1

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.polynomialSnapshots_codimension
#print axioms KakeyaTwoScale.ActualBufferedArchive.polynomialSnapshots_dimension
#print axioms KakeyaTwoScale.ActualBufferedArchive.polynomialSnapshots_length_le
