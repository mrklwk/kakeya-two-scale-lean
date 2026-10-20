module
public import KakeyaTwoScale.ArchiveCaptureEquations

@[expose] public section

open Set MvPolynomial
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive
open PolynomialArchiveSnapshot
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

def terminalPolynomial (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    PolynomialArchiveSnapshot k T C O := by
  induction H with
  | zero I P U => exact ofData I
  | short I P U _ => exact ofData I
  | last I P U Z => exact ofStage I Z
  | next I P U Z hb ht tail ih => exact ih

theorem terminalPolynomial_physical
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.terminalPolynomial.physical=H.terminal := by
  induction H with
  | zero => rfl
  | short => rfl
  | last => rfl
  | next I P U Z hb ht tail ih => exact ih

theorem polynomialSnapshots_head_mem
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    ofData I∈H.polynomialSnapshots := by
  cases H <;> simp [polynomialSnapshots]

theorem terminalPolynomial_mem
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.terminalPolynomial∈H.polynomialSnapshots := by
  induction H with
  | zero => simp [terminalPolynomial,polynomialSnapshots]
  | short => simp [terminalPolynomial,polynomialSnapshots]
  | last => simp [terminalPolynomial,polynomialSnapshots]
  | next I P U Z hb ht tail ih => exact List.mem_cons_of_mem _ ih

/-- Every actual earlier entry is an algebraic ancestor of the ACTUAL terminal
entry. The common-grain map is obtained from the recursive archive. -/
theorem polynomialSnapshots_ancestor_terminal
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    ∀ S∈H.polynomialSnapshots, Ancestor I.cube S H.terminalPolynomial := by
  induction H with
  | zero I P U =>
    intro S hS
    have he : S=ofData I := by simpa [polynomialSnapshots] using hS
    subst S
    exact Ancestor.refl _ _
  | short I P U hh =>
    intro S hS
    have he : S=ofData I := by simpa [polynomialSnapshots] using hS
    subst S
    exact Ancestor.refl _ _
  | last I P U Z =>
    intro S hS
    change S∈[ofData I,ofStage I Z] at hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact ofStage_ancestor I Z
    · have he := List.mem_singleton.mp hS
      subst S
      exact Ancestor.refl _ _
  | next I P U Z hb ht tail ih =>
    have hmid : Ancestor I.cube (ofStage I Z) tail.terminalPolynomial := by
      simpa only [AmbientBufferedStageData.nextData_cube,AmbientBufferedStageData.nextData_polynomialSnapshot] using
        ih _ tail.polynomialSnapshots_head_mem
    intro S hS
    change S∈ofData I::tail.polynomialSnapshots at hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact (ofStage_ancestor I Z).trans hmid
    · simpa only [terminalPolynomial,AmbientBufferedStageData.nextData_cube] using ih S hS

/-- All originals represented in one terminal grain see exactly the same
ancestor equations. A representative tuple cannot select a different flag. -/
theorem terminal_grain_ancestor_coherent
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (y z : T) (hy : y∈H.terminalPolynomial.state.tuples) (hz : z∈H.terminalPolynomial.state.tuples)
    (he : H.terminalPolynomial.state.grain (I.cube y)=H.terminalPolynomial.state.grain (I.cube z)) :
    ∀ S∈H.polynomialSnapshots, S.state.grain (I.cube y)=S.state.grain (I.cube z) := by
  intro S hS
  obtain ⟨hd,hs,parent,hparent,hzero⟩ := H.polynomialSnapshots_ancestor_terminal S hS
  exact (hparent y hy).symm.trans ((congrArg parent he).trans (hparent z hz))

/-- Consequently the literal padded coefficient family is representative
independent on a terminal grain, not merely equivalent as a set of zeros. -/
theorem captureEquationFamily_same_grain
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (y z : T) (hy : y∈H.terminalPolynomial.state.tuples) (hz : z∈H.terminalPolynomial.state.tuples)
    (he : H.terminalPolynomial.state.grain (I.cube y)=H.terminalPolynomial.state.grain (I.cube z)) :
    H.captureEquationFamily y=H.captureEquationFamily z := by
  funext j q
  unfold captureEquationFamily
  exact congrArg (fun g => (H.polynomialSnapshots[j]).captureEquations (b+c) (c+fuel) _ g q)
    (H.terminal_grain_ancestor_coherent y z hy hz he _ (List.getElem_mem j.isLt))

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.polynomialSnapshots_ancestor_terminal
#print axioms KakeyaTwoScale.ActualBufferedArchive.terminal_grain_ancestor_coherent
#print axioms KakeyaTwoScale.ActualBufferedArchive.captureEquationFamily_same_grain
