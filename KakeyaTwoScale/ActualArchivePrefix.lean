module
public import KakeyaTwoScale.ActualArchiveCaptureRelation

@[expose] public section

open Set MvPolynomial
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive
open PolynomialArchiveSnapshot
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

theorem polynomialSnapshots_ancestor_index
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (i j : Fin H.polynomialSnapshots.length) (hij : i≤j) :
    Ancestor I.cube (H.polynomialSnapshots[i]) (H.polynomialSnapshots[j]) := by
  obtain rfl | hlt := Fin.eq_or_lt_of_le hij
  · exact Ancestor.refl _ _
  · exact H.polynomialSnapshots_ancestry.2.rel_get_of_lt hlt

/-- Index the positive-codimension levels of an ACTUAL prefix, excluding root
and all entries after the chosen depth. No short later entry is smuggled into
long-prefix eligibility. -/
def positivePrefixIndex (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (depth : Fin H.polynomialSnapshots.length) (j : Fin depth.val) : Fin H.polynomialSnapshots.length :=
  ⟨j.val+1,by have hd := depth.isLt; have hj := j.isLt; omega⟩

theorem positivePrefixIndex_le (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (depth : Fin H.polynomialSnapshots.length) (j : Fin depth.val) :
    H.positivePrefixIndex depth j≤depth := by
  change j.val+1≤depth.val
  omega

theorem positivePrefix_codimension (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (depth : Fin H.polynomialSnapshots.length) (j : Fin depth.val) :
    (H.polynomialSnapshots[H.positivePrefixIndex depth j]).codimension=c+(j.val+1) := by
  exact H.polynomialSnapshots_codimension (j.val+1) _
    (List.getElem?_eq_getElem (H.positivePrefixIndex depth j).isLt)

def prefixCaptureEquations (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n e : ℕ) (hn : b+c=n+1) (depth : Fin H.polynomialSnapshots.length) (y : T) :
    Fin depth.val → Fin e → MvPolynomial (Fin (n+1)) ℝ :=
  fun j => H.captureEquationFamilyAt n e hn y (H.positivePrefixIndex depth j)

theorem prefix_tuple_mem (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (depth : Fin H.polynomialSnapshots.length) (y : T)
    (hy : y∈(H.polynomialSnapshots[depth]).state.tuples) (j : Fin depth.val) :
    y∈(H.polynomialSnapshots[H.positivePrefixIndex depth j]).state.tuples := by
  obtain ⟨hd,hs,rest⟩ := H.polynomialSnapshots_ancestor_index _ depth (H.positivePrefixIndex_le depth j)
  exact hs hy

theorem prefixCaptureEquations_degree_calendar
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n e : ℕ) (hn : b+c=n+1) (depth : Fin H.polynomialSnapshots.length)
    (y : T) (hy : y∈(H.polynomialSnapshots[depth]).state.tuples)
    (J0 : ℕ) (hJ : J≤J0)
    (hs : s=b*t) (hseq : ∀ j∈Finset.range s, I.D j=partitionBoxDegree b j) :
    ∀ j q, (H.prefixCaptureEquations n e hn depth y j q).totalDegree ≤
      archiveDegreeCalendar (n+1) t J0 fuel := by
  classical
  intro j q
  let S := H.polynomialSnapshots[H.positivePrefixIndex depth j]
  have hS : S∈H.polynomialSnapshots := List.getElem_mem (H.positivePrefixIndex depth j).isLt
  apply S.captureEquations_degree
  intro z
  have hc := H.polynomialSnapshots_calendar (n+1) J0 (max I.K 0)
    (le_max_right _ _) 0 hn hs hseq hJ (le_max_left _ _) S hS
  exact ((H.polynomialSnapshots_sound S hS).1 _
    (Finset.mem_image.mpr ⟨y,H.prefix_tuple_mem depth y hy j,rfl⟩) z).trans
    (by simpa only [Nat.zero_add] using hc.1)

/-- All actual originals in the chosen prefix grain use the same literal
coefficient family, even when the full archive continues to shorter levels. -/
theorem prefixCaptureEquations_same_grain
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n e : ℕ) (hn : b+c=n+1) (depth : Fin H.polynomialSnapshots.length)
    (y z : T) (hy : y∈(H.polynomialSnapshots[depth]).state.tuples)
    (hz : z∈(H.polynomialSnapshots[depth]).state.tuples)
    (he : (H.polynomialSnapshots[depth]).state.grain (I.cube y)=
      (H.polynomialSnapshots[depth]).state.grain (I.cube z)) :
    H.prefixCaptureEquations n e hn depth y=H.prefixCaptureEquations n e hn depth z := by
  funext j q
  obtain ⟨hd,hs,parent,hparent,hzero⟩ := H.polynomialSnapshots_ancestor_index _ depth
    (H.positivePrefixIndex_le depth j)
  have hg := (hparent y hy).symm.trans ((congrArg parent he).trans (hparent z hz))
  exact congrArg (fun g => (H.polynomialSnapshots[H.positivePrefixIndex depth j]).captureEquations
    (n+1) e _ g q) hg

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.positivePrefix_codimension
#print axioms KakeyaTwoScale.ActualBufferedArchive.prefixCaptureEquations_degree_calendar
#print axioms KakeyaTwoScale.ActualBufferedArchive.prefixCaptureEquations_same_grain
