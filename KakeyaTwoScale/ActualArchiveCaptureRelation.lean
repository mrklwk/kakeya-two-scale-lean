module
public import KakeyaTwoScale.ActualArchiveGrainFlag
public import KakeyaTwoScale.UniformCaptureDepth

@[expose] public section

open Set Metric MeasureTheory MvPolynomial
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

def captureLengths (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (family : Fin k) : Fin H.polynomialSnapshots.length → ℝ :=
  fun j => (H.polynomialSnapshots[j]).state.length I.δ family

theorem captureLengths_pos (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (family : Fin k) (j : Fin H.polynomialSnapshots.length) : 0 < H.captureLengths family j := by
  exact mul_pos I.width_pos (pow_pos (by norm_num) _)

def captureCenter (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n : ℕ) (hn : b+c=n+1) (y : T) : EuclideanSpace ℝ (Fin (n+1)) :=
  ((H.polynomialSnapshots_dimension _ H.terminalPolynomial_mem).trans hn) ▸
    H.terminalPolynomial.state.ballCenter (H.terminalPolynomial.state.grain (I.cube y))

/-- Exact zero-set interpretation of an actual indexed coefficient family.
Zero padding has no rank assertion: rank belongs to the ORIGINAL codimension
c+j equations, not the padded codomain. -/
theorem captureEquationFamilyAt_zero
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n : ℕ) (hn : b+c=n+1) (y : T) (j : Fin H.polynomialSnapshots.length)
    (x : EuclideanSpace ℝ (Fin (n+1))) :
    x∈captureZeroSet (H.captureEquationFamilyAt n (n+1+fuel) hn y j) ↔
      (((H.polynomialSnapshots_dimension _ (List.getElem_mem j.isLt)).trans hn).symm ▸ x) ∈
        (H.polynomialSnapshots[j]).zeroSet ((H.polynomialSnapshots[j]).state.grain (I.cube y)) := by
  apply PolynomialArchiveSnapshot.captureEquations_zero
  have hh : (H.polynomialSnapshots[j]).codimension≤c+fuel :=
    H.polynomialSnapshots_codimension_le _ (List.getElem_mem j.isLt)
  exact hh.trans (Nat.add_le_add_right (by omega) fuel)

end ActualBufferedArchive

/-- An actual-archive instance of the jointly quantified capture sweep.
The constant precedes ALL stage precision, finite types, input data, archive,
stopping depth, original representative, chart and scale. The degree calendar,
length positivity, equation insertion and stopping-depth bound are proved.
This is the one-scale analytic estimate; it does not assert a distinct-line
lower bound for this eligible universe or the nested-volume upper bound. -/
theorem actual_archive_capture_sweep (n t J0 fuel : ℕ) (C0 : ℝ) (hC : 0 ≤ C0) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (b c k A B Lh a J s : ℕ) (hn : b+c=n+1)
        (T C O : Type) [DecidableEq T] [DecidableEq C]
        (N : Fin k→ℝ) (I : AmbientBufferedStageData b c k A B Lh J s T C O)
        (P U : ℝ) (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel),
      J≤J0 → s=b*t →
      (∀ j∈Finset.range s, I.D j=partitionBoxDegree b j) →
      ∀ y∈H.terminal.state.tuples, ∀ (family : Fin k) (h : Fin (n+1))
        (outer : Fin H.polynomialSnapshots.length) (rho slabStart slabLength : ℝ),
      0 < rho → 0 < slabLength →
      let D := archiveDegreeCalendar (n+1) t J0 fuel
      let Q := H.captureEquationFamilyAt n (n+1+fuel) hn y
      let center := H.captureCenter n hn y
      let L := H.captureLengths family
      volume {v | ∃ z, universalEligibleLine D C0 h outer
        (captureParameters Q center L rho slabStart slabLength) v z} *
        ENNReal.ofReal (slabLength^(n+1)) ≤
      ENNReal.ofReal K * (volume.prod volume)
        {z : (Fin n→ℝ) × ℝ | center+euclideanUnsplit h (z.2,z.1) ∈
          thickening rho (captureZeroSet (Q outer) ∩ closedBall center ((C0+4)*L outer))} := by
  obtain ⟨K,hK,hvol⟩ := uniform_capture_depth_volume n (n+1+fuel)
    (archiveDegreeCalendar (n+1) t J0 fuel) (fuel+1) C0 hC
  refine ⟨K,hK,?_⟩
  intro b c k A B Lh a J s hn T C O _ _ N I P U H hJ hs hseq y hy family h outer rho slabStart slabLength hrho hslab
  exact hvol H.polynomialSnapshots.length H.polynomialSnapshots_length_le h outer
    (H.captureEquationFamilyAt n (n+1+fuel) hn y)
    (H.captureEquationFamilyAt_degree_calendar n (n+1+fuel) hn y hy J0 hJ hs hseq)
    (H.captureCenter n hn y) (H.captureLengths family) (H.captureLengths_pos family)
    rho slabStart slabLength hrho hslab

end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.captureEquationFamilyAt_zero
#print axioms KakeyaTwoScale.actual_archive_capture_sweep
