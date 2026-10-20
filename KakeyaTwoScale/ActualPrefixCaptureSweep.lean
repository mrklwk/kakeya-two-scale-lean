module
public import KakeyaTwoScale.ActualArchivePrefix

@[expose] public section

open Set Metric MeasureTheory MvPolynomial
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

def prefixCaptureLengths (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (depth : Fin H.polynomialSnapshots.length) (family : Fin k) : Fin depth.val → ℝ :=
  fun j => H.captureLengths family (H.positivePrefixIndex depth j)

theorem prefixCaptureLengths_pos (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (depth : Fin H.polynomialSnapshots.length) (family : Fin k) (j : Fin depth.val) :
    0 < H.prefixCaptureLengths depth family j := H.captureLengths_pos family _

def prefixCaptureCenter (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n : ℕ) (hn : b+c=n+1) (depth : Fin H.polynomialSnapshots.length) (y : T) :
    EuclideanSpace ℝ (Fin (n+1)) :=
  ((H.polynomialSnapshots_dimension _ (List.getElem_mem depth.isLt)).trans hn) ▸
    (H.polynomialSnapshots[depth]).state.ballCenter ((H.polynomialSnapshots[depth]).state.grain (I.cube y))

end ActualBufferedArchive

/-- A positive-codimension actual-prefix instance of the jointly quantified capture sweep.
The constant precedes ALL stage precision, finite types, input data, archive,
stopping depth, original representative, chart and scale. The degree calendar,
length positivity, equation insertion and stopping-depth bound are proved.
This is the one-scale analytic estimate; it does not assert a distinct-line
lower bound for this eligible universe or the nested-volume upper bound. -/
theorem actual_archive_prefix_capture_sweep (n t J0 fuel : ℕ) (C0 : ℝ) (hC : 0 ≤ C0) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (b c k A B Lh a J s : ℕ) (hn : b+c=n+1)
        (T C O : Type) [DecidableEq T] [DecidableEq C]
        (N : Fin k→ℝ) (I : AmbientBufferedStageData b c k A B Lh J s T C O)
        (P U : ℝ) (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel),
      J≤J0 → s=b*t →
      (∀ j∈Finset.range s, I.D j=partitionBoxDegree b j) →
      ∀ (depth : Fin H.polynomialSnapshots.length),
      ∀ y∈(H.polynomialSnapshots[depth]).state.tuples, ∀ (family : Fin k) (h : Fin (n+1))
        (outer : Fin depth.val) (rho slabStart slabLength : ℝ),
      0 < rho → 0 < slabLength →
      let D := archiveDegreeCalendar (n+1) t J0 fuel
      let Q := H.prefixCaptureEquations n (n+1+fuel) hn depth y
      let center := H.prefixCaptureCenter n hn depth y
      let L := H.prefixCaptureLengths depth family
      volume {v | ∃ z, universalEligibleLine D C0 h outer
        (captureParameters Q center L rho slabStart slabLength) v z} *
        ENNReal.ofReal (slabLength^(n+1)) ≤
      ENNReal.ofReal K * (volume.prod volume)
        {z : (Fin n→ℝ) × ℝ | center+euclideanUnsplit h (z.2,z.1) ∈
          thickening rho (captureZeroSet (Q outer) ∩ closedBall center ((C0+4)*L outer))} := by
  obtain ⟨K,hK,hvol⟩ := uniform_capture_depth_volume n (n+1+fuel)
    (archiveDegreeCalendar (n+1) t J0 fuel) (fuel+1) C0 hC
  refine ⟨K,hK,?_⟩
  intro b c k A B Lh a J s hn T C O _ _ N I P U H hJ hs hseq depth y hy family h outer rho slabStart slabLength hrho hslab
  have hd : depth.val≤fuel+1 := by have hh := H.polynomialSnapshots_length_le; have hi := depth.isLt; omega
  exact hvol depth.val hd h outer
    (H.prefixCaptureEquations n (n+1+fuel) hn depth y)
    (H.prefixCaptureEquations_degree_calendar n (n+1+fuel) hn depth y hy J0 hJ hs hseq)
    (H.prefixCaptureCenter n hn depth y) (H.prefixCaptureLengths depth family) (H.prefixCaptureLengths_pos depth family)
    rho slabStart slabLength hrho hslab

end KakeyaTwoScale
#print axioms KakeyaTwoScale.actual_archive_prefix_capture_sweep
