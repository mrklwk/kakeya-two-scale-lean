module
public import KakeyaTwoScale.ArchiveCoordinateState

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

/-- The actual prefix captures each owned tuple's cylinder with the one fixed
coefficient family of its endpoint grain. Calendar enlargement is proved here. -/
theorem coordinate_prefix_capture
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n : ℕ) (hn : b+c=n+1) (depth : Fin H.polynomialSnapshots.length)
    (y z : T) (hy : y∈(H.coordinateState (n+1) hn depth).tuples)
    (hz : z∈(H.coordinateState (n+1) hn depth).tuples)
    (hgrain : (H.coordinateState (n+1) hn depth).grain (I.cube y)=
      (H.coordinateState (n+1) hn depth).grain (I.cube z))
    (J0 : ℕ) (hJ : J≤J0) (hs : s=b*t)
    (hseq : ∀ j∈Finset.range s, I.D j=partitionBoxDegree b j)
    (K0 : ℝ) (hK0 : 0≤K0) (hIK : I.K≤K0) (i : Fin depth.val) (family : Fin k) :
    let S := H.coordinateState (n+1) hn (H.positivePrefixIndex depth i)
    S.geometry I.δ family (S.parent y family) ⊆
      thickening ((max 1 (archiveRadiusCalendar A K0 fuel))*I.δ)
        (captureZeroSet (H.prefixCaptureEquations n (n+1+fuel) hn depth z i)) := by
  dsimp only
  have hy' : y∈(H.polynomialSnapshots[depth]).state.tuples := by
    rwa [H.coordinateState_tuples] at hy
  have hz' : z∈(H.polynomialSnapshots[depth]).state.tuples := by
    rwa [H.coordinateState_tuples] at hz
  have hgrain' : (H.polynomialSnapshots[depth]).state.grain (I.cube y)=
      (H.polynomialSnapshots[depth]).state.grain (I.cube z) :=
    (PolynomialArchiveSnapshot.coordinateState_grain_eq _ _ _ _ _ _).mp hgrain
  have hsame := H.prefixCaptureEquations_same_grain n (n+1+fuel) hn depth y z hy' hz' hgrain'
  let X := H.polynomialSnapshots[H.positivePrefixIndex depth i]
  have hX : X∈H.polynomialSnapshots := List.getElem_mem (H.positivePrefixIndex depth i).isLt
  have he : X.codimension≤n+1+fuel := by
    have hh := H.polynomialSnapshots_codimension_le X hX
    omega
  have hmem : y∈(H.coordinateState (n+1) hn (H.positivePrefixIndex depth i)).tuples := by
    rw [H.coordinateState_tuples]
    exact H.prefix_tuple_mem depth y hy' i
  have hcap := X.coordinateState_capture (n+1) (n+1+fuel)
    ((H.polynomialSnapshots_dimension X hX).trans hn) he I.δ I.cube
    (H.polynomialSnapshots_sound X hX) y hmem family
  change _⊆thickening (X.radius*I.δ)
    (captureZeroSet (H.prefixCaptureEquations n (n+1+fuel) hn depth y i)) at hcap
  rw [hsame] at hcap
  have hcal := H.polynomialSnapshots_calendar (n+1) J0 K0 hK0 0 hn hs hseq hJ hIK X hX
  have hradius : X.radius ≤ max 1 (archiveRadiusCalendar A K0 fuel) :=
    (by simpa only [Nat.zero_add] using hcal.2.1 : X.radius≤archiveRadiusCalendar A K0 fuel).trans (le_max_right _ _)
  intro x hx
  obtain ⟨v,hv,hd⟩ := mem_thickening_iff.mp (hcap hx)
  exact mem_thickening_iff.mpr ⟨v,hv,hd.trans_le (mul_le_mul_of_nonneg_right hradius I.width_pos.le)⟩

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.coordinate_prefix_capture
