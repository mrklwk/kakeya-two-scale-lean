module
public import KakeyaTwoScale.WeightedTupleMass
public import KakeyaTwoScale.ActualStoppingCases

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k → ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O}
    {P U : ℝ} {fuel : ℕ}

/-- Actual archive mass retention transfers to fixed-band weights of the
same stored original tuples. It pays precisely the band factor 2^alpha and
the actual archive loss, including root, frozen and terminal snapshots. -/
theorem snapshot_weighted_mass
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (i : ℕ) (hi : i ≤ H.drops) (w : T → ℝ) {θ : ℝ} (hθ : 0 < θ)
    (hw : ∀ y ∈ I.W.tuples, θ ≤ w y ∧ w y ≤ 2 * θ) :
    weightedTupleCubeMass I.W.tuples I.cube I.cubes w I.alpha /
      (2 ^ I.alpha * H.loss) ≤
      weightedTupleCubeMass (H.snapshotAt i).state.tuples I.cube I.cubes w I.alpha := by
  exact weightedTupleCubeMass_dyadic_retention I.W.tuples (H.snapshotAt i).state.tuples
    (H.snapshots_tuples_subset _ (H.snapshotAt_mem i hi)) I.cube I.cubes w
    hθ I.exponent_pos.le H.loss_pos hw (H.snapshot_mass i hi)

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.snapshot_weighted_mass
