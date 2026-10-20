module
public import KakeyaTwoScale.FrozenAncestorAxisCapture
public import KakeyaTwoScale.ActualArchiveAnalyticSelection

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale
namespace FrozenGeometryState

/-- A family maximal in actual physical length exceeds the threshold whenever
any family does. Positive dyadic height requires the threshold to be at least δ. -/
theorem exists_maximal_long_family {n k : ℕ} {T C O : Type}
    (S : FrozenGeometryState n k T C O) (δ threshold : ℝ)
    (hlong : ∃ j, threshold<S.length δ j) :
    ∃ j, (∀ i, S.length δ i≤S.length δ j) ∧ threshold<S.length δ j := by
  classical
  obtain ⟨j₀,hj₀⟩ := hlong
  have hne : (Finset.univ.image (S.length δ)).Nonempty :=
    ⟨S.length δ j₀,Finset.mem_image.mpr ⟨j₀,Finset.mem_univ _,rfl⟩⟩
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp (Finset.max'_mem _ hne)
  have hmax (i) : S.length δ i≤S.length δ j := by
    rw [he]
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  exact ⟨j,hmax,hj₀.trans_le (hmax j₀)⟩

end FrozenGeometryState
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

/-- The actual first-short selection supplies a maximal long family at
each earlier level; it never assigns old lower counts to selected marginals. -/
theorem exists_first_short_maximal_families
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) (R : ℝ) :
    ∃ r : ℕ, r≤H.drops ∧
      (r=H.drops ∨ ∀ j, (H.snapshotAt r).state.length I.δ j≤8*R*I.δ) ∧
      (∀ i<r, ∃ j,
        (∀ l, (H.snapshotAt i).state.length I.δ l≤(H.snapshotAt i).state.length I.δ j) ∧
        8*R*I.δ<(H.snapshotAt i).state.length I.δ j) ∧
      tupleCubeMass I.W.tuples I.cube I.cubes I.alpha/H.loss≤
        tupleCubeMass (H.snapshotAt r).state.tuples I.cube I.cubes I.alpha := by
  obtain ⟨r,hr,hstop,hlong,_,_,hmass⟩ := H.exists_first_short_snapshot (8*R)
  refine ⟨r,hr,hstop,?_,hmass⟩
  intro i hi
  exact ((H.snapshotAt i).state.exists_maximal_long_family I.δ (8*R*I.δ) (hlong i hi))

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.exists_maximal_long_family
#print axioms KakeyaTwoScale.ActualBufferedArchive.exists_first_short_maximal_families
