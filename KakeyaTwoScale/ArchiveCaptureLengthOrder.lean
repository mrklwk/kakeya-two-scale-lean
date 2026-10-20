module
public import KakeyaTwoScale.ArchiveOriginalEquations
public import KakeyaTwoScale.FrozenPhysicalAccounting

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale
namespace BufferedArchiveSnapshot

/-- Actual whole-cylinder containment forces the common family length to
shrink. The witness is a represented tuple of the descendant snapshot. -/
theorem PhysicalAncestor.length_le {k : ℕ} {T C O : Type} {delta : ℝ}
    {S U : BufferedArchiveSnapshot k T C O} (hh : PhysicalAncestor delta S U)
    (hd : 0<delta) (tube : T→Fin k→O) (hS : Certified delta tube S)
    (hU : Certified delta tube U) (j : Fin k) :
    U.state.length delta j≤S.state.length delta j := by
  rcases S with ⟨n,S⟩
  rcases U with ⟨m,U⟩
  obtain ⟨he,hs,hc,ha,ho⟩ := hh
  dsimp only at he
  subst m
  obtain ⟨y,hy⟩ := hU.1
  have hL : 0<S.length delta j := mul_pos hd (pow_pos (by norm_num) _)
  have hl : 0<U.length delta j := mul_pos hd (pow_pos (by norm_num) _)
  have hcontain := hc y hy j
  change flatCylinder _ _ _ _⊆flatCylinder _ _ _ _ at hcontain
  rw [ha y hy j] at hcontain
  have hv := disjoint_contained_cylinders_length_sum ({0} : Finset ℕ)
    (S.base j (S.parent y j)) (S.axis j (S.parent y j))
    (fun _ => U.base j (U.parent y j)) (fun _ => U.length delta j)
    (S.length delta j) delta (hS.2.1 j _) hL hd (fun _ _ => hl)
    (fun _ _ => hcontain) (by simp)
  simpa only [Finset.sum_singleton] using hv

end BufferedArchiveSnapshot
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

theorem captureLengths_antitone
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) (family : Fin k) :
    Antitone (H.captureLengths family) := by
  intro i j hij
  obtain rfl | hlt := Fin.eq_or_lt_of_le hij
  · rfl
  have hp : H.polynomialSnapshots.Pairwise
      (fun S U => BufferedArchiveSnapshot.PhysicalAncestor I.δ S.physical U.physical) := by
    have hh := H.snapshots_physical_ancestry.2
    rw [← H.polynomialSnapshots_physical,List.pairwise_map] at hh
    exact hh
  have hh := hp.rel_get_of_lt hlt
  have hmem (i : Fin H.polynomialSnapshots.length) :
      (H.polynomialSnapshots[i]).physical∈H.snapshots := by
    rw [← H.polynomialSnapshots_physical]
    exact List.mem_map.mpr ⟨_,List.getElem_mem i.isLt,rfl⟩
  exact hh.length_le I.width_pos I.tube
    (H.snapshots_certified _ (hmem i)) (H.snapshots_certified _ (hmem j)) family

theorem prefixCaptureLengths_antitone
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (depth : Fin H.polynomialSnapshots.length) (family : Fin k) :
    Antitone (H.prefixCaptureLengths depth family) := by
  intro i j hij
  apply H.captureLengths_antitone family
  change i.val+1≤j.val+1
  exact Nat.add_le_add_right hij 1

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.BufferedArchiveSnapshot.PhysicalAncestor.length_le
#print axioms KakeyaTwoScale.ActualBufferedArchive.captureLengths_antitone
#print axioms KakeyaTwoScale.ActualBufferedArchive.prefixCaptureLengths_antitone
