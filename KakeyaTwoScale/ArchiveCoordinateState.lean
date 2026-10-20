module
public import KakeyaTwoScale.ArchiveCaptureLengthOrder
public import KakeyaTwoScale.ActualArchiveLocalization

@[expose] public section

open Set Metric MvPolynomial
noncomputable section
namespace KakeyaTwoScale
namespace PolynomialArchiveSnapshot
variable {k : ℕ} {T C O : Type}

def coordinateState (S : PolynomialArchiveSnapshot k T C O) (n : ℕ) (hd : S.dimension=n) :
    FrozenGeometryState n k T C O := hd ▸ S.state

theorem coordinateState_tuples (S : PolynomialArchiveSnapshot k T C O) (n : ℕ) (hd : S.dimension=n) :
    (S.coordinateState n hd).tuples=S.state.tuples := by subst n; rfl

theorem coordinateState_grain_eq (S : PolynomialArchiveSnapshot k T C O) (n : ℕ) (hd : S.dimension=n)
    (cube : T→C) (y z : T) :
    (S.coordinateState n hd).grain (cube y)=(S.coordinateState n hd).grain (cube z) ↔
      S.state.grain (cube y)=S.state.grain (cube z) := by subst n; rfl

theorem coordinateState_center (S : PolynomialArchiveSnapshot k T C O) (n : ℕ) (hd : S.dimension=n)
    (cube : T→C) (y : T) :
    (S.coordinateState n hd).ballCenter ((S.coordinateState n hd).grain (cube y))=
      (hd ▸ S.state.ballCenter (S.state.grain (cube y))) := by subst n; rfl

theorem coordinateState_length (S : PolynomialArchiveSnapshot k T C O) (n : ℕ) (hd : S.dimension=n)
    (delta : ℝ) (j : Fin k) : (S.coordinateState n hd).length delta j=S.state.length delta j := by subst n; rfl

theorem coordinateState_certified (S : PolynomialArchiveSnapshot k T C O) (n : ℕ) (hd : S.dimension=n)
    (delta : ℝ) (tube : T→Fin k→O) (hc : BufferedArchiveSnapshot.Certified delta tube S.physical) :
    BufferedArchiveSnapshot.Certified delta tube (BufferedArchiveSnapshot.ofState (S.coordinateState n hd)) := by
  subst n
  exact hc

theorem coordinateState_localized (S : PolynomialArchiveSnapshot k T C O) (n : ℕ) (hd : S.dimension=n)
    (delta : ℝ) (cube : T→C) (hc : BufferedArchiveSnapshot.Localized delta cube S.physical) :
    BufferedArchiveSnapshot.Localized delta cube (BufferedArchiveSnapshot.ofState (S.coordinateState n hd)) := by
  subst n
  exact hc

theorem coordinateState_radius_controlled (S : PolynomialArchiveSnapshot k T C O) (n : ℕ)
    (hd : S.dimension=n) (A : ℕ) (delta : ℝ)
    (hc : BufferedArchiveSnapshot.RadiusControlled A delta S.physical) :
    BufferedArchiveSnapshot.RadiusControlled A delta (BufferedArchiveSnapshot.ofState (S.coordinateState n hd)) := by
  subst n
  exact hc

theorem coordinateState_ancestor (S U : PolynomialArchiveSnapshot k T C O) (n : ℕ)
    (hs : S.dimension=n) (hu : U.dimension=n) (delta : ℝ)
    (hc : BufferedArchiveSnapshot.PhysicalAncestor delta S.physical U.physical) :
    BufferedArchiveSnapshot.PhysicalAncestor delta
      (BufferedArchiveSnapshot.ofState (S.coordinateState n hs))
      (BufferedArchiveSnapshot.ofState (U.coordinateState n hu)) := by
  rcases S with ⟨s,sc,sD,S,sP,sR⟩
  rcases U with ⟨u,uc,uD,U,uP,uR⟩
  dsimp only at hs hu
  subst s
  subst u
  exact hc

/-- Transport actual whole-cylinder capture and identify the same padded zeros
in common coordinates. This is independent of any representative selection. -/
theorem coordinateState_capture (S : PolynomialArchiveSnapshot k T C O) (n e : ℕ)
    (hd : S.dimension=n) (he : S.codimension≤e) (delta : ℝ) (cube : T→C)
    (hs : S.Sound delta cube) (y : T) (hy : y∈(S.coordinateState n hd).tuples) (j : Fin k) :
    (S.coordinateState n hd).geometry delta j ((S.coordinateState n hd).parent y j) ⊆
      thickening (S.radius*delta) {x : EuclideanSpace ℝ (Fin n) |
        ∀ z, eval x.ofLp (S.captureEquations n e hd (S.state.grain (cube y)) z)=0} := by
  subst n
  have heq : {x : EuclideanSpace ℝ (Fin S.dimension) |
      ∀ z, eval x.ofLp (S.captureEquations S.dimension e rfl (S.state.grain (cube y)) z)=0}=
      S.zeroSet (S.state.grain (cube y)) := by
    ext x
    exact S.captureEquations_zero S.dimension e rfl he _ x
  rw [heq]
  exact hs.2.2 y hy j

end PolynomialArchiveSnapshot
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

def coordinateState (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n : ℕ) (hn : b+c=n) (i : Fin H.polynomialSnapshots.length) : FrozenGeometryState n k T C O :=
  (H.polynomialSnapshots[i]).coordinateState n
    ((H.polynomialSnapshots_dimension _ (List.getElem_mem i.isLt)).trans hn)

theorem coordinateState_certified (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n : ℕ) (hn : b+c=n) (i : Fin H.polynomialSnapshots.length) :
    BufferedArchiveSnapshot.Certified I.δ I.tube (BufferedArchiveSnapshot.ofState (H.coordinateState n hn i)) := by
  apply PolynomialArchiveSnapshot.coordinateState_certified
  apply H.snapshots_certified
  rw [← H.polynomialSnapshots_physical]
  exact List.mem_map.mpr ⟨_,List.getElem_mem i.isLt,rfl⟩

theorem coordinateState_localized (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n : ℕ) (hn : b+c=n) (i : Fin H.polynomialSnapshots.length) :
    BufferedArchiveSnapshot.Localized I.δ I.cube (BufferedArchiveSnapshot.ofState (H.coordinateState n hn i)) := by
  apply PolynomialArchiveSnapshot.coordinateState_localized
  apply H.snapshots_localized
  rw [← H.polynomialSnapshots_physical]
  exact List.mem_map.mpr ⟨_,List.getElem_mem i.isLt,rfl⟩

theorem coordinateState_ancestor (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n : ℕ) (hn : b+c=n) (i j : Fin H.polynomialSnapshots.length) (hij : i≤j) :
    BufferedArchiveSnapshot.PhysicalAncestor I.δ
      (BufferedArchiveSnapshot.ofState (H.coordinateState n hn i))
      (BufferedArchiveSnapshot.ofState (H.coordinateState n hn j)) := by
  apply PolynomialArchiveSnapshot.coordinateState_ancestor
  obtain rfl | hlt := Fin.eq_or_lt_of_le hij
  · exact BufferedArchiveSnapshot.PhysicalAncestor.refl _ _
  have hp := H.snapshots_physical_ancestry.2
  rw [← H.polynomialSnapshots_physical,List.pairwise_map] at hp
  exact hp.rel_get_of_lt hlt

theorem coordinateState_radius_controlled (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n : ℕ) (hn : b+c=n) (i : Fin H.polynomialSnapshots.length)
    (hroot : BufferedArchiveSnapshot.RadiusControlled A I.δ (BufferedArchiveSnapshot.ofState I.W)) :
    BufferedArchiveSnapshot.RadiusControlled A I.δ (BufferedArchiveSnapshot.ofState (H.coordinateState n hn i)) := by
  apply PolynomialArchiveSnapshot.coordinateState_radius_controlled
  apply H.snapshots_radius_controlled hroot
  rw [← H.polynomialSnapshots_physical]
  exact List.mem_map.mpr ⟨_,List.getElem_mem i.isLt,rfl⟩

theorem coordinateState_root (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n : ℕ) (hn : b+c=n) (i : Fin H.polynomialSnapshots.length) :
    BufferedArchiveSnapshot.PhysicalAncestor I.δ
      (BufferedArchiveSnapshot.ofState (hn ▸ I.W))
      (BufferedArchiveSnapshot.ofState (H.coordinateState n hn i)) := by
  apply PolynomialArchiveSnapshot.coordinateState_ancestor (PolynomialArchiveSnapshot.ofData I)
    (H.polynomialSnapshots[i]) n hn _ I.δ
  apply H.snapshots_physical_ancestry.1
  rw [← H.polynomialSnapshots_physical]
  exact List.mem_map.mpr ⟨_,List.getElem_mem i.isLt,rfl⟩

theorem coordinateState_length (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n : ℕ) (hn : b+c=n) (i : Fin H.polynomialSnapshots.length) (j : Fin k) :
    (H.coordinateState n hn i).length I.δ j=H.captureLengths j i :=
  PolynomialArchiveSnapshot.coordinateState_length _ _ _ _ _

theorem coordinateState_tuples (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n : ℕ) (hn : b+c=n) (i : Fin H.polynomialSnapshots.length) :
    (H.coordinateState n hn i).tuples=(H.polynomialSnapshots[i]).state.tuples :=
  PolynomialArchiveSnapshot.coordinateState_tuples _ _ _

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.PolynomialArchiveSnapshot.coordinateState_capture
#print axioms KakeyaTwoScale.ActualBufferedArchive.coordinateState_ancestor
#print axioms KakeyaTwoScale.ActualBufferedArchive.coordinateState_certified
#print axioms KakeyaTwoScale.ActualBufferedArchive.coordinateState_localized
