module
public import KakeyaTwoScale.ActualActivePrefix
public import KakeyaTwoScale.ArchiveCoordinateState

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
theorem PolynomialArchiveSnapshot.coordinateState_physical {k : ℕ} {T Q O : Type}
    (S : PolynomialArchiveSnapshot k T Q O) (n : ℕ) (hd : S.dimension=n) :
    BufferedArchiveSnapshot.ofState (S.coordinateState n hd)=S.physical := by
  subst n
  rfl

namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T Q O : Type} [DecidableEq T] [DecidableEq Q]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T Q O}
    {P U : ℝ} {fuel : ℕ}

theorem polynomialSnapshots_length_eq (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel) :
    H.polynomialSnapshots.length=H.drops+1 := by
  have hh := congrArg List.length H.polynomialSnapshots_physical
  simpa only [List.length_map,H.snapshots_length] using hh

def polynomialIndex (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (r : ℕ) (hr : r≤H.drops) : Fin H.polynomialSnapshots.length :=
  ⟨r,by rw [H.polynomialSnapshots_length_eq]; omega⟩

theorem entryAt_polynomial_physical (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (r : ℕ) (hr : r≤H.drops) :
    (H.polynomialSnapshots[H.polynomialIndex r hr]).physical=(H.entryAt r hr).snapshot := by
  rw [H.entryAt_snapshot,H.snapshotAt_eq r hr]
  have hh := congrArg (fun l : List (BufferedArchiveSnapshot k T Q O) => l[r]?) H.polynomialSnapshots_physical
  have hp : r<H.polynomialSnapshots.length := (H.polynomialIndex r hr).isLt
  have hs : r<H.snapshots.length := by rw [H.snapshots_length]; omega
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hp,List.getElem?_eq_getElem hs,
    Option.map_some,Option.some.injEq,polynomialIndex,Fin.getElem_fin] using hh

theorem entryAt_capture_length (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (r : ℕ) (hr : r≤H.drops) (j : Fin k) :
    (H.entryAt r hr).snapshot.state.length I.δ j=H.captureLengths j (H.polynomialIndex r hr) := by
  rw [←H.entryAt_polynomial_physical r hr]
  rfl

theorem entryAt_length_antitone (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (i r : ℕ) (hi : i≤r) (hr : r≤H.drops) (j : Fin k) :
    (H.entryAt r hr).snapshot.state.length I.δ j≤
      (H.entryAt i (hi.trans hr)).snapshot.state.length I.δ j := by
  rw [H.entryAt_capture_length,H.entryAt_capture_length]
  exact H.captureLengths_antitone j hi

/-- A family long at the endpoint is active at every earlier level of that
same family. No choice of a different family is made along the prefix. -/
theorem entryAt_active_of_long (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (i r : ℕ) (hi : i≤r) (hr : r≤H.drops) (j : Fin k)
    (hlong : I.δ<(H.entryAt r hr).snapshot.state.length I.δ j) :
    0<(H.entryAt i (hi.trans hr)).snapshot.state.height j := by
  have h := H.entryAt_length_antitone i r hi hr j
  by_contra hz
  have he : (H.entryAt i (hi.trans hr)).snapshot.state.height j=0 := by omega
  simp only [FrozenGeometryState.length,he,pow_zero,mul_one] at h
  exact (not_lt_of_ge h) hlong

theorem coordinateState_entryAt (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (n : ℕ) (hn : b+c=n) (r : ℕ) (hr : r≤H.drops) :
    BufferedArchiveSnapshot.ofState (H.coordinateState n hn (H.polynomialIndex r hr))=
      (H.entryAt r hr).snapshot := by
  rw [←H.entryAt_polynomial_physical r hr]
  exact PolynomialArchiveSnapshot.coordinateState_physical _ _ _


end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.entryAt_polynomial_physical
#print axioms KakeyaTwoScale.ActualBufferedArchive.entryAt_active_of_long
#print axioms KakeyaTwoScale.ActualBufferedArchive.coordinateState_entryAt
