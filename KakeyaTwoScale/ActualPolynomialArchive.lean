module
public import KakeyaTwoScale.PolynomialArchiveSnapshot

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale
open PolynomialArchiveSnapshot

namespace FixedAmbientBufferedData
variable {n b c k A B Lh J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]

theorem polynomialSnapshot_toAmbient (I : FixedAmbientBufferedData n b c k A B Lh J s T C O) :
    ofData I.toAmbient = ⟨n,c,J,I.W,I.P,I.K⟩ := by
  have h := I.ambient_eq
  subst n
  rfl
end FixedAmbientBufferedData

namespace AmbientBufferedStageData
variable {b c k A B Lh J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]

theorem nextData_polynomialSnapshot (I : AmbientBufferedStageData b c k A B Lh J s T C O)
    {N : Fin k→ℝ} {P U : ℝ} {a : ℕ}
    (Z : ActualNormalizedBufferedStage I.toInput N P U a) (hb : 1<b) (t : ℕ) (ht : 2≤t) :
    ofData (I.nextData Z hb t ht)=ofStage I Z := by
  rw [nextData,FixedAmbientBufferedData.polynomialSnapshot_toAmbient]
  rfl
end AmbientBufferedStageData

namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

/-- The original algebraic data from the actual recursive construction.
No zero-set sequence or common-grain map is supplied by a caller. -/
def polynomialSnapshots (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    List (PolynomialArchiveSnapshot k T C O) := by
  induction H with
  | zero I P U => exact [ofData I]
  | short I P U _ => exact [ofData I]
  | last I P U Z => exact [ofData I,ofStage I Z]
  | next I P U Z hb ht tail ih => exact ofData I::ih

theorem polynomialSnapshots_physical
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    H.polynomialSnapshots.map physical=H.snapshots := by
  induction H with
  | zero => rfl
  | short => rfl
  | last => rfl
  | next I P U Z hb ht tail ih =>
    change (ofData I).physical::tail.polynomialSnapshots.map physical = _
    rw [ih]
    rfl

/-- Every stored equation family retains its actual degree bound, regularity
and whole-cylinder capture. -/
theorem polynomialSnapshots_sound
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    ∀ S∈H.polynomialSnapshots, Sound I.δ I.cube S := by
  induction H with
  | zero I P U =>
    intro S hS
    change S∈[ofData I] at hS
    rcases List.mem_singleton.mp hS with rfl
    exact ofData_sound I
  | short I P U _ =>
    intro S hS
    change S∈[ofData I] at hS
    rcases List.mem_singleton.mp hS with rfl
    exact ofData_sound I
  | last I P U Z =>
    intro S hS
    change S∈[ofData I,ofStage I Z] at hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact ofData_sound I
    · rcases List.mem_singleton.mp hS with rfl
      exact ofStage_sound I Z
  | next I P U Z hb ht tail ih =>
    intro S hS
    change S∈ofData I::tail.polynomialSnapshots at hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact ofData_sound I
    · simpa only [AmbientBufferedStageData.nextData_delta,AmbientBufferedStageData.nextData_cube] using ih S hS

/-- A single actual ancestor grain is shared by every tuple of a descendant
grain. All its zero-set inclusions follow from preserved equations. -/
theorem polynomialSnapshots_ancestry
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) :
    (∀ S∈H.polynomialSnapshots, Ancestor I.cube (ofData I) S) ∧
    H.polynomialSnapshots.Pairwise (Ancestor I.cube) := by
  induction H with
  | zero I P U =>
    change (∀ S∈[ofData I], Ancestor I.cube (ofData I) S) ∧ _
    exact ⟨fun _ h=>List.mem_singleton.mp h ▸ Ancestor.refl _ _,by simp [polynomialSnapshots]⟩
  | short I P U _ =>
    change (∀ S∈[ofData I], Ancestor I.cube (ofData I) S) ∧ _
    exact ⟨fun _ h=>List.mem_singleton.mp h ▸ Ancestor.refl _ _,by simp [polynomialSnapshots]⟩
  | last I P U Z =>
    change (∀ S∈[ofData I,ofStage I Z], Ancestor I.cube (ofData I) S) ∧
      [ofData I,ofStage I Z].Pairwise (Ancestor I.cube)
    have hz := ofStage_ancestor I Z
    constructor
    · intro S hS
      rcases List.mem_cons.mp hS with rfl | hS
      · exact Ancestor.refl _ _
      · rcases List.mem_singleton.mp hS with rfl
        exact hz
    · simpa [List.pairwise_cons] using hz
  | next I P U Z hb ht tail ih =>
    change (∀ S∈ofData I::tail.polynomialSnapshots, Ancestor I.cube (ofData I) S) ∧
      (ofData I::tail.polynomialSnapshots).Pairwise (Ancestor I.cube)
    have hi : ∀ S∈tail.polynomialSnapshots, Ancestor I.cube (ofStage I Z) S := by
      simpa only [AmbientBufferedStageData.nextData_cube,AmbientBufferedStageData.nextData_polynomialSnapshot] using ih.1
    have hh : ∀ S∈tail.polynomialSnapshots, Ancestor I.cube (ofData I) S :=
      fun S hS=>(ofStage_ancestor I Z).trans (hi S hS)
    refine ⟨?_,List.pairwise_cons.mpr ⟨hh,?_⟩⟩
    · intro S hS
      rcases List.mem_cons.mp hS with rfl | hS
      · exact Ancestor.refl _ _
      · exact hh S hS
    · simpa only [AmbientBufferedStageData.nextData_cube] using ih.2

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.polynomialSnapshots_physical
#print axioms KakeyaTwoScale.ActualBufferedArchive.polynomialSnapshots_sound
#print axioms KakeyaTwoScale.ActualBufferedArchive.polynomialSnapshots_ancestry
