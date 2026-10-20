module
public import KakeyaTwoScale.ActualMassToLength
public import KakeyaTwoScale.ActualBufferedArchive
public import KakeyaTwoScale.BufferedSnapshotAncestry

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace FrozenGeometryState

/-- Transport full actual validity while retaining the literal physical snapshot. -/
theorem exists_valid_same_snapshot {m n k : ℕ} {T C O : Type}
    (S : FrozenGeometryState m k T C O) (hmn : m=n)
    (Y₀ : Finset T) (cube : T→C) (tube : T→Fin k→O)
    (Q : C→Set (EuclideanSpace ℝ (Fin m)))
    (Q' : C→Set (EuclideanSpace ℝ (Fin n))) (hQ : HEq Q Q') (δ : ℝ)
    (hv : S.Valid Y₀ cube tube Q δ) :
    ∃ S' : FrozenGeometryState n k T C O,
      BufferedArchiveSnapshot.ofState S'=BufferedArchiveSnapshot.ofState S ∧
      S'.Valid Y₀ cube tube Q' δ := by
  subst n
  have he : Q=Q' := eq_of_heq hQ
  subst Q'
  exact ⟨S,rfl,hv⟩

end FrozenGeometryState
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O}
    {P U : ℝ} {fuel : ℕ}

/-- Every actual archive snapshot has full validity in the root coordinates.
Validity is extracted from the constructors, never supplied as a new premise. -/
theorem snapshots_valid_in_coordinates
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n : ℕ) (hn : b+c=n) (Q : C→Set (EuclideanSpace ℝ (Fin n)))
    (hQ : HEq I.Q Q) :
    ∀ X∈H.snapshots, ∃ S : FrozenGeometryState n k T C O,
      BufferedArchiveSnapshot.ofState S=X ∧ S.Valid I.Y₀ I.cube I.tube Q I.δ := by
  induction H with
  | zero I P U =>
    intro X hX
    change X∈[BufferedArchiveSnapshot.ofState I.W] at hX
    rcases List.mem_singleton.mp hX with rfl
    exact I.W.exists_valid_same_snapshot hn _ _ _ _ _ hQ _ I.valid
  | short I P U hs =>
    intro X hX
    change X∈[BufferedArchiveSnapshot.ofState I.W] at hX
    rcases List.mem_singleton.mp hX with rfl
    exact I.W.exists_valid_same_snapshot hn _ _ _ _ _ hQ _ I.valid
  | last I P U Z =>
    intro X hX
    change X∈[BufferedArchiveSnapshot.ofState I.W,BufferedArchiveSnapshot.ofState Z.state] at hX
    rcases List.mem_cons.mp hX with rfl | hX
    · exact I.W.exists_valid_same_snapshot hn _ _ _ _ _ hQ _ I.valid
    · rcases List.mem_singleton.mp hX with rfl
      have hv : Z.state.Valid I.Y₀ I.cube I.tube I.Q I.δ := by
        have hz := Z.valid
        change Z.state.Valid I.Y₀ I.cube I.tube (fun q => physicalCoordinateCube (I.toInput.Q q)) I.δ at hz
        simpa only [AmbientBufferedStageData.toInput_physicalCube] using hz
      exact Z.state.exists_valid_same_snapshot hn _ _ _ _ _ hQ _ hv
  | next I P U Z hb ht tail ih =>
    intro X hX
    change X∈BufferedArchiveSnapshot.ofState I.W::tail.snapshots at hX
    rcases List.mem_cons.mp hX with rfl | hX
    · exact I.W.exists_valid_same_snapshot hn _ _ _ _ _ hQ _ I.valid
    · obtain ⟨S,hS,hv⟩ := ih (by omega) ((I.nextData_cubes_HEq Z hb t ht).trans hQ) X hX
      refine ⟨S,hS,?_⟩
      simpa only [AmbientBufferedStageData.nextData_Y₀,AmbientBufferedStageData.nextData_cube,
        AmbientBufferedStageData.nextData_tube,AmbientBufferedStageData.nextData_δ] using hv

/-- Actual archived mass-to-length, uniform before the precision, root,
horizon, snapshot, and original population. The normalized retention hypothesis
is explicit and must include any root determinant-band density loss. -/
theorem exists_archive_mass_to_length (n : ℕ) :
    ∃ Bgrid : ℕ, 0 < Bgrid ∧
    ∀ {k A B Lh a t b c J s : ℕ} {T O : Type} [DecidableEq T] [DecidableEq O],
    ∀ {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T (Fin n→ℤ) O}
      {P U : ℝ} {fuel : ℕ},
    ∀ (H : ActualBufferedArchive k A B Lh a t T (Fin n→ℤ) O N I P U fuel),
      b+c=n → HEq I.Q (fun z : Fin n→ℤ => (WithLp.ofLp ⁻¹' gridCell I.δ z : Set (EuclideanSpace ℝ (Fin n)))) →
    ∀ X∈H.snapshots, ∀ (available : Fin k→(Fin n→ℤ)→Finset O),
      (∀ y∈I.Y₀, ∀ l, I.tube y l∈available l (I.cube y)) →
      (∀ y∈I.Y₀, ∀ z∈I.Y₀, I.cube y=I.cube z → I.tube y=I.tube z → y=z) →
    ∀ (μ : Fin k→ℝ), (∀ l, 0<μ l) →
      (∀ q∈I.cubes, ∀ l, ((available l q).card:ℝ)≤μ l) →
    ∀ η : ℝ, 0≤η →
      η*(I.cubes.card:ℝ)*(∏ l, μ l)^I.alpha ≤
        tupleCubeMass X.state.tuples I.cube I.cubes I.alpha →
    ∀ j : Fin k,
      η^(1/I.alpha)*(I.cubes.card:ℝ)*μ j*I.δ ≤
        (Bgrid:ℝ)*X.state.length I.δ j*(X.state.count j:ℝ) := by
  obtain ⟨Bgrid,hB,hmain⟩ := exists_actual_mass_to_length n
  refine ⟨Bgrid,hB,?_⟩
  intro k A B Lh a t b c J s T O _ _ N I P U fuel H hn hQ X hX available hmem hinj μ hμ hbound η hη hmass j
  obtain ⟨S,hS,hvalid⟩ := H.snapshots_valid_in_coordinates n hn _ hQ X hX
  subst X
  have hne : I.cubes.Nonempty := by
    obtain ⟨y,hy⟩ := I.nonempty
    exact ⟨I.cube y,I.support y (I.valid.1 hy)⟩
  exact hmain S I.Y₀ I.cube I.tube I.δ I.width_pos hvalid I.cubes hne
    available hmem hinj μ hμ hbound I.alpha η I.exponent_pos I.exponent_le_one hη hmass j

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.exists_valid_same_snapshot
#print axioms KakeyaTwoScale.ActualBufferedArchive.snapshots_valid_in_coordinates
#print axioms KakeyaTwoScale.ActualBufferedArchive.exists_archive_mass_to_length
