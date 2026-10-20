module
public import KakeyaTwoScale.GrainOriginalMultiplicity

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
namespace FrozenGeometryState

/-- Each distinct original in an actual grain has a witness in the ORIGINAL
stored tuple relation. Choosing these witnesses never regenerates incidences. -/
theorem grain_original_owned_witness {n k : ℕ} {T C O : Type} [DecidableEq O]
    (S : FrozenGeometryState n k T C O) (cube : T→C) (g : S.Grain) (j : Fin k)
    (o : O) (ho : o∈(S.grainRecords cube g j).image (S.original j)) :
    ∃ y∈S.tuples, S.grain (cube y)=g ∧ S.original j (S.parent y j)=o := by
  classical
  obtain ⟨record,hr,he⟩ := Finset.mem_image.mp ho
  obtain ⟨y,hy,hparent⟩ := Finset.mem_image.mp hr
  have hy' := Finset.mem_filter.mp hy
  exact ⟨y,hy'.1,hy'.2,hparent ▸ he⟩

/-- Simultaneous representatives are indexed by original identifiers, never by
possibly repeated descendant records. -/
theorem grain_original_owned_representatives {n k : ℕ} {T C O : Type} [DecidableEq O]
    (S : FrozenGeometryState n k T C O) (cube : T→C) (g : S.Grain) (j : Fin k) :
    ∃ y : {o // o∈(S.grainRecords cube g j).image (S.original j)}→T,
      ∀ o, y o∈S.tuples ∧ S.grain (cube (y o))=g ∧ S.original j (S.parent (y o) j)=o.val := by
  classical
  have hh (o : {o // o∈(S.grainRecords cube g j).image (S.original j)}) :=
    S.grain_original_owned_witness cube g j o.val o.property
  choose y hy using hh
  exact ⟨y,hy⟩

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.grain_original_owned_witness
#print axioms KakeyaTwoScale.FrozenGeometryState.grain_original_owned_representatives
