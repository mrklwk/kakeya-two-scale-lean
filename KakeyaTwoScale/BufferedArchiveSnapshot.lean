module
public import KakeyaTwoScale.ActualNormalizedStageGeometry

@[expose] public section

open Set
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- A complete immutable physical level. Ambient dimensions are recorded
explicitly while dimension-transition coordinate casts are being assembled.
The original tuple, cube and tube-ID types remain fixed at every level. -/
structure BufferedArchiveSnapshot (k : ℕ) (T C O : Type) where
  dimension : ℕ
  state : FrozenGeometryState dimension k T C O

namespace BufferedArchiveSnapshot
variable {k : ℕ} {T C O : Type}

def ofState {n : ℕ} (S : FrozenGeometryState n k T C O) : BufferedArchiveSnapshot k T C O := ⟨n,S⟩

def axial (S : BufferedArchiveSnapshot k T C O) (δ : ℝ) (j : Fin k) : ℝ :=
  S.state.length δ j*(S.state.count j:ℝ)

/-- Snapshot data includes every record and every grain in the
frozen state, rather than only the grains represented at the final level. -/
theorem ofState_records {n : ℕ} (S : FrozenGeometryState n k T C O) (j : Fin k) :
    (ofState S).state.records j=S.records j := rfl

end BufferedArchiveSnapshot
end KakeyaTwoScale
