module
public import KakeyaTwoScale.TerminalGridComponents

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

abbrev GridPlaneBank (d q : ℕ) (B : Finset ℤ) :=
  Σ J : {J : Finset (Fin d) // J.card≤q}, (J.val→B)

/-- The bank pays for fixed coordinates only, giving the geometric dimension
exponent q rather than the ambient exponent d. -/
theorem gridPlaneBank_card_le (d q : ℕ) (B : Finset ℤ) (hB : B.Nonempty) :
    Fintype.card (GridPlaneBank d q B)≤2^d*B.card^q := by
  classical
  have hpos : 1≤B.card := hB.card_pos
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _J : {J : Finset (Fin d) // J.card≤q}, B.card^q := by
      apply Finset.sum_le_sum
      intro J _
      simp only [Fintype.card_fun,Fintype.card_coe]
      exact Nat.pow_le_pow_right hpos J.property
    _ = Fintype.card {J : Finset (Fin d) // J.card≤q} * B.card^q := by simp
    _ ≤ 2^d*B.card^q := Nat.mul_le_mul_right _ (by
      have hh := Fintype.card_subtype_le (fun J : Finset (Fin d) => J.card≤q)
      simpa using hh)

def GridPlaneBank.labels {d q : ℕ} {B : Finset ℤ} (p : GridPlaneBank d q B) : Fin d→ℤ :=
  fun j => if hj : j∈p.1.val then (p.2 ⟨j,hj⟩).val else 0

@[simp] theorem GridPlaneBank.labels_mem {d q : ℕ} {B : Finset ℤ}
    (p : GridPlaneBank d q B) (j : Fin d) (hj : j∈p.1.val) :
    p.labels j=(p.2 ⟨j,hj⟩).val := dite_eq_left hj

/-- A terminal face's fixed labels give an actual bounded plane-bank entry. -/
def terminalFacePlane {d q : ℕ} (B : Finset ℤ) (k : Fin d→ℤ)
    (sigma : Fin d→Option Bool) (hq : (gridFaceFixed sigma).card≤q)
    (hB : ∀ j∈gridFaceFixed sigma, gridFaceLabels k sigma j∈B) : GridPlaneBank d q B :=
  ⟨⟨gridFaceFixed sigma,hq⟩,fun j => ⟨gridFaceLabels k sigma j,hB j j.property⟩⟩

theorem terminalFacePlane_plane {d q : ℕ} (B : Finset ℤ) (k : Fin d→ℤ)
    (sigma : Fin d→Option Bool) (hq : (gridFaceFixed sigma).card≤q)
    (hB : ∀ j∈gridFaceFixed sigma, gridFaceLabels k sigma j∈B)
    (a theta : Fin d→ℝ) (h : ℝ) :
    coordinateGridPlane a theta h (terminalFacePlane B k sigma hq hB).labels
      (terminalFacePlane B k sigma hq hB).1.val =
      coordinateGridPlane a theta h (gridFaceLabels k sigma) (gridFaceFixed sigma) := by
  ext x
  change (∀ j∈gridFaceFixed sigma, x j=gridLevel a theta h _ j) ↔ _
  constructor <;> intro hx j hj <;>
    simpa [gridLevel,GridPlaneBank.labels,terminalFacePlane,hj] using hx j hj

end KakeyaTwoScale
#print axioms KakeyaTwoScale.gridPlaneBank_card_le
#print axioms KakeyaTwoScale.terminalFacePlane_plane
