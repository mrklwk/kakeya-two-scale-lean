module
public import KakeyaTwoScale.AmbientPolynomialWall
public import Mathlib.Data.Set.Card

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

/-- The actual nonempty connected components of a polynomial complement,
represented as sets. Representatives are required to lie outside the zero set. -/
def polynomialComplementComponents {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    Set (Set (EuclideanSpace ℝ (Fin n))) :=
  {S | ∃ x, x ∉ ambientPolynomialZeroSet P ∧
    connectedComponentIn (ambientPolynomialZeroSet P)ᶜ x = S}

/-- Those actual complementary components met by the entire affine line. -/
def polynomialLineComponents {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (b u : EuclideanSpace ℝ (Fin n)) : Set (Set (EuclideanSpace ℝ (Fin n))) :=
  {S | ∃ t : ℝ, b+t • u ∉ ambientPolynomialZeroSet P ∧
    connectedComponentIn (ambientPolynomialZeroSet P)ᶜ (b+t • u) = S}

theorem polynomialComplementComponents_nonempty {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : S ∈ polynomialComplementComponents P) :
    S.Nonempty := by
  obtain ⟨x,hx,rfl⟩ := hS
  exact ⟨x,mem_connectedComponentIn hx⟩

theorem polynomialComplementComponents_cover {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    ⋃₀ polynomialComplementComponents P = (ambientPolynomialZeroSet P)ᶜ := by
  ext x
  constructor
  · rintro ⟨S,⟨y,hy,rfl⟩,hx⟩
    exact connectedComponentIn_subset _ _ hx
  · intro hx
    exact ⟨connectedComponentIn (ambientPolynomialZeroSet P)ᶜ x, ⟨x,hx,rfl⟩,
      mem_connectedComponentIn hx⟩

/-- A uniform bound for finite subfamilies proves actual finiteness first.
Thus `ncard` is never used to hide a possibly infinite family. -/
theorem finite_ncard_le_of_finset_bound {α : Type*} (S : Set α) (B : ℕ)
    (h : ∀ F : Finset α, (F : Set α) ⊆ S → F.card ≤ B) :
    S.Finite ∧ S.ncard ≤ B := by
  classical
  have hf : S.Finite := by
    by_contra hinf
    obtain ⟨T,hTS,hT,hcard⟩ := Set.Infinite.exists_subset_ncard_eq hinf (B+1)
    have hb := h hT.toFinset (by simpa using hTS)
    have he : hT.toFinset.card = B+1 := by rwa [← Set.ncard_eq_toFinset_card T hT]
    omega
  refine ⟨hf, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hf]
  exact h hf.toFinset (by simp)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomialComplementComponents_nonempty
#print axioms KakeyaTwoScale.polynomialComplementComponents_cover
#print axioms KakeyaTwoScale.finite_ncard_le_of_finset_bound
