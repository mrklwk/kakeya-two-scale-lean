module
public import KakeyaTwoScale.PolynomialCaptureFormula

@[expose] public section

open Set MvPolynomial
open OAI.Release061 OAI.Release061.SignElimination
noncomputable section
namespace KakeyaTwoScale

/-- Polynomial preimages expressed by compositional scalar certificates. -/
theorem polynomialSignSet_preimage_scalars {X Y ι κ : Type*}
    {c : X→ι→ℝ} {d : Y→κ→ℝ} {S : Set Y}
    (hS : PolynomialSignSet d S) (f : X→Y)
    (hf : ∀ j, PolynomialScalar c (fun x => d (f x) j)) :
    PolynomialSignSet c (f ⁻¹' S) := by
  classical
  choose Q hQ using hf
  exact hS.polynomial_preimage f Q (fun x j => (hQ j x).symm)

/-- Universal vector quantification uses the proved finite projection theorem. -/
theorem polynomialSignSet_forall_vector {X ι : Type*} {n : ℕ} {c : X→ι→ℝ}
    (P : X→(Fin n→ℝ)→Prop)
    (hP : PolynomialSignSet (fun z : X × (Fin n→ℝ) => Sum.elim (c z.1) z.2)
      {z | P z.1 z.2}) : PolynomialSignSet c {x | ∀ y, P x y} := by
  have hh := polynomialSignSet_projection_finite hP.compl
  convert hh.compl using 1
  ext x
  simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomialSignSet_preimage_scalars
#print axioms KakeyaTwoScale.polynomialSignSet_forall_vector
