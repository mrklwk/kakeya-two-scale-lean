module
public import KakeyaTwoScale.FlatCylinderSignFormula

@[expose] public section

open Set MvPolynomial
open OAI.Release061 OAI.Release061.SignElimination
noncomputable section
namespace KakeyaTwoScale

/-- Universal containment in a joint polynomial-sign family preserves the
joint format. This quantifies over every cylinder point, not sampled points. -/
theorem cylinder_containment_sign {X ι π : Type*} {d : ℕ}
    (c : X→ι→ℝ) (p : X→π→ℝ) (b u : X→Fin d→ℝ) (L w : X→ℝ)
    (S : Set ((π→ℝ) × (Fin d→ℝ)))
    (hS : PolynomialSignSet (fun z => Sum.elim z.1 z.2) S)
    (hp : ∀ j, PolynomialScalar c (fun z => p z j))
    (hb : ∀ j, PolynomialScalar c (fun z => b z j))
    (hu : ∀ j, PolynomialScalar c (fun z => u z j))
    (hL : PolynomialScalar c L) (hw : PolynomialScalar c w) :
    PolynomialSignSet c {z | ∀ y, flatCylinderFormula (b z) (u z) y (L z) (w z) → (p z,y)∈S} := by
  let c' : X × (Fin d→ℝ) → ι⊕Fin d→ℝ := fun z => Sum.elim (c z.1) z.2
  have lift {f : X→ℝ} (hf : PolynomialScalar c f) : PolynomialScalar c' (fun z => f z.1) :=
    hf.coordinate_preimage Prod.fst Sum.inl (by intros; rfl)
  have hflat := flatCylinderFormula_sign c' (fun z => b z.1) (fun z => u z.1) Prod.snd
    (fun z => L z.1) (fun z => w z.1) (fun j => lift (hb j)) (fun j => lift (hu j))
    (fun j => PolynomialScalar.coordinate (Sum.inr j)) (lift hL) (lift hw)
  have hmember := polynomialSignSet_preimage_scalars hS
    (fun z : X × (Fin d→ℝ) => (p z.1,z.2)) (c := c') (by
      intro j
      rcases j with j|j
      · exact lift (hp j)
      · exact PolynomialScalar.coordinate (Sum.inr j))
  apply polynomialSignSet_forall_vector
  convert hflat.compl.union hmember using 1
  ext z
  simp only [mem_ofPred_eq,mem_union,mem_compl_iff,mem_preimage]
  tauto

end KakeyaTwoScale
#print axioms KakeyaTwoScale.cylinder_containment_sign
