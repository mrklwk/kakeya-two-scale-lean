module
public import KakeyaTwoScale.SemialgebraicSelection

@[expose] public section

open Set MvPolynomial MeasureTheory
open OAI.Release061
noncomputable section
namespace KakeyaTwoScale

/-- The parameter coordinates include all coefficients, scales and auxiliary real data.
The output atom count and degree precede every specialization of these parameters. -/
theorem uniform_semialgebraic_selection {π : Type*} {n k : ℕ}
    (A : Set (((π → ℝ) × (Fin n → ℝ)) × (Fin k → ℝ)))
    (hA : PolynomialSignSet
      (fun z => Sum.elim (Sum.elim z.1.1 z.1.2) z.2) A) :
    ∃ s D : ℕ, ∃ F : (π → ℝ) → (Fin n → ℝ) → (Fin k → ℝ),
      ∃ P : (π → ℝ) → Fin s → MvPolynomial (Fin k ⊕ Fin n) ℝ,
      ∃ accept : (Fin s → SignType) → Prop,
        (∀ a x, (∃ y, ((a,x),y) ∈ A) → ((a,x),F a x) ∈ A) ∧
        (∀ a j, (P a j).totalDegree ≤ D) ∧
        (∀ a x y, y = F a x ↔
          accept (fun j => SignType.sign (eval (Sum.elim y x) (P a j)))) ∧
        ∀ a, ∃ U : Set (Fin n → ℝ),
          IsOpen U ∧ volume Uᶜ = 0 ∧ ContDiffOn ℝ 1 (F a) U := by
  classical
  obtain ⟨f,hf,hgraph⟩ := semialgebraic_total_selection (c := fun z : (π → ℝ) × (Fin n → ℝ) => Sum.elim z.1 z.2) hA
  obtain ⟨s,D,Q,accept,hQ,hdesc⟩ := semialgebraic_sign_format hgraph
  let subst (a : π → ℝ) : (π ⊕ Fin n) ⊕ Fin k → MvPolynomial (Fin k ⊕ Fin n) ℝ :=
    Sum.elim (Sum.elim (fun i => C (a i)) (fun i => X (Sum.inr i)))
      (fun i => X (Sum.inl i))
  let P (a : π → ℝ) (j : Fin s) := (Q j).eval₂ C (subst a)
  have heval (a : π → ℝ) (x : Fin n → ℝ) (y : Fin k → ℝ) (j : Fin s) :
      eval (Sum.elim y x) (P a j) = eval (Sum.elim (Sum.elim a x) y) (Q j) := by
    rw [show P a j = eval₂Hom C (subst a) (Q j) from rfl,
      PolynomialSignSet.eval_substitution]
    congr 2
    funext i
    rcases i with (i | i) | i <;> simp [subst]
  refine ⟨s,D,(fun a x => f (a,x)),P,accept,?_,?_,?_,?_⟩
  · exact fun a x hx => hf (a,x) hx
  · intro a j
    apply le_trans (polynomial_affine_substitution_degree (Q j) (subst a) ?_) (hQ j)
    intro i
    rcases i with (i | i) | i <;> simp [subst]
  · intro a x y
    simpa only [heval,mem_ofPred_eq] using hdesc ((a,x),y)
  · intro a
    apply semialgebraic_graph_conull_contDiff
    have hh := hgraph.polynomial_preimage
      (fun z : (Fin n → ℝ) × (Fin k → ℝ) => ((a,z.1),z.2))
      (Sum.elim (Sum.elim (fun i => C (a i)) (fun i => X (Sum.inl i)))
        (fun i => X (Sum.inr i)))
      (d := fun z : (Fin n → ℝ) × (Fin k → ℝ) => Sum.elim z.1 z.2)
      (by intro z i; rcases i with (i | i) | i <;> simp)
    exact hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_semialgebraic_selection
