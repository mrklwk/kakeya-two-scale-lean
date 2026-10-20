module
public import OAI.Analysis.SymmetricDomains.PolynomialSignSetChoice2
public import KakeyaTwoScale.SignConditionRegularFibers

@[expose] public section

open Set MvPolynomial
open OAI.Release061
noncomputable section
namespace KakeyaTwoScale

/-- An actual finite list of atoms determines membership. No complexity premise. -/
theorem semialgebraic_finite_atoms {X ι : Type*} {c : X → ι → ℝ}
    {S : Set X} (hS : PolynomialSignSet c S) :
    ∃ A : Finset (MvPolynomial ι ℝ), ∀ x y,
      (∀ p ∈ A, SignType.sign (eval (c x) p) = SignType.sign (eval (c y) p)) →
      (x ∈ S ↔ y ∈ S) := by
  classical
  induction hS with
  | zero p =>
    refine ⟨{p}, fun x y h => ?_⟩
    have he := h p (Finset.mem_singleton_self p)
    change eval (c x) p = 0 ↔ eval (c y) p = 0
    simpa only [sign_eq_zero_iff] using
      (show SignType.sign (eval (c x) p) = 0 ↔ SignType.sign (eval (c y) p) = 0 by rw [he])
  | positive p =>
    refine ⟨{p}, fun x y h => ?_⟩
    have he := h p (Finset.mem_singleton_self p)
    change 0 < eval (c x) p ↔ 0 < eval (c y) p
    rw [← sign_eq_one_iff, ← sign_eq_one_iff, he]
  | compl _ ih =>
    obtain ⟨A,hA⟩ := ih
    exact ⟨A, fun x y h => not_congr (hA x y h)⟩
  | union _ _ ih ih' =>
    obtain ⟨A,hA⟩ := ih
    obtain ⟨B,hB⟩ := ih'
    refine ⟨A ∪ B, fun x y h => ?_⟩
    exact or_congr (hA x y (fun p hp => h p (Finset.mem_union_left _ hp)))
      (hB x y (fun p hp => h p (Finset.mem_union_right _ hp)))

/-- Finite sign format extracted before any coordinate specialization. -/
theorem semialgebraic_sign_format {X ι : Type*} {c : X → ι → ℝ}
    {S : Set X} (hS : PolynomialSignSet c S) :
    ∃ s D : ℕ, ∃ P : Fin s → MvPolynomial ι ℝ,
      ∃ accept : (Fin s → SignType) → Prop,
        (∀ j, (P j).totalDegree ≤ D) ∧
        ∀ x, x ∈ S ↔ accept (fun j => SignType.sign (eval (c x) (P j))) := by
  classical
  obtain ⟨A,hA⟩ := semialgebraic_finite_atoms hS
  let e := Fintype.equivFin A
  let P : Fin (Fintype.card A) → MvPolynomial ι ℝ := fun j => (e.symm j).val
  let accept : (Fin (Fintype.card A) → SignType) → Prop :=
    fun v => ∃ x ∈ S, ∀ j, SignType.sign (eval (c x) (P j)) = v j
  refine ⟨Fintype.card A, A.sup totalDegree, P, accept, ?_, ?_⟩
  · intro j
    exact Finset.le_sup (f := totalDegree) (e.symm j).property
  · intro x
    constructor
    · intro hx
      exact ⟨x,hx,fun _ => rfl⟩
    · rintro ⟨y,hy,he⟩
      apply (hA y x ?_).mp hy
      intro p hp
      simpa only [P, e.symm_apply_apply] using he (e ⟨p,hp⟩)

/-- Specializing arbitrary parameters to constants preserves every atom degree. -/
def specializeSignAtom {π ι : Type*} (a : π → ℝ)
    (P : MvPolynomial (π ⊕ ι) ℝ) : MvPolynomial ι ℝ :=
  P.eval₂ C (Sum.elim (fun i => C (a i)) X)

theorem specializeSignAtom_degree {π ι : Type*} (a : π → ℝ)
    (P : MvPolynomial (π ⊕ ι) ℝ) :
    (specializeSignAtom a P).totalDegree ≤ P.totalDegree := by
  apply polynomial_affine_substitution_degree
  intro i
  cases i <;> simp

theorem specializeSignAtom_eval {π ι : Type*} (a : π → ℝ)
    (P : MvPolynomial (π ⊕ ι) ℝ) (x : ι → ℝ) :
    eval x (specializeSignAtom a P) = eval (Sum.elim a x) P := by
  exact PolynomialSignSet.eval_substitution x (Sum.elim (fun i => C (a i)) X) P |>.trans
    (by congr 2; funext i; cases i <;> simp)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.semialgebraic_sign_format
#print axioms KakeyaTwoScale.specializeSignAtom_degree
