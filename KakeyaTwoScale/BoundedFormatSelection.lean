module
public import KakeyaTwoScale.UniformSemialgebraicSelection

@[expose] public section

open Set MvPolynomial MeasureTheory
open OAI.Release061 OAI.Release061.SignElimination
noncomputable section
namespace KakeyaTwoScale

/-- A fixed finite monomial box containing every degree-at-most-d support. -/
def selectionMonomialBox (ν : Type*) [Fintype ν] (d : ℕ) : Finset (ν →₀ ℕ) := by
  classical
  exact Finset.univ.image (fun e : ν → Fin (d+1) =>
    Finsupp.equivFunOnFinite.symm (fun i => (e i).val))

theorem support_subset_selectionMonomialBox {ν : Type*} [Fintype ν]
    (d : ℕ) (p : MvPolynomial ν ℝ) (hp : p.totalDegree ≤ d) :
    p.support ⊆ selectionMonomialBox ν d := by
  classical
  intro e he
  let a : ν → Fin (d+1) := fun i => ⟨e i, Nat.lt_succ_of_le
    ((le_degreeOf_of_mem_support i he).trans ((degreeOf_le_totalDegree p i).trans hp))⟩
  exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,by ext i; rfl⟩

def universalSelectionAtom {n k s : ℕ} (T : Finset ((Fin n ⊕ Fin k) →₀ ℕ))
    (j : Fin s) :
    MvPolynomial (((Fin s × ((Fin n ⊕ Fin k) →₀ ℕ)) ⊕ Fin n) ⊕ Fin k) ℝ :=
  ∑ e ∈ T, X (Sum.inl (Sum.inl (j,e))) *
    ∏ i ∈ e.support, (X (Sum.elim (fun a => Sum.inl (Sum.inr a)) Sum.inr i)) ^ e i

theorem universalSelectionAtom_eval {n k s : ℕ}
    (T : Finset ((Fin n ⊕ Fin k) →₀ ℕ)) (P : Fin s → MvPolynomial (Fin n ⊕ Fin k) ℝ)
    (hP : ∀ j, (P j).support ⊆ T) (j : Fin s) (x : Fin n → ℝ) (y : Fin k → ℝ) :
    eval (Sum.elim (Sum.elim (fun q : Fin s × ((Fin n ⊕ Fin k) →₀ ℕ) => (P q.1).coeff q.2) x) y)
      (universalSelectionAtom T j) = eval (Sum.elim x y) (P j) := by
  classical
  simp only [universalSelectionAtom,map_sum,map_mul,eval_X,Sum.elim_inl,map_prod,map_pow]
  have he (i : Fin n ⊕ Fin k) :
      Sum.elim (Sum.elim (fun q : Fin s × ((Fin n ⊕ Fin k) →₀ ℕ) => (P q.1).coeff q.2) x) y
        (Sum.elim (fun a => Sum.inl (Sum.inr a)) Sum.inr i) = Sum.elim x y i := by
    cases i <;> rfl
  simp_rw [he]
  rw [eval_eq]
  symm
  apply Finset.sum_subset (hP j)
  intro e _ he
  simp only [notMem_support_iff.mp he,zero_mul]

/-- Uniform bounded-format selection, with no relation/section existence premise.
For fixed input dimensions, number of atoms, degree bound and Boolean rule, the
output atom count and degree are fixed BEFORE the input polynomial coefficients. -/
theorem bounded_format_selection (n k s d : ℕ)
    (W : (Fin s → SignType) → Prop) :
    ∃ b D : ℕ,
      ∀ P : Fin s → MvPolynomial (Fin n ⊕ Fin k) ℝ,
        (∀ j, (P j).totalDegree ≤ d) →
        ∃ f : (Fin n → ℝ) → (Fin k → ℝ),
          ∃ Q : Fin b → MvPolynomial (Fin k ⊕ Fin n) ℝ,
            ∃ accept : (Fin b → SignType) → Prop,
              (∀ x, (∃ y, W (fun j => SignType.sign (eval (Sum.elim x y) (P j)))) →
                W (fun j => SignType.sign (eval (Sum.elim x (f x)) (P j)))) ∧
              (∀ j, (Q j).totalDegree ≤ D) ∧
              (∀ x y, y = f x ↔ accept (fun j => SignType.sign (eval (Sum.elim y x) (Q j)))) ∧
              ∃ U : Set (Fin n → ℝ), IsOpen U ∧ volume Uᶜ = 0 ∧ ContDiffOn ℝ 1 f U := by
  classical
  let T := selectionMonomialBox (Fin n ⊕ Fin k) d
  let π := Fin s × ((Fin n ⊕ Fin k) →₀ ℕ)
  let c : (((π → ℝ) × (Fin n → ℝ)) × (Fin k → ℝ)) → ((π ⊕ Fin n) ⊕ Fin k) → ℝ :=
    fun z => Sum.elim (Sum.elim z.1.1 z.1.2) z.2
  let A : Set (((π → ℝ) × (Fin n → ℝ)) × (Fin k → ℝ)) :=
    {z | W (fun j => SignType.sign (eval (c z) (universalSelectionAtom T j)))}
  have hA : PolynomialSignSet c A := by
    have h := polynomialSignSet_finite_signs (c := c) PolynomialSignSet.univ
      (fun j z => eval (c z) (universalSelectionAtom T j))
      (fun j => RationalOn.polynomial (universalSelectionAtom T j)) W
    simpa only [univ_inter] using h
  obtain ⟨b,D,F,Q,accept,hF,hQ,hgraph,hreg⟩ := uniform_semialgebraic_selection A hA
  refine ⟨b,D,?_⟩
  intro P hP
  let a : π → ℝ := fun q => (P q.1).coeff q.2
  have hs (j : Fin s) : (P j).support ⊆ T := support_subset_selectionMonomialBox d (P j) (hP j)
  have he (x : Fin n → ℝ) (y : Fin k → ℝ) :
      ((a,x),y) ∈ A ↔ W (fun j => SignType.sign (eval (Sum.elim x y) (P j))) := by
    change W _ ↔ W _
    change W (fun j => SignType.sign (eval (Sum.elim (Sum.elim a x) y) (universalSelectionAtom T j))) ↔ _
    apply iff_of_eq
    apply congrArg W
    funext j
    exact congrArg SignType.sign (universalSelectionAtom_eval T P hs j x y)
  refine ⟨F a,Q a,accept,?_,hQ a,hgraph a,hreg a⟩
  intro x hx
  apply (he x (F a x)).mp
  apply hF a x
  obtain ⟨y,hy⟩ := hx
  exact ⟨y,(he x y).mpr hy⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.bounded_format_selection
