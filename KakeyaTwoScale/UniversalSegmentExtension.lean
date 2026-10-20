module
public import KakeyaTwoScale.UniformSelectedExtension
public import KakeyaTwoScale.PolynomialCaptureFormula

@[expose] public section

open Set MeasureTheory MvPolynomial
open OAI.Release061 OAI.Release061.SignElimination
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- All points obtained by extending a closed segment contained in `E`. -/
def segmentExtension {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : ℝ) (E : Set V) : Set V :=
  {x | ∃ v, ∀ t∈Icc (0:ℝ) 1, x+(t-T) • v∈E}

/-- The extension relation is jointly semialgebraic, including the extension
factor as a real parameter; no coefficient-dependent format is selected. -/
theorem universal_segment_extension_sign {π : Type*} {n : ℕ}
    (S : Set ((π→ℝ) × (Fin n→ℝ)))
    (hS : PolynomialSignSet (fun z => Sum.elim z.1 z.2) S) :
    PolynomialSignSet
      (fun z : ((((π⊕Unit)→ℝ) × (Fin n→ℝ)) × (Fin n→ℝ)) =>
        Sum.elim (Sum.elim z.1.1 z.1.2) z.2)
      {z | ∀ t∈Icc (0:ℝ) 1,
        ((fun i => z.1.1 (Sum.inl i)),z.1.2+(t-z.1.1 (Sum.inr ())) • z.2)∈S} := by
  classical
  let X := ((((π⊕Unit)→ℝ) × (Fin n→ℝ)) × (Fin n→ℝ))
  let c : X → ((π⊕Unit)⊕Fin n)⊕Fin n → ℝ :=
    fun z => Sum.elim (Sum.elim z.1.1 z.1.2) z.2
  let c' : X × ℝ → Option (((π⊕Unit)⊕Fin n)⊕Fin n) → ℝ :=
    fun z o => o.elim z.2 (c z.1)
  let f : X × ℝ → (π→ℝ) × (Fin n→ℝ) := fun z =>
    ((fun i => z.1.1.1 (Sum.inl i)),z.1.1.2+(z.2-z.1.1.1 (Sum.inr ())) • z.1.2)
  have ht : PolynomialScalar c' Prod.snd := PolynomialScalar.coordinate none
  have hT : PolynomialScalar c' (fun z => z.1.1.1 (Sum.inr ())) :=
    PolynomialScalar.coordinate (some (Sum.inl (Sum.inl (Sum.inr ()))))
  have hf (i : π⊕Fin n) : PolynomialScalar c' (fun z => Sum.elim (f z).1 (f z).2 i) := by
    rcases i with i|j
    · exact PolynomialScalar.coordinate (some (Sum.inl (Sum.inl (Sum.inl i))))
    · exact (PolynomialScalar.coordinate (some (Sum.inl (Sum.inr j)))).add
        ((ht.sub hT).mul (PolynomialScalar.coordinate (some (Sum.inr j))))
  choose Q hQ using hf
  have hnear := hS.polynomial_preimage f Q (fun z i => (hQ i z).symm)
  have hguard := ((PolynomialScalar.const (c := c') 0).le ht).inter
    (ht.le (PolynomialScalar.const 1))
  apply polynomialSignSet_forall_real
  convert hguard.compl.union hnear using 1
  ext z
  simp only [mem_ofPred_eq,mem_union,mem_compl_iff,mem_inter_iff,mem_Icc,mem_preimage]
  change (∀ (_ : 0≤z.2 ∧ z.2≤1),f z∈S) ↔ _
  tauto

/-- Uniform extension volume for the entire jointly semialgebraic family.
The constants precede both the family parameters and the extension factor. -/
theorem uniform_segment_extension_volume {π : Type*} (n : ℕ)
    (S : Set ((π→ℝ) × (Fin n→ℝ)))
    (hS : PolynomialSignSet (fun z => Sum.elim z.1 z.2) S) :
    ∃ C : ℝ, 0<C ∧ ∃ M : ℕ, ∀ (p : π→ℝ) (T : ℝ),
      volume (segmentExtension T {x | (p,x)∈S}) ≤
        (ENNReal.ofReal (C*(max 1 |T|)^n)*M)*volume {x | (p,x)∈S} := by
  let A : Set (((((π⊕Unit)→ℝ) × (Fin n→ℝ))) × (Fin n→ℝ)) :=
    {z | ∀ t∈Icc (0:ℝ) 1,
      ((fun i => z.1.1 (Sum.inl i)),z.1.2+(t-z.1.1 (Sum.inr ())) • z.2)∈S}
  obtain ⟨C,hC,M,h⟩ := uniform_semialgebraic_extension_volume n A
    (universal_segment_extension_sign S hS)
  refine ⟨C,hC,M,?_⟩
  intro p T
  simpa only [A,segmentExtension,mem_ofPred_eq,Sum.elim_inl,Sum.elim_inr] using
    h (Sum.elim p (fun _ => T)) T {x | (p,x)∈S} (by intros x v hx t ht; exact hx t ht)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.universal_segment_extension_sign
#print axioms KakeyaTwoScale.uniform_segment_extension_volume
