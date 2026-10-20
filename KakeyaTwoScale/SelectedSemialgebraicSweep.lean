module
public import KakeyaTwoScale.OpenDomainSweep

@[expose] public section

open Set MeasureTheory MvPolynomial
open OAI.Release061 OAI.Release061.SignElimination
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- A supplied semialgebraic relation produces a genuine selected sweep with
uniform constants before every real parameter value. Its entire eligible slope
projection is counted, including the null exceptional slopes by inner regularity. -/
theorem uniform_selected_semialgebraic_sweep {π : Type*} (n : ℕ)
    (A : Set (((π → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ)))
    (hA : PolynomialSignSet (fun z => Sum.elim (Sum.elim z.1.1 z.1.2) z.2) A) :
    ∃ C : ℝ, 0 < C ∧ ∃ M : ℕ,
      ∃ F : (π → ℝ) → (Fin n → ℝ) → (Fin n → ℝ),
        (∀ p x, (∃ y, ((p,x),y) ∈ A) → ((p,x),F p x) ∈ A) ∧
        ∀ p a L, 0 < L →
          volume {x | ∃ y, ((p,x),y) ∈ A} * ENNReal.ofReal (L^(n+1)) ≤
            (ENNReal.ofReal C * M) * (volume.prod volume)
              (differentiableLineSweep (F p) id {x | ∃ y, ((p,x),y) ∈ A} a L) := by
  obtain ⟨C,hC,hvol⟩ := open_regular_sweep_volume n
  obtain ⟨s,D,F,Q,accept,hF,hQ,hgraph,hreg⟩ := uniform_semialgebraic_selection A hA
  refine ⟨C,hC,2^s*(4*D+1)^n,F,hF,?_⟩
  intro p a L hL
  obtain ⟨U,hU,hUnull,hFU⟩ := hreg p
  let B : Set (Fin n → ℝ) := {x | ∃ y, ((p,x),y) ∈ A}
  have hAp := hA.polynomial_preimage
    (fun z : (Fin n → ℝ) × (Fin n → ℝ) => ((p,z.1),z.2))
    (Sum.elim (Sum.elim (fun i => MvPolynomial.C (p i)) (fun i => X (Sum.inl i)))
      (fun i => X (Sum.inr i)))
    (d := fun z : (Fin n → ℝ) × (Fin n → ℝ) => Sum.elim z.1 z.2)
    (by intro z i; rcases i with (i | i) | i <;> simp)
  have hB : PolynomialSignSet id B := polynomialSignSet_projection_finite (c := id) hAp
  let V := interior B ∩ U
  have hV : IsOpen V := isOpen_interior.inter hU
  have hVB : V ⊆ B := fun x hx => interior_subset hx.1
  have hnull : volume (B \ V) = 0 := by
    apply measure_mono_null _ (measure_union_null (semialgebraic_diff_interior_null B hB) hUnull)
    intro x hx
    by_cases hi : x ∈ interior B
    · exact Or.inr (fun hu => hx.2 ⟨hi,hu⟩)
    · exact Or.inl ⟨hx.1,hi⟩
  have heq : volume V = volume B := measure_eq_measure_of_null_sdiff hVB hnull
  have hh := hvol (F p) V hV (hFU.mono inter_subset_right) a L hL (2^s*(4*D+1)^n) (by
    intro t _ z
    exact sign_graph_open_regular_slice_encard_le (F p) V hV (hFU.mono inter_subset_right)
      (Q p) (hQ p) accept (fun x y => eq_comm.trans (hgraph p x y)) t z)
  rw [heq] at hh
  apply hh.trans
  apply mul_le_mul le_rfl _ zero_le zero_le
  exact measure_mono (image_mono (Set.prod_mono hVB Subset.rfl))

/-- A common target containing the selected segments bounds the whole eligible
slope measure. The target and time interval may depend on every real parameter;
the constants cannot. The containment premise must hold for the fixed interval,
not merely for some interval on each eligible line. -/
theorem uniform_semialgebraic_target_volume {π : Type*} (n : ℕ)
    (A : Set (((π → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ)))
    (hA : PolynomialSignSet (fun z => Sum.elim (Sum.elim z.1.1 z.1.2) z.2) A) :
    ∃ C : ℝ, 0 < C ∧ ∃ M : ℕ, ∀ (p : π → ℝ) (a L : ℝ), 0 < L →
      ∀ E : Set ((Fin n → ℝ) × ℝ),
      (∀ v b, ((p,v),b) ∈ A → ∀ t ∈ Icc a (a+L), (b+t • v,t) ∈ E) →
      volume {v | ∃ b, ((p,v),b) ∈ A} * ENNReal.ofReal (L^(n+1)) ≤
        (ENNReal.ofReal C * M) * (volume.prod volume) E := by
  obtain ⟨C,hC,M,F,hF,hvol⟩ := uniform_selected_semialgebraic_sweep n A hA
  refine ⟨C,hC,M,?_⟩
  intro p a L hL E hE
  apply (hvol p a L hL).trans
  apply mul_le_mul le_rfl _ zero_le zero_le
  apply measure_mono
  rintro _ ⟨⟨v,t⟩,⟨hv,ht⟩,rfl⟩
  exact hE v (F p v) (hF p v hv) t ht

end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_selected_semialgebraic_sweep

#print axioms KakeyaTwoScale.uniform_semialgebraic_target_volume
