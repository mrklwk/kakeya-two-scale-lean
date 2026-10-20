module
public import KakeyaTwoScale.SemialgebraicSignFormat
public import OAI.Analysis.SymmetricDomains.GenericAlgebraicRamificationUniform
public import KakeyaTwoScale.PolynomialZeroNull

@[expose] public section

open Set MvPolynomial MeasureTheory
open OAI.Release061 OAI.Release061.SignElimination
noncomputable section
namespace KakeyaTwoScale

/-- Choice with a whole graph, extended by zero jointly in all input coordinates. -/
theorem semialgebraic_total_selection {X ι κ : Type*} [Finite κ]
    {c : X → ι → ℝ} {A : Set (X × (κ → ℝ))}
    (hA : PolynomialSignSet (fun z => Sum.elim (c z.1) z.2) A) :
    ∃ f : X → κ → ℝ,
      (∀ x, (∃ y, (x,y) ∈ A) → (x,f x) ∈ A) ∧
      PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
        {z | z.2 = f z.1} := by
  classical
  obtain ⟨f,hf,hgraph⟩ := polynomialSignSet_choice_finite hA
  let D : Set X := {x | ∃ y, (x,y) ∈ A}
  have hD : PolynomialSignSet c D := polynomialSignSet_projection_finite hA
  let g : X → κ → ℝ := fun x => if x ∈ D then f x else 0
  have hDp := hD.coordinate_preimage (fun z : X × (κ → ℝ) => z.1) Sum.inl
    (d := fun z => Sum.elim (c z.1) z.2) (by intros; rfl)
  have hz : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.2 = 0} := by
    have hh := PolynomialSignSet.forall_finite (fun i : κ => fun z : X × (κ → ℝ) => z.2 i = 0)
      (fun i => by
        convert (PolynomialSignSet.zero
          (c := fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
          (MvPolynomial.X (Sum.inr i))) using 1
        ext z
        simp only [mem_ofPred_eq, eval_X, Sum.elim_inr])
    simpa only [funext_iff, Pi.zero_apply] using hh
  refine ⟨g,fun x hx => ?_,?_⟩
  · simpa only [g,ite_eq_left (show x ∈ D from hx)] using hf x hx
  · convert hgraph.union (hDp.compl.inter hz) using 1
    ext z
    by_cases hd : ∃ y, (z.1,y) ∈ A <;> simp [g,D,hd]

/-- Every scalar coordinate of a semialgebraic vector graph is semialgebraic. -/
theorem semialgebraic_coordinate_graph {n k : ℕ}
    (f : (Fin n → ℝ) → (Fin k → ℝ))
    (hf : PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin k → ℝ) => Sum.elim z.1 z.2)
      {z | z.2 = f z.1}) (i : Fin k) :
    PolynomialSignSet id {z : Option (Fin n) → ℝ |
      (fun j => z (some j)) ∈ (univ : Set (Fin n → ℝ)) ∧
      z none = f (fun j => z (some j)) i} := by
  let c : ((Fin n → ℝ) × ℝ) → Option (Fin n) → ℝ :=
    fun z o => o.elim z.2 z.1
  have hg := hf.coordinate_preimage
    (fun z : ((Fin n → ℝ) × ℝ) × (Fin k → ℝ) => (z.1.1,z.2))
    (Sum.elim (fun j => Sum.inl (some j)) Sum.inr)
    (d := fun z => Sum.elim (c z.1) z.2) (by intro z j; cases j <;> rfl)
  have he : PolynomialSignSet (fun z : ((Fin n → ℝ) × ℝ) × (Fin k → ℝ) =>
      Sum.elim (c z.1) z.2) {z | z.2 i = z.1.2} := by
    convert (PolynomialSignSet.zero
      (c := fun z : ((Fin n → ℝ) × ℝ) × (Fin k → ℝ) => Sum.elim (c z.1) z.2)
      (X (Sum.inr i) - X (Sum.inl none))) using 1
    ext z
    simp only [mem_ofPred_eq, map_sub, eval_X, Sum.elim_inr, Sum.elim_inl,
      c, Option.elim_none, sub_eq_zero]
  have hp := polynomialSignSet_projection_finite (hg.inter he)
  have hs := hp.coordinate_preimage
    (fun z : Option (Fin n) → ℝ => ((fun j => z (some j)),z none)) id
    (d := id) (by intro z o; cases o <;> rfl)
  convert hs using 1
  ext z
  simp only [mem_ofPred_eq,mem_univ,true_and,mem_preimage,mem_inter_iff]
  constructor
  · intro h
    exact ⟨f (fun j => z (some j)),rfl,h.symm⟩
  · rintro ⟨y,rfl,h⟩
    exact h.symm

/-- One open, possibly disconnected, conull set suffices; no cell-count loss. -/
theorem semialgebraic_graph_conull_contDiff {n k : ℕ}
    (f : (Fin n → ℝ) → (Fin k → ℝ))
    (hf : PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin k → ℝ) => Sum.elim z.1 z.2)
      {z | z.2 = f z.1}) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ volume Uᶜ = 0 ∧ ContDiffOn ℝ 1 f U := by
  classical
  have hi (i : Fin k) := semialgebraic_function_analytic_off_polynomial univ
    (fun x => f x i) (semialgebraic_coordinate_graph f hf i)
  choose Q hQ hreg using hi
  let P : MvPolynomial (Fin n) ℝ := ∏ i, Q i
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hQ i)
  let U : Set (Fin n → ℝ) := {x | eval x P ≠ 0}
  refine ⟨U, (MvPolynomial.continuous_eval P).isOpen_preimage _ isOpen_ne, ?_, ?_⟩
  · simpa only [U,compl_ofPred,not_not] using polynomial_zero_volume P hP
  · have ha : AnalyticOnNhd ℝ f U := by
      intro x hx
      apply analyticAt_pi_iff.mpr
      intro i
      apply hreg i x (mem_univ _) 
      intro hz
      apply hx
      change eval x (∏ j, Q j) = 0
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hz
    exact ha.contDiffOn ((MvPolynomial.continuous_eval P).isOpen_preimage _ isOpen_ne).uniqueDiffOn

/-- Discarding the boundary of a semialgebraic parameter domain costs zero measure. -/
theorem semialgebraic_diff_interior_null {n : ℕ} (D : Set (Fin n → ℝ))
    (hD : PolynomialSignSet id D) : volume (D \ interior D) = 0 := by
  obtain ⟨P,hP,hzero⟩ := hD.frontier_polynomial continuous_id
  apply measure_mono_null _ (polynomial_zero_volume P hP)
  intro x hx
  exact hzero x ⟨subset_closure hx.1,hx.2⟩

/-- The selected section is C1 on an open subset of the actual eligible domain,
with exactly null omitted mass. No uniform bound on the number of components is needed. -/
theorem semialgebraic_selection_on_open_domain {n k : ℕ}
    (A : Set ((Fin n → ℝ) × (Fin k → ℝ)))
    (hA : PolynomialSignSet (fun z => Sum.elim z.1 z.2) A) :
    ∃ f : (Fin n → ℝ) → (Fin k → ℝ),
      (∀ x, (∃ y, (x,y) ∈ A) → (x,f x) ∈ A) ∧
      PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin k → ℝ) => Sum.elim z.1 z.2)
        {z | z.2 = f z.1} ∧
      ∃ U : Set (Fin n → ℝ), IsOpen U ∧ U ⊆ {x | ∃ y, (x,y) ∈ A} ∧
        volume ({x | ∃ y, (x,y) ∈ A} \ U) = 0 ∧ ContDiffOn ℝ 1 f U := by
  obtain ⟨f,hf,hg⟩ := semialgebraic_total_selection (c := id) hA
  obtain ⟨V,hV,hnull,hreg⟩ := semialgebraic_graph_conull_contDiff f hg
  let D : Set (Fin n → ℝ) := {x | ∃ y, (x,y) ∈ A}
  have hD : PolynomialSignSet id D := SignElimination.polynomialSignSet_projection_finite hA
  refine ⟨f,hf,hg,interior D ∩ V,isOpen_interior.inter hV,
    fun x hx => interior_subset hx.1,?_,hreg.mono inter_subset_right⟩
  apply measure_mono_null _ (measure_union_null (semialgebraic_diff_interior_null D hD) hnull)
  intro x hx
  by_cases hi : x ∈ interior D
  · exact Or.inr (fun hv => hx.2 ⟨hi,hv⟩)
  · exact Or.inl ⟨hx.1,hi⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.semialgebraic_total_selection
#print axioms KakeyaTwoScale.semialgebraic_graph_conull_contDiff

#print axioms KakeyaTwoScale.semialgebraic_selection_on_open_domain
