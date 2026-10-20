module
public import KakeyaTwoScale.VariableParentCounts

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Exact axial sum split by the actual represented physical parent.
Records are deduplicated before summation, independently of tuple multiplicity. -/
theorem axial_record_sum_fibers {P A : Type*} [DecidableEq P] [DecidableEq A]
    (records : Finset (P × A)) (ell : P × A → ℝ) :
    (∑ record ∈ records, ell record) =
      ∑ p ∈ records.image Prod.fst, ∑ record ∈ records.filter (fun r => r.1=p), ell record := by
  symm
  exact Finset.sum_fiberwise_of_maps_to (fun r hr => Finset.mem_image_of_mem Prod.fst hr) ell

/-- Local budgets on exact represented fibers aggregate with no sign
assumption: this is exact finite partitioning followed by summation. -/
theorem axial_record_sum_le {P A : Type*} [DecidableEq P] [DecidableEq A]
    (records : Finset (P × A)) (ell : P × A → ℝ) (L : P → ℝ)
    (hbudget : ∀ p ∈ records.image Prod.fst,
      (∑ record ∈ records.filter (fun r => r.1=p), ell record) ≤ L p) :
    (∑ record ∈ records, ell record) ≤ ∑ p ∈ records.image Prod.fst, L p := by
  rw [axial_record_sum_fibers]
  exact Finset.sum_le_sum hbudget

/-- Actual tuple-selected children inherit the sum of the represented parent
budgets. Extra allowed starts are permitted, with their actual nonnegative
lengths; no geometry or cumulative budget is assumed as a conclusion. -/
theorem variable_child_axial_sum_le {T P A : Type*}
    [DecidableEq T] [DecidableEq P] [DecidableEq A]
    (Y Z : Finset T) (parent : T → P) (start : T → A) (starts : P → Finset A)
    (ell : P × A → ℝ) (L : P → ℝ)
    (hZY : Z ⊆ Y) (hmem : ∀ y ∈ Z, start y ∈ starts (parent y))
    (hnonneg : ∀ p ∈ Y.image parent, ∀ a ∈ starts p, 0 ≤ ell (p,a))
    (hbudget : ∀ p ∈ Y.image parent, (∑ a ∈ starts p, ell (p,a)) ≤ L p) :
    (∑ record ∈ Z.image (fun y => (parent y,start y)), ell record) ≤
      ∑ p ∈ Y.image parent, L p := by
  classical
  let families := fun p => (starts p).image (fun a => (p,a))
  let all := (Y.image parent).biUnion families
  have hsub : Z.image (fun y => (parent y,start y)) ⊆ all := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_biUnion.mpr ⟨parent y,Finset.mem_image_of_mem parent (hZY hy),
      Finset.mem_image_of_mem (fun a => (parent y,a)) (hmem y hy)⟩
  have hdis : (↑(Y.image parent) : Set P).PairwiseDisjoint families := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro record hr hs
    obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hr
    obtain ⟨b,hb,heb⟩ := Finset.mem_image.mp hs
    exact hpq (congrArg Prod.fst (hea.trans heb.symm))
  calc
    _ ≤ ∑ record ∈ all, ell record := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro record hr _
      obtain ⟨p,hp,hr⟩ := Finset.mem_biUnion.mp hr
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hr
      exact hnonneg p hp a ha)
    _ = ∑ p ∈ Y.image parent, ∑ a ∈ starts p, ell (p,a) := by
      rw [Finset.sum_biUnion hdis]
      apply Finset.sum_congr rfl
      intro p hp
      exact Finset.sum_image (fun a _ b _ h => congrArg Prod.snd h)
    _ ≤ _ := Finset.sum_le_sum hbudget

/-- Cumulative conservation along already represented generations. The only
step premise is the independently proved local aggregated budget, not an
assumed final ancestor bound. -/
theorem axial_generation_sum_le_root {R : ℕ → Type*}
    (records : ∀ k, Finset (R k)) (ell : ∀ k, R k → ℝ)
    (hstep : ∀ k, (∑ r ∈ records (k+1), ell (k+1) r) ≤ ∑ r ∈ records k, ell k r)
    (depth : ℕ) :
    (∑ r ∈ records depth, ell depth r) ≤ ∑ r ∈ records 0, ell 0 r := by
  induction depth with
  | zero => exact le_rfl
  | succ k ih => exact (hstep k).trans ih

end KakeyaTwoScale
#print axioms KakeyaTwoScale.axial_record_sum_fibers
#print axioms KakeyaTwoScale.axial_record_sum_le
#print axioms KakeyaTwoScale.variable_child_axial_sum_le
#print axioms KakeyaTwoScale.axial_generation_sum_le_root
