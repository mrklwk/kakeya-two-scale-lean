module
public import KakeyaTwoScale.RegularInjectivePartition

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal Function
noncomputable section
namespace KakeyaTwoScale

/-- Differentiability partitions any measurable set of regular points into
countably many measurable, disjoint pieces on which the actual map is injective.
Only derivatives within that very set are required; no global extension is used. -/
theorem regular_injective_partition_within {m : ℕ}
    (f : (Fin m → ℝ) → (Fin m → ℝ))
    (Df : (Fin m → ℝ) → ((Fin m → ℝ) →L[ℝ] (Fin m → ℝ)))
    {R : Set (Fin m → ℝ)} (hR : MeasurableSet R)
    (hf : ∀ x ∈ R, HasFDerivWithinAt f (Df x) R x)
    (hreg : ∀ x ∈ R, (Df x).det ≠ 0) :
    ∃ P : ℕ → Set (Fin m → ℝ),
      (∀ i, MeasurableSet (P i)) ∧ Pairwise (Disjoint on P) ∧
      (⋃ i, P i) = R ∧ (∀ i, InjOn f (P i)) := by
  classical
  let E := Fin m → ℝ
  rcases R.eq_empty_or_nonempty with hE | hE
  · subst R
    exact ⟨fun _ => ∅, by simp, by simp [Pairwise], by simp, by simp⟩
  rcases subsingleton_or_nontrivial E with hsub | hnon
  · let _ := hsub
    refine ⟨fun i => if i=0 then R else ∅, ?_, ?_, ?_, ?_⟩
    · intro i; dsimp only; split_ifs
      · exact hR
      · exact MeasurableSet.empty
    · intro i j hij; by_cases hi : i=0 <;> by_cases hj : j=0 <;> simp_all [Function.onFun]
    · ext x; simp
    · intro i x hx y hy he; exact Subsingleton.elim _ _
  let _ := hnon
  let e (A : E →L[ℝ] E) (hA : A.det ≠ 0) : E ≃L[ℝ] E :=
    (A.toLinearMap.equivOfDetNeZero hA).toContinuousLinearEquiv
  let r (A : E →L[ℝ] E) : ℝ≥0 :=
    if hA : A.det ≠ 0 then ‖((e A hA).symm : E →L[ℝ] E)‖₊⁻¹ / 2 else 1
  have hr : ∀ A, r A ≠ 0 := by
    intro A
    by_cases hA : A.det ≠ 0
    · dsimp only [r]
      rw [dite_eq_left hA]
      exact ne_of_gt (half_pos (inv_pos.mpr (e A hA).nnnorm_symm_pos))
    · dsimp only [r]
      rw [dite_eq_right hA]
      norm_num
  obtain ⟨t,A,hd,ht,hcover,happ,hval⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f R Df
      hf r hr
  refine ⟨fun i => R ∩ t i, fun i => hR.inter (ht i), ?_, ?_, ?_⟩
  · intro i j hij
    exact (hd hij).mono inter_subset_right inter_subset_right
  · ext x
    simp only [mem_iUnion, mem_inter_iff]
    exact ⟨fun ⟨i,hx,hi⟩ => hx, fun hx => by
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover hx)
      exact ⟨i,hx,hi⟩⟩
  · intro i
    obtain ⟨y,hy,he⟩ := hval hE i
    have ha : (A i).det ≠ 0 := he ▸ hreg y hy
    have happro : ApproximatesLinearOn f (e (A i) ha : E →L[ℝ] E) (R ∩ t i) (r (A i)) := happ i
    apply happro.injOn (Or.inr _)
    dsimp [r]
    rw [dite_eq_left ha]
    exact half_lt_self (inv_pos.mpr (e (A i) ha).nnnorm_symm_pos)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.regular_injective_partition_within
