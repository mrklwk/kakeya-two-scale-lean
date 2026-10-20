module
public import KakeyaTwoScale.TypeClassAsymptotics

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped BigOperators Topology

theorem wordTypeClass_card_mul_on {I A : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq A] (w : I → A) (S : Finset A)
    (hw : ∀ i, w i ∈ S) :
    (wordTypeClass w).card*(∏ a ∈ S, (Fintype.card {i : I // w i = a}).factorial) =
      (Fintype.card I).factorial := by
  have hsub : Finset.univ.image w ⊆ S := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact hw i
  have he : (∏ a ∈ Finset.univ.image w, (Fintype.card {i : I // w i = a}).factorial) =
      ∏ a ∈ S, (Fintype.card {i : I // w i = a}).factorial := by
    apply Finset.prod_subset hsub
    intro a _ ha
    have hz : Fintype.card {i : I // w i = a} = 0 := by
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun i => ha (Finset.mem_image.mpr ⟨i.val,Finset.mem_univ _,i.property⟩)⟩
    simp [hz]
  rw [← he]
  exact wordTypeClass_card_mul_fiber_factorials w

def repeatedWord {I A : Type*} (w : I → A) (k : ℕ) : I × Fin k → A := fun i => w i.1

theorem repeatedWord_fiber_card {I A : Type*} [Fintype I] [DecidableEq A]
    (w : I → A) (k : ℕ) (a : A) :
    Fintype.card {i : I × Fin k // repeatedWord w k i = a} =
      Fintype.card {i : I // w i = a}*k := by
  let e : {i : I × Fin k // repeatedWord w k i = a} ≃ {i : I // w i = a} × Fin k :=
    { toFun := fun i => (⟨i.val.1,i.property⟩,i.val.2)
      invFun := fun i => ⟨(i.1.val,i.2),i.1.property⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  simpa using Fintype.card_congr e

theorem word_symbol_count_sum {I A : Type*} [Fintype I] [DecidableEq A]
    (w : I → A) :
    ∑ a ∈ Finset.univ.image w, Fintype.card {i : I // w i = a} = Fintype.card I := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset I))
    (t := Finset.univ.image w) (f := w) (fun i _ => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  simpa only [Finset.card_univ,Fintype.card_subtype] using h.symm

/-- Exact log cardinality of the constructed repeated type classes. -/
theorem repeated_type_log_card {I A : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq A] (w : I → A) (k : ℕ) :
    Real.log ((wordTypeClass (repeatedWord w k)).card:ℝ) =
      Real.log (((Fintype.card I)*k).factorial:ℝ)-
        ∑ a ∈ Finset.univ.image w, Real.log ((Fintype.card {i : I // w i = a}*k).factorial:ℝ) := by
  have h := wordTypeClass_card_mul_on (repeatedWord w k) (Finset.univ.image w)
    (fun i => Finset.mem_image.mpr ⟨i.1,Finset.mem_univ _,rfl⟩)
  simp only [Fintype.card_prod,Fintype.card_fin,repeatedWord_fiber_card] at h
  have hr : ((wordTypeClass (repeatedWord w k)).card:ℝ)*
      (∏ a ∈ Finset.univ.image w, ((Fintype.card {i : I // w i = a}*k).factorial:ℝ)) =
      (((Fintype.card I)*k).factorial:ℝ) := by exact_mod_cast h
  have hp : (0:ℝ) < (wordTypeClass (repeatedWord w k)).card := by
    exact_mod_cast Finset.card_pos.mpr (wordTypeClass_nonempty _)
  have hl := congrArg Real.log hr
  rw [Real.log_mul (ne_of_gt hp) (by positivity),Real.log_prod (fun a _ => by positivity)] at hl
  linarith

/-- Actual type-class logarithmic cardinalities converge to the entropy
numerator of the empirical symbol law. -/
theorem repeated_type_log_tendsto {I A : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq A] (w : I → A) :
    Tendsto (fun k : ℕ => Real.log ((wordTypeClass (repeatedWord w k)).card:ℝ)/(k:ℝ))
      atTop (𝓝 ((Fintype.card I:ℝ)*Real.log (Fintype.card I)-
        ∑ a ∈ Finset.univ.image w, (Fintype.card {i : I // w i = a}:ℝ)*Real.log (Fintype.card {i : I // w i = a}))) := by
  simpa only [repeated_type_log_card,← Nat.cast_sum,word_symbol_count_sum] using
    multinomial_log_tendsto (Finset.univ.image w) (fun a => Fintype.card {i : I // w i = a})

end KakeyaTwoScale
#print axioms KakeyaTwoScale.wordTypeClass_card_mul_on
#print axioms KakeyaTwoScale.repeatedWord_fiber_card
#print axioms KakeyaTwoScale.word_symbol_count_sum
#print axioms KakeyaTwoScale.repeated_type_log_card
#print axioms KakeyaTwoScale.repeated_type_log_tendsto
