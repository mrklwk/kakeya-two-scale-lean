module
public import KakeyaTwoScale.RepeatedTypeClasses

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped BigOperators Topology

def empiricalLaw {I A : Type*} [Fintype I] [DecidableEq A] (w : I → A) (a : A) : ℝ :=
  Fintype.card {i : I // w i = a}/(Fintype.card I:ℝ)

theorem empiricalLaw_sum {I A : Type*} [Fintype I] [Nonempty I] [DecidableEq A] (w : I → A) :
    ∑ a ∈ Finset.univ.image w, empiricalLaw w a = 1 := by
  unfold empiricalLaw
  rw [← Finset.sum_div,← Nat.cast_sum,word_symbol_count_sum]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

theorem empiricalLaw_pos {I A : Type*} [Fintype I] [Nonempty I] [DecidableEq A]
    (w : I → A) {a : A} (ha : a ∈ Finset.univ.image w) : 0 < empiricalLaw w a := by
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ha
  have : Nonempty {i : I // w i = a} := ⟨⟨i,hi⟩⟩
  have hp : (0:ℝ) < Fintype.card {i : I // w i = a} := by exact_mod_cast Fintype.card_pos
  have hn : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  exact div_pos hp hn

theorem empirical_entropy_numerator {I A : Type*}
    [Fintype I] [Nonempty I] [DecidableEq A] (w : I → A) :
    (Fintype.card I:ℝ)*finiteEntropy (Finset.univ.image w) (empiricalLaw w) =
      (Fintype.card I:ℝ)*Real.log (Fintype.card I)-
        ∑ a ∈ Finset.univ.image w, (Fintype.card {i : I // w i = a}:ℝ)*Real.log (Fintype.card {i : I // w i = a}) := by
  have hn : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have ht : ∀ a ∈ Finset.univ.image w,
      (Fintype.card I:ℝ)*(empiricalLaw w a*Real.log (empiricalLaw w a)) =
        (Fintype.card {i : I // w i = a}:ℝ)*Real.log (Fintype.card {i : I // w i = a})-
        (Fintype.card {i : I // w i = a}:ℝ)*Real.log (Fintype.card I) := by
    intro a ha
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ha
    have : Nonempty {i : I // w i = a} := ⟨⟨i,hi⟩⟩
    have hc : (0:ℝ) < Fintype.card {i : I // w i = a} := by exact_mod_cast Fintype.card_pos
    unfold empiricalLaw
    rw [Real.log_div (ne_of_gt hc) (ne_of_gt hn)]
    field_simp
  unfold finiteEntropy
  rw [mul_neg,Finset.mul_sum,Finset.sum_congr rfl ht,Finset.sum_sub_distrib,← Finset.sum_mul,
    ← Nat.cast_sum,word_symbol_count_sum]
  ring

/-- A genuine entropy asymptotic for the actual repeated type classes. -/
theorem repeated_type_entropy_tendsto {I A : Type*}
    [Fintype I] [Nonempty I] [DecidableEq I] [DecidableEq A] (w : I → A) :
    Tendsto (fun k : ℕ => Real.log ((wordTypeClass (repeatedWord w k)).card:ℝ)/
      ((Fintype.card I:ℝ)*k)) atTop
      (𝓝 (finiteEntropy (Finset.univ.image w) (empiricalLaw w))) := by
  have hn : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hh := (repeated_type_log_tendsto w).div_const (Fintype.card I:ℝ)
  rw [← empirical_entropy_numerator w,mul_div_cancel_left₀ _ hn] at hh
  convert hh using 1
  funext k
  field_simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.empiricalLaw_sum
#print axioms KakeyaTwoScale.empiricalLaw_pos
#print axioms KakeyaTwoScale.empirical_entropy_numerator
#print axioms KakeyaTwoScale.repeated_type_entropy_tendsto
