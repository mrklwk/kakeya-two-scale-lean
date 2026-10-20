module
public import KakeyaTwoScale.ModularProjectionBound
public import Mathlib.Combinatorics.Additive.Energy

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators Pointwise

def fieldInterval (p m : ℕ) : Finset (ZMod p) := (Finset.range m).image (fun i : ℕ => (i:ZMod p))

def fieldProgression {p : ℕ} (I : Finset (ZMod p)) (d t : ZMod p) : Finset (ZMod p) :=
  I.image (fun i => t+d*i)

theorem fieldInterval_card (p m : ℕ) (hm : m ≤ p) : (fieldInterval p m).card = m := by
  unfold fieldInterval
  rw [Finset.card_image_iff.mpr ?_,Finset.card_range]
  intro i hi j hj he
  have hi' : i < p := lt_of_lt_of_le (Finset.mem_range.mp hi) hm
  have hj' : j < p := lt_of_lt_of_le (Finset.mem_range.mp hj) hm
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hi',Nat.mod_eq_of_lt hj'] using hv

theorem fieldProgression_card {p : ℕ} [Fact p.Prime] (I : Finset (ZMod p))
    (d t : ZMod p) (hd : d ≠ 0) : (fieldProgression I d t).card = I.card := by
  apply Finset.card_image_of_injective
  intro x y he
  exact mul_left_cancel₀ hd (add_left_cancel he)

/-- Exact translation-hit set; the same dilate appears once, avoiding any
ambiguity between an index interval and an already dilated progression. -/
theorem progression_hit_set {p : ℕ} [Fact p.Prime] (A I : Finset (ZMod p)) (d : ZMod p) :
    (Finset.univ.filter (fun t => (A ∩ fieldProgression I d t).Nonempty)) =
      A - I.image (fun i => d*i) := by
  ext t
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.Nonempty,Finset.mem_inter,
    fieldProgression,Finset.mem_image,Finset.mem_sub]
  constructor
  · rintro ⟨x,hx,i,hi,he⟩
    exact ⟨x,hx,d*i,⟨i,hi,rfl⟩,by rw [← he]; ring⟩
  · rintro ⟨x,hx,y,⟨i,hi,rfl⟩,he⟩
    exact ⟨x,hx,i,hi,by rw [← he]; ring⟩

/-- The elementary energy inequality needed before the spectral estimates
in PZ's progression-sumset lemma. Both sides use actual finite sets. -/
theorem progression_sumset_energy {p : ℕ} [Fact p.Prime] (A : Finset (ZMod p))
    (m : ℕ) (hm : m ≤ p) (d : ZMod p) (hd : d ≠ 0) :
    A.card^2*m^2 ≤ (A + (fieldInterval p m).image (fun i => d⁻¹*i)).card *
      Finset.addEnergy A ((fieldInterval p m).image (fun i => d⁻¹*i)) := by
  have hc : ((fieldInterval p m).image (fun i => d⁻¹*i)).card = m := by
    have hi : Function.Injective (fun i : ZMod p => d⁻¹*i) := by
      intro x y h
      exact mul_left_cancel₀ (inv_ne_zero hd) h
    rw [Finset.card_image_of_injective _ hi,fieldInterval_card p m hm]
  simpa only [hc] using Finset.le_card_add_mul_addEnergy A ((fieldInterval p m).image (fun i => d⁻¹*i))

/-- For a fixed difference, the exact first moment over all translations is
|A| |I|. No independence between hits at different indices is assumed. -/
theorem progression_translation_first_moment {p : ℕ} [Fact p.Prime]
    (A I : Finset (ZMod p)) (d : ZMod p) (hd : d ≠ 0) :
    ∑ t : ZMod p, (A ∩ fieldProgression I d t).card = A.card*I.card := by
  let S := A.product I
  let f := fun z : ZMod p × ZMod p => z.1-d*z.2
  have hf (t : ZMod p) : (S.filter (fun z => f z = t)).card = (A ∩ fieldProgression I d t).card := by
    apply Finset.card_bij (fun z _ => z.1)
    · intro z hz
      obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
      obtain ⟨ha,hi⟩ := Finset.mem_product.mp hz
      exact Finset.mem_inter.mpr ⟨ha,Finset.mem_image.mpr ⟨z.2,hi,by dsimp [f] at he; linear_combination -he⟩⟩
    · intro z hz w hw he
      have hz' := (Finset.mem_filter.mp hz).2
      have hw' := (Finset.mem_filter.mp hw).2
      apply Prod.ext he
      apply mul_left_cancel₀ hd
      dsimp [f] at hz' hw'
      rw [he] at hz'
      linear_combination hw'-hz'
    · intro a ha
      obtain ⟨ha,hi⟩ := Finset.mem_inter.mp ha
      obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hi
      exact ⟨(a,i),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hi⟩,by dsimp [f]; linear_combination -he⟩,rfl⟩
  have hs := Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.univ) (f := f)
    (by intro z _; exact Finset.mem_univ _)
  rw [Finset.sum_congr rfl (fun t _ => hf t)] at hs
  have hc : S.card = A.card*I.card := by
    simpa only [S,Finset.instSProd,SProd.sprod] using Finset.card_product A I
  exact hs.symm.trans hc

/-- Finite Markov bound derived from the exact first moment. The threshold
is an integer and may be chosen after rounding a desired real threshold. -/
theorem progression_translation_markov {p : ℕ} [Fact p.Prime]
    (A I : Finset (ZMod p)) (d : ZMod p) (hd : d ≠ 0) (T : ℕ) :
    T*(Finset.univ.filter (fun t => T ≤ (A ∩ fieldProgression I d t).card)).card ≤ A.card*I.card := by
  let B := Finset.univ.filter (fun t => T ≤ (A ∩ fieldProgression I d t).card)
  calc
    _ = ∑ _t ∈ B, T := by simp [B,mul_comm]
    _ ≤ ∑ t ∈ B, (A ∩ fieldProgression I d t).card :=
      Finset.sum_le_sum (fun t ht => (Finset.mem_filter.mp ht).2)
    _ ≤ ∑ t : ZMod p, (A ∩ fieldProgression I d t).card :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = _ := progression_translation_first_moment A I d hd

end KakeyaTwoScale
#print axioms KakeyaTwoScale.fieldInterval_card
#print axioms KakeyaTwoScale.fieldProgression_card
#print axioms KakeyaTwoScale.progression_hit_set
#print axioms KakeyaTwoScale.progression_sumset_energy
#print axioms KakeyaTwoScale.progression_translation_first_moment

#print axioms KakeyaTwoScale.progression_translation_markov
