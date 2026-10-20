module
public import KakeyaTwoScale.SampledProjectionBounds
public import KakeyaTwoScale.SimultaneousSampling

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

def samplingHeightMass (p m : ℕ) (ε : ℝ) (H : Finset (ZMod p × ZMod p)) : ℝ :=
  (((H.image Prod.snd).erase 0).card:ℝ)*(Nat.floor ((m:ℝ)*(p:ℝ)^(-ε)):ℝ)*(p:ℝ)^(1-ε)

def samplingProjectionBudget (p m : ℕ) (H : Finset (ZMod p × ZMod p)) (F : Finset (ℤ × ℤ)) : ℕ :=
  (p-1)*m*∑ c ∈ F, (2*coefficientWidth c.1 c.2+1)*(H.image (modularLinearForm p c.1 c.2)).card

theorem halfFieldInterval_card_le (p m : ℕ) (hm : 0 < m) : (halfFieldInterval p m).card ≤ m := by
  apply Finset.card_image_le.trans
  rw [Nat.card_Icc]
  omega

/-- Actual simultaneous finite progression extraction. Nonzero height loss,
floor count, coefficient constants and all averaging factors are explicit. -/
theorem exists_progression_extraction (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p → ∀ m : ℕ,
      0 < m → m < p → 0 < Nat.floor ((m:ℝ)*(p:ℝ)^(-ε)) →
      ∀ H : Finset (ZMod p × ZMod p), ((H.image Prod.snd).erase 0).Nonempty →
      (∀ y ∈ (H.image Prod.snd).erase 0, (p:ℝ)/(m:ℝ) ≤ ((H.filter (fun v => v.2=y)).card:ℝ)) →
      ∀ F : Finset (ℤ × ℤ), (∀ c ∈ F, (c.1:ZMod p) ≠ 0) →
      ∃ d t : ZMod p, d ≠ 0 ∧
        samplingHeightMass p m ε H/(2*((p-1)*p:ℕ)) ≤
          (((sampledGraph H (positiveFieldInterval p m) (halfFieldInterval p m) d t).image Prod.snd).card:ℝ) ∧
        ∀ c ∈ F,
          (((sampledGraph H (positiveFieldInterval p m) (halfFieldInterval p m) d t).image
            (modularLinearForm p c.1 c.2)).card:ℝ) ≤
          2*(m:ℝ)*(samplingProjectionBudget p m H F:ℝ)/samplingHeightMass p m ε H := by
  obtain ⟨N,hN⟩ := progression_height_hits_lower ε hε
  refine ⟨N,?_⟩
  intro p _ hpN m hm hmp hg H hY hf F hF
  let S := nonzeroTranslationSamples p
  let Y := (H.image Prod.snd).erase 0
  let T := fun z : ZMod p × ZMod p => sampledGraph H (positiveFieldInterval p m) (halfFieldInterval p m) z.1 z.2
  let height := fun z => (((T z).image Prod.snd).card:ℝ)
  let cost := fun z => (∑ c ∈ F, (((T z).image (modularLinearForm p c.1 c.2)).card:ℝ))
  let L := samplingHeightMass p m ε H
  let B := (samplingProjectionBudget p m H F:ℝ)
  have hp : 0 < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hL : 0 < L := by
    have hYc : 0 < (Y.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hY
    have hgc : 0 < (Nat.floor ((m:ℝ)*(p:ℝ)^(-ε)):ℝ) := by exact_mod_cast hg
    exact mul_pos (mul_pos hYc hgc) (Real.rpow_pos_of_pos hp _)
  have hScard : S.card = (p-1)*p := nonzeroTranslationSamples_card p
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    rw [hScard]
    have hp2 := (Fact.out : p.Prime).two_le
    exact Nat.mul_pos (by omega) (by omega)
  have hheight : ∀ z ∈ S, height z ≤ (m:ℝ) := by
    intro z _
    dsimp only [height,T]
    exact_mod_cast (sampled_heights_bound H (positiveFieldInterval p m) (halfFieldInterval p m) z.1 z.2).trans
      (halfFieldInterval_card_le p m hm)
  have hcost : ∀ z ∈ S, 0 ≤ cost z := by
    intro z _
    exact Finset.sum_nonneg (fun c _ => Nat.cast_nonneg _)
  have hlower : L ≤ ∑ z ∈ S, height z := by
    change samplingHeightMass p m ε H ≤ ∑ z ∈ nonzeroTranslationSamples p,
      (((sampledGraph H (positiveFieldInterval p m) (halfFieldInterval p m) z.1 z.2).image Prod.snd).card:ℝ)
    rw [← Nat.cast_sum,sampled_height_count_sum p H _ _ (halfFieldInterval_nonzero p m hm hmp),Nat.cast_sum]
    calc
      _ = ∑ _y ∈ Y, (Nat.floor ((m:ℝ)*(p:ℝ)^(-ε)):ℝ)*(p:ℝ)^(1-ε) := by
        simp only [Finset.sum_const,nsmul_eq_mul,samplingHeightMass,Y]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun y hy => hN p hpN m hm hmp (fieldFiberXs H y)
        (by rw [fieldFiberXs_card]; exact hf y hy) y (Finset.mem_erase.mp hy).1)
  have hupper : ∑ z ∈ S, cost z ≤ B := by
    dsimp [cost]
    rw [Finset.sum_comm]
    have hpoint (c : ℤ × ℤ) (hc : c ∈ F) :
        (∑ z ∈ S, (((T z).image (modularLinearForm p c.1 c.2)).card:ℝ)) ≤
          ((p-1)*((2*coefficientWidth c.1 c.2+1)*m*(H.image (modularLinearForm p c.1 c.2)).card):ℕ) := by
      exact_mod_cast sampled_projection_total_sum p m hm H c.1 c.2 (hF c hc)
    apply (Finset.sum_le_sum hpoint).trans_eq
    dsimp [B,samplingProjectionBudget]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  obtain ⟨z,hz,hheightz,hcostz⟩ := exists_simultaneous_sample S hS height cost L B m hL
    (by dsimp [B]; positivity) (by exact_mod_cast hm) hheight hcost hlower hupper
  refine ⟨z.1,z.2,(Finset.mem_erase.mp (Finset.mem_product.mp hz).1).1,?_,?_⟩
  · simpa only [hScard] using hheightz
  · intro c hc
    have h := Finset.single_le_sum (fun c (_ : c ∈ F) => (Nat.cast_nonneg _ : (0:ℝ) ≤ ((T z).image (modularLinearForm p c.1 c.2)).card)) hc
    exact h.trans hcostz

end KakeyaTwoScale
#print axioms KakeyaTwoScale.halfFieldInterval_card_le
#print axioms KakeyaTwoScale.exists_progression_extraction
