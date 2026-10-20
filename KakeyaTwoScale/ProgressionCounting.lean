module
public import KakeyaTwoScale.ProgressionExtraction
public import KakeyaTwoScale.RationalRectification

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

def slopeRectificationBudget (R : Finset ℚ) : ℕ := ∑ r ∈ R, rectificationFactor r

/-- Generic progression comparison from an explicit vertical counting
hypothesis. The closed 625/373 specialization below discharges that hypothesis. -/
theorem progression_counting_of_field_counting (R : Finset ℚ) (β : ℝ)
    (hcount : ∀ (p : ℕ) [NeZero p], ∀ G : Finset (ZMod p × ZMod p), ∀ N : ℝ, 0 ≤ N →
      (∀ r ∈ R,
        ((G.image (modularLinearForm p (slopeCoefficients r).1 (slopeCoefficients r).2)).card:ℝ) *
          rectificationFactor r ≤ N) →
      ((G.image Prod.snd).card:ℝ) ≤ N^β) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p → ∀ m : ℕ,
      0 < m → m < p → 0 < Nat.floor ((m:ℝ)*(p:ℝ)^(-ε)) →
      ∀ H : Finset (ZMod p × ZMod p), ((H.image Prod.snd).erase 0).Nonempty →
      (∀ y ∈ (H.image Prod.snd).erase 0, (p:ℝ)/(m:ℝ) ≤ ((H.filter (fun v => v.2=y)).card:ℝ)) →
      (∀ r ∈ R, (r.den:ZMod p) ≠ 0) →
      samplingHeightMass p m ε H/(2*((p-1)*p:ℕ)) ≤
        (2*(m:ℝ)*(samplingProjectionBudget p m H (R.image slopeCoefficients):ℝ)/
          samplingHeightMass p m ε H*(slopeRectificationBudget R:ℝ))^β := by
  intro ε hε
  obtain ⟨N,hN⟩ := exists_progression_extraction ε hε
  refine ⟨N,?_⟩
  intro p hp hpN m hm hmp hg H hY hf hden
  obtain ⟨d,t,_,hheight,hproj⟩ := hN p hpN m hm hmp hg H hY hf
    (R.image slopeCoefficients) (by
      intro c hc
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hc
      simpa only [slopeCoefficients,Int.cast_natCast] using hden r hr)
  let U := 2*(m:ℝ)*(samplingProjectionBudget p m H (R.image slopeCoefficients):ℝ)/samplingHeightMass p m ε H
  have hU : 0 ≤ U := by dsimp [U,samplingHeightMass]; positivity
  apply hheight.trans
  apply hcount p _ (U*(slopeRectificationBudget R:ℝ)) (mul_nonneg hU (Nat.cast_nonneg _))
  intro r hr
  have hfactor : rectificationFactor r ≤ slopeRectificationBudget R :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hr
  exact (mul_le_mul_of_nonneg_right (hproj _ (Finset.mem_image.mpr ⟨r,hr,rfl⟩))
    (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hfactor) hU)

/-- Closed finite progression comparison: only explicit size and denominator
conditions remain, with no assumed arithmetic or homogenization theorem. -/
theorem finite_progression_counting_625_373 :
    ∃ R : Finset ℚ, R.Nonempty ∧ ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p → ∀ m : ℕ,
      0 < m → m < p → 0 < Nat.floor ((m:ℝ)*(p:ℝ)^(-ε)) →
      ∀ H : Finset (ZMod p × ZMod p), ((H.image Prod.snd).erase 0).Nonempty →
      (∀ y ∈ (H.image Prod.snd).erase 0, (p:ℝ)/(m:ℝ) ≤ ((H.filter (fun v => v.2=y)).card:ℝ)) →
      (∀ r ∈ R, (r.den:ZMod p) ≠ 0) →
      samplingHeightMass p m ε H/(2*((p-1)*p:ℕ)) ≤
        (2*(m:ℝ)*(samplingProjectionBudget p m H (R.image slopeCoefficients):ℝ)/
          samplingHeightMass p m ε H*(slopeRectificationBudget R:ℝ))^(625/373:ℝ) := by
  obtain ⟨R,hR,hcount⟩ := finite_field_vertical_counting_625_373
  exact ⟨R,hR,progression_counting_of_field_counting R _ hcount⟩

/-- A single fixed slope family supplies BOTH the ordinary entropy bound
and progression counting. This preserves the witness needed in the
zero-conditional-entropy case. -/
theorem finite_progression_and_entropy_625_373 :
    ∃ R : Finset ℚ, ∃ hR : R.Nonempty,
      (∀ (A : Type) [Fintype A] (q : A → ℝ), (∀ a, 0 ≤ q a) → (∑ a, q a = 1) →
        ∀ f : A → ArithmeticPoint,
          pushEntropy q (Prod.snd ∘ f) ≤ (625/373:ℝ)*R.sup' hR
            (fun r => pushEntropy q (arithmeticProjection r ∘ f))) ∧
      (∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p → ∀ m : ℕ,
      0 < m → m < p → 0 < Nat.floor ((m:ℝ)*(p:ℝ)^(-ε)) →
      ∀ H : Finset (ZMod p × ZMod p), ((H.image Prod.snd).erase 0).Nonempty →
      (∀ y ∈ (H.image Prod.snd).erase 0, (p:ℝ)/(m:ℝ) ≤ ((H.filter (fun v => v.2=y)).card:ℝ)) →
      (∀ r ∈ R, (r.den:ZMod p) ≠ 0) →
      samplingHeightMass p m ε H/(2*((p-1)*p:ℕ)) ≤
        (2*(m:ℝ)*(samplingProjectionBudget p m H (R.image slopeCoefficients):ℝ)/
          samplingHeightMass p m ε H*(slopeRectificationBudget R:ℝ))^(625/373:ℝ)) := by
  obtain ⟨S,hproper,hSD⟩ := finiteSD_625_373_constant_one
  have hS := hSD.slopes_nonempty (by norm_num)
  refine ⟨S.image verticalSlope,hS.image _,?_,?_⟩
  · intro A _ q hq hsum f
    exact hSD.vertical_entropy (by norm_num) hS hproper q hq hsum f
  · apply progression_counting_of_field_counting
    apply vertical_counting_rectification
    intro G N hN hproj
    simpa only [one_mul] using hSD.vertical_image_bound hproper G N hN hproj

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_progression_counting_625_373

#print axioms KakeyaTwoScale.progression_counting_of_field_counting
#print axioms KakeyaTwoScale.finite_progression_and_entropy_625_373
