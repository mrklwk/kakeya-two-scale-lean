module
public import KakeyaTwoScale.IntegerRectification
public import KakeyaTwoScale.VerticalCounting

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

def rationalLift (p : ℕ) (v : ZMod p × ZMod p) : ArithmeticPoint :=
  ((integerLift p v).1,(integerLift p v).2)

theorem rationalLift_height_card (p : ℕ) [NeZero p]
    (G : Finset (ZMod p × ZMod p)) :
    ((G.image (rationalLift p)).image Prod.snd).card = (G.image Prod.snd).card := by
  rw [Finset.image_image]
  apply image_card_of_same_fibers
  intro v _ w _
  constructor
  · intro h
    change ((integerLift p v).2:ℚ) = ((integerLift p w).2:ℚ) at h
    have hi : (integerLift p v).2 = (integerLift p w).2 := by
      exact_mod_cast h
    have hf := congrArg (fun z : ℤ => (z : ZMod p)) hi
    simpa [integerLift] using hf
  · intro h
    simp [rationalLift,integerLift,h]

theorem rationalLift_projection_card_bound (p : ℕ) [NeZero p]
    (a b : ℤ) (hb : b ≠ 0) (G : Finset (ZMod p × ZMod p)) :
    ((G.image (rationalLift p)).image (arithmeticProjection ((a:ℚ)/(b:ℚ)))).card ≤
      (G.image (modularLinearForm p b a)).card * (2*(|b|+|a|)+1).toNat := by
  have hbq : (b:ℚ) ≠ 0 := by exact_mod_cast hb
  have hint := image_card_of_same_fibers (G.image (integerLift p))
    (integerProjection ((a:ℚ)/(b:ℚ))) (integerLinearForm b a) (by
      intro v _ w _
      constructor
      · intro h
        have hh := congrArg (fun x => (b:ℚ)*x) h
        rw [rational_projection_integer_form a b hb,rational_projection_integer_form a b hb] at hh
        exact_mod_cast hh
      · intro h
        apply mul_left_cancel₀ hbq
        rw [rational_projection_integer_form a b hb,rational_projection_integer_form a b hb,h])
  have he : ((G.image (rationalLift p)).image (arithmeticProjection ((a:ℚ)/(b:ℚ)))).card =
      ((G.image (integerLift p)).image (integerProjection ((a:ℚ)/(b:ℚ)))).card := by
    simp only [Finset.image_image,Function.comp_def,rationalLift,arithmeticProjection,integerProjection]
  rw [he,hint]
  exact integerLift_projection_card_bound p b a G

def slopeCoefficients (r : ℚ) : ℤ × ℤ := (r.den,r.num)
def rectificationFactor (r : ℚ) : ℕ := (2*(|(r.den:ℤ)|+|r.num|)+1).toNat

theorem rationalLift_slope_card_bound (p : ℕ) [NeZero p]
    (r : ℚ) (G : Finset (ZMod p × ZMod p)) :
    ((G.image (rationalLift p)).image (arithmeticProjection r)).card ≤
      (G.image (modularLinearForm p (slopeCoefficients r).1 (slopeCoefficients r).2)).card *
        rectificationFactor r := by
  have hb : (r.den:ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  simpa only [Rat.num_div_den,slopeCoefficients,rectificationFactor,Int.cast_natCast] using
    rationalLift_projection_card_bound p r.num r.den hb G

/-- The rational ordinary counting theorem applies to canonical lifts with
an explicit loss depending only on the finitely many rational slopes. -/
theorem vertical_counting_rectification (R : Finset ℚ) (β : ℝ)
    (hcount : ∀ G : Finset ArithmeticPoint, ∀ N : ℝ, 0 ≤ N →
      (∀ r ∈ R, ((G.image (arithmeticProjection r)).card:ℝ) ≤ N) →
      ((G.image Prod.snd).card:ℝ) ≤ N^β) :
    ∀ (p : ℕ) [NeZero p], ∀ G : Finset (ZMod p × ZMod p), ∀ N : ℝ, 0 ≤ N →
      (∀ r ∈ R,
        ((G.image (modularLinearForm p (slopeCoefficients r).1 (slopeCoefficients r).2)).card:ℝ) *
          rectificationFactor r ≤ N) →
      ((G.image Prod.snd).card:ℝ) ≤ N^β := by
  intro p hp G N hN hproj
  have h := hcount (G.image (rationalLift p)) N hN (by
    intro r hr
    calc
      _ ≤ ((G.image (modularLinearForm p (slopeCoefficients r).1 (slopeCoefficients r).2)).card:ℝ) *
          rectificationFactor r := by exact_mod_cast rationalLift_slope_card_bound p r G
      _ ≤ N := hproj r hr)
  rwa [rationalLift_height_card] at h

theorem finite_field_vertical_counting_625_373 :
    ∃ R : Finset ℚ, R.Nonempty ∧ ∀ (p : ℕ) [NeZero p],
      ∀ G : Finset (ZMod p × ZMod p), ∀ N : ℝ, 0 ≤ N →
      (∀ r ∈ R,
        ((G.image (modularLinearForm p (slopeCoefficients r).1 (slopeCoefficients r).2)).card:ℝ) *
          rectificationFactor r ≤ N) →
      ((G.image Prod.snd).card:ℝ) ≤ N^(625/373:ℝ) := by
  obtain ⟨R,hR,hcount⟩ := finite_vertical_counting_625_373
  exact ⟨R,hR,vertical_counting_rectification R _ hcount⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.rationalLift_height_card
#print axioms KakeyaTwoScale.rationalLift_projection_card_bound
#print axioms KakeyaTwoScale.rationalLift_slope_card_bound
#print axioms KakeyaTwoScale.finite_field_vertical_counting_625_373

#print axioms KakeyaTwoScale.vertical_counting_rectification
