module
public import KakeyaTwoScale.StableModularModel
public import KakeyaTwoScale.RationalRectification

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

def modelingFactor (r : ℚ) : ℕ := (2*(|(r.den:ℤ)|+|r.num|+1)+1).toNat

theorem modelingFactor_pos (r : ℚ) : 0 < modelingFactor r := by
  have := abs_nonneg (r.den:ℤ)
  have := abs_nonneg r.num
  dsimp [modelingFactor]
  omega

theorem rectificationFactor_pos (r : ℚ) : 0 < rectificationFactor r := by
  have := abs_nonneg (r.den:ℤ)
  have := abs_nonneg r.num
  dsimp [rectificationFactor]
  omega

theorem modular_cleared_projection_card (p : ℕ) [Fact p.Prime]
    (H : Finset (ZMod p × ZMod p)) (a b : ℤ) (hb : (b:ZMod p) ≠ 0) :
    (H.image (modularLinearForm p b a)).card = (H.image (modularRationalProjection p a b)).card := by
  apply image_card_of_same_fibers
  intro v _ w _
  have he (z : ZMod p × ZMod p) : modularLinearForm p b a z = (b:ZMod p)*modularRationalProjection p a b z := by
    dsimp [modularLinearForm,modularRationalProjection]
    field_simp
  rw [he v,he w]
  exact ⟨mul_left_cancel₀ hb,congrArg (fun z => (b:ZMod p)*z)⟩

theorem exists_stable_model_cleared (p : ℕ) [Fact p.Prime]
    (G : Finset (ℤ × ℤ)) (hG : G.Nonempty) (R : Finset ℚ) (hR : R.Nonempty)
    (hp : 20*(G.image Prod.snd).card ≤ p)
    (hP : ∀ r ∈ R, (G.image (integerProjection r)).card ≤ (G.image Prod.snd).card)
    (hden : ∀ r ∈ R, (r.den:ZMod p) ≠ 0)
    (M : ℕ) (hM : ∀ y ∈ G.image Prod.snd, (G.filter (fun v => v.2=y)).card = M) :
    ∃ H : Finset (ZMod p × ZMod p),
      (3/5:ℝ)*(G.image Prod.snd).card ≤ ((H.image Prod.snd).card:ℝ) ∧
      (∀ y ∈ H.image Prod.snd,
        M ≤ 2*(H.filter (fun v => v.2=y)).card ∧ (H.filter (fun v => v.2=y)).card ≤ M) ∧
      ∀ r ∈ R,
        (H.image (modularLinearForm p (slopeCoefficients r).1 (slopeCoefficients r).2)).card ≤
          (G.image (integerProjection r)).card * modelingFactor r := by
  obtain ⟨H,_,hY,hF,hproj⟩ := exists_stable_modular_model p G hG R hR hp hP M hM
  refine ⟨H,hY,hF,?_⟩
  intro r hr
  have hd : ((r.den:ℤ):ZMod p) ≠ 0 := by simpa using hden r hr
  have hh := hproj r.num r.den hd
  dsimp [slopeCoefficients]
  rw [modular_cleared_projection_card p H r.num r.den hd]
  simpa only [Int.cast_natCast,Rat.num_div_den,modelingFactor] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.modelingFactor_pos
#print axioms KakeyaTwoScale.rectificationFactor_pos
#print axioms KakeyaTwoScale.modular_cleared_projection_card
#print axioms KakeyaTwoScale.exists_stable_model_cleared
