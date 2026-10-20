module
public import KakeyaTwoScale.ModularRounding
public import KakeyaTwoScale.FiniteFiberEncoding
public import Mathlib.Data.Int.Interval

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Explicit projection loss for the deterministic modular rounding map.
The loss depends only on the signed integer coefficients. -/
theorem modular_projection_card_bound (p : ℕ) (θ : ℝ) (a b : ℤ)
    (G : Finset (ℤ × ℤ)) :
    ((G.image (modularPair p θ)).image (modularLinearForm p a b)).card ≤
      (G.image (integerLinearForm a b)).card * (2*(|a|+|b|+1)+1).toNat := by
  let M := |a|+|b|+1
  let C := Finset.Icc (-M) M
  let T := (G.image (integerLinearForm a b)).product C
  let f := fun z : ℤ × ℤ => modularRound p θ z.1+(z.2:ZMod p)
  have hsub : (G.image (modularPair p θ)).image (modularLinearForm p a b) ⊆ T.image f := by
    intro y hy
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨c,hc,he⟩ := modular_projection_carry p θ a b w
    refine Finset.mem_image.mpr ⟨(integerLinearForm a b w,c),?_,he.symm⟩
    refine Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨w,hw,rfl⟩,?_⟩
    exact Finset.mem_Icc.mpr (abs_le.mp hc)
  have hcard : C.card = (2*(|a|+|b|+1)+1).toNat := by
    simp only [C,Int.card_Icc]
    congr 1
    dsimp [M]
    ring
  calc
    _ ≤ (T.image f).card := Finset.card_le_card hsub
    _ ≤ T.card := Finset.card_image_le
    _ = _ := by simpa only [T,hcard,Finset.instSProd,SProd.sprod] using Finset.card_product (G.image (integerLinearForm a b)) C

def modularRationalProjection (p : ℕ) [Fact p.Prime] (a b : ℤ) (v : ZMod p × ZMod p) : ZMod p :=
  v.1+(a:ZMod p)/(b:ZMod p)*v.2

/-- Rational projections in a prime field require a denominator nonzero in
that field. No restriction on a zero numerator is imposed. -/
theorem modular_rational_projection_card_bound (p : ℕ) [Fact p.Prime]
    (θ : ℝ) (a b : ℤ) (hb : (b:ZMod p) ≠ 0) (G : Finset (ℤ × ℤ)) :
    ((G.image (modularPair p θ)).image (modularRationalProjection p a b)).card ≤
      (G.image (integerProjection ((a:ℚ)/(b:ℚ)))).card * (2*(|b|+|a|+1)+1).toNat := by
  have hbz : b ≠ 0 := by intro h; apply hb; simp [h]
  have hmul (v : ZMod p × ZMod p) :
      (b:ZMod p)*modularRationalProjection p a b v = modularLinearForm p b a v := by
    simp only [modularRationalProjection,modularLinearForm]
    field_simp
  have hfield := image_card_of_same_fibers (G.image (modularPair p θ))
    (modularRationalProjection p a b) (modularLinearForm p b a) (by
      intro v _ w _
      rw [← hmul v,← hmul w]
      exact ⟨congrArg (fun x => (b:ZMod p)*x),mul_left_cancel₀ hb⟩)
  have hbq : (b:ℚ) ≠ 0 := by exact_mod_cast hbz
  have hint := image_card_of_same_fibers G (integerProjection ((a:ℚ)/(b:ℚ)))
    (integerLinearForm b a) (by
      intro v _ w _
      constructor
      · intro h
        have hh := congrArg (fun x => (b:ℚ)*x) h
        rw [rational_projection_integer_form a b hbz,rational_projection_integer_form a b hbz] at hh
        exact_mod_cast hh
      · intro h
        apply mul_left_cancel₀ hbq
        rw [rational_projection_integer_form a b hbz,rational_projection_integer_form a b hbz,h])
  rw [hfield,hint]
  exact modular_projection_card_bound p θ b a G

end KakeyaTwoScale
#print axioms KakeyaTwoScale.modular_projection_card_bound
#print axioms KakeyaTwoScale.modular_rational_projection_card_bound
