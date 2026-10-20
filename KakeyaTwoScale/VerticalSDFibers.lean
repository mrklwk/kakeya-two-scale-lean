module
public import KakeyaTwoScale.SumDifference
public import KakeyaTwoScale.RefinedFiberProjection

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- A fixed nu fiber is parameterized by its first endpoint. -/
theorem vertical_nu_first_injective (G : Finset ArithmeticPoint)
    (U : Finset (ArithmeticPoint × ArithmeticPoint)) (a p z : ℚ)
    (hU : U ⊆ G.product G)
    (hdiff : Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint))
    (hnu : ∀ v ∈ U, verticalNu a p v = z) :
    Set.InjOn Prod.fst (↑U : Set (ArithmeticPoint × ArithmeticPoint)) := by
  intro v hv w hw hfirst
  have hm := (hnu v hv).trans (hnu w hw).symm
  dsimp [verticalNu] at hm
  rw [hfirst] at hm
  have hsecond : v.2=w.2 := hdiff (Finset.mem_product.mp (hU hv)).2
    (Finset.mem_product.mp (hU hw)).2 (add_left_cancel hm)
  exact Prod.ext hfirst hsecond

theorem vertical_nu_first_card (G : Finset ArithmeticPoint)
    (U : Finset (ArithmeticPoint × ArithmeticPoint)) (a p z : ℚ)
    (hU : U ⊆ G.product G)
    (hdiff : Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint))
    (hnu : ∀ v ∈ U, verticalNu a p v = z) :
    (U.image Prod.fst).card = U.card :=
  Finset.card_image_iff.mpr (vertical_nu_first_injective G U a p z hU hdiff hnu)

/-- The first-endpoint projection image is bounded by the corresponding
actual double-projection image. -/
theorem first_projection_card_le_double (U : Finset (ArithmeticPoint × ArithmeticPoint)) (r t : ℚ) :
    ((U.image Prod.fst).image (arithmeticProjection r)).card ≤
      (U.image (fun v => (arithmeticProjection r v.1, arithmeticProjection t v.2))).card := by
  have he : (U.image Prod.fst).image (arithmeticProjection r) =
      (U.image (fun v => (arithmeticProjection r v.1, arithmeticProjection t v.2))).image Prod.fst := by
    simp only [Finset.image_image, Function.comp_def]
  rw [he]
  exact Finset.card_image_le

/-- Actual application of the preceding SD estimate to a parameterized nu
fiber. The double-projection estimates are the outputs of the refinement
counting stage; the resulting nonlinear inequality is proved, not assumed. -/
theorem FiniteSDBound.vertical_fiber {R : Finset ℚ} {β C : ℝ} (hSD : FiniteSDBound R β C)
    (G : Finset ArithmeticPoint) (U : Finset (ArithmeticPoint × ArithmeticPoint))
    (a p z : ℚ) (dual : ℚ → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hU : U ⊆ G.product G)
    (hdiff : Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint))
    (hnu : ∀ v ∈ U, verticalNu a p v = z)
    (hproj : ∀ r ∈ R,
      ((U.image (fun v => (arithmeticProjection r v.1, arithmeticProjection (dual r) v.2))).card : ℝ) ≤
        K*U.card) :
    (U.card : ℝ) ≤ C*(K*U.card)^β := by
  let H := U.image Prod.fst
  have hHG : H ⊆ G := by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_product.mp (hU hv)).1
  have hd : Set.InjOn (arithmeticProjection (-1)) (↑H : Set ArithmeticPoint) :=
    fun _ hx _ hy he => hdiff (hHG hx) (hHG hy) he
  have hp : ∀ r ∈ R, ((H.image (arithmeticProjection r)).card : ℝ) ≤ K*U.card := by
    intro r hr
    have hb : ((H.image (arithmeticProjection r)).card : ℝ) ≤
        (U.image (fun v => (arithmeticProjection r v.1, arithmeticProjection (dual r) v.2))).card := by
      exact_mod_cast first_projection_card_le_double U r (dual r)
    exact hb.trans (hproj r hr)
  have h := hSD H hd (K*U.card) (mul_nonneg hK (Nat.cast_nonneg _)) hp
  have hc : H.card = U.card := vertical_nu_first_card G U a p z hU hdiff hnu
  simpa only [hc] using h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.vertical_nu_first_injective
#print axioms KakeyaTwoScale.vertical_nu_first_card
#print axioms KakeyaTwoScale.first_projection_card_le_double
#print axioms KakeyaTwoScale.FiniteSDBound.vertical_fiber
