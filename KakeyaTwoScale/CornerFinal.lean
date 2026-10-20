module
public import KakeyaTwoScale.PowerFeedback
public import KakeyaTwoScale.IntersectedRefinement
public import KakeyaTwoScale.CornerFibers

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- The actual outer projection used on the corner refinement. -/
def cornerOuterProjection (p t r : ℚ) (c : ArithmeticCorner) : ℚ × ℚ :=
  (arithmeticProjection r c.2.1,cornerNu p t r (c.1,c.2.2))

theorem cornerOuter_determines_mu (G : Finset ArithmeticPoint) (p s t r : ℚ)
    (hr : r ≠ p) {c d : ArithmeticCorner}
    (hc : c ∈ arithmeticCorners G p s) (hd : d ∈ arithmeticCorners G p s)
    (he : cornerOuterProjection p t r c = cornerOuterProjection p t r d) :
    cornerMu t c = cornerMu t d := by
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  exact (corner_mu_nu_fiber_iff G p s t r hr hc hd h1).mpr h2

theorem corner_fiber_first_card (G : Finset ArithmeticPoint) (p s t z : ℚ)
    (hrs : p ≠ s) (hdiff : Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint))
    (U : Finset ArithmeticCorner) (hU : U ⊆ arithmeticCorners G p s)
    (hmu : ∀ c ∈ U, cornerMu t c = z) :
    (U.image (fun c => c.2.1)).card = U.card := by
  apply Finset.card_image_iff.mpr
  intro c hc d hd he
  apply corner_first_mu_injective G p s t hrs hdiff (hU hc) (hU hd)
  exact Prod.ext he ((hmu c hc).trans (hmu d hd).symm)

theorem corner_first_projection_le_outer (U : Finset ArithmeticCorner) (p t r : ℚ) :
    ((U.image (fun c => c.2.1)).image (arithmeticProjection r)).card ≤
      (U.image (cornerOuterProjection p t r)).card := by
  have he : (U.image (fun c => c.2.1)).image (arithmeticProjection r) =
      (U.image (cornerOuterProjection p t r)).image Prod.fst := by
    simp only [Finset.image_image,Function.comp_def,cornerOuterProjection]
  rw [he]
  exact Finset.card_image_le

/-- Apply the preceding outer SD estimate to an actual nonempty mu fiber. -/
theorem FiniteSDBound.corner_fiber {R : Finset ℚ} {β C : ℝ} (hSD : FiniteSDBound R β C)
    (G : Finset ArithmeticPoint) (U : Finset ArithmeticCorner) (p s t z : ℚ)
    (hps : p ≠ s) (hdiff : Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint))
    (hU : U ⊆ arithmeticCorners G p s) (hmu : ∀ c ∈ U, cornerMu t c = z)
    (K : ℝ) (hK : 0 ≤ K)
    (hp : ∀ r ∈ R, ((U.image (cornerOuterProjection p t r)).card : ℝ) ≤ K*U.card) :
    (U.card : ℝ) ≤ C*(K*U.card)^β := by
  let H := U.image (fun c => c.2.1)
  have hHG : H ⊆ G := by
    intro x hx
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hx
    exact ((mem_arithmeticCorners G p s c).mp (hU hc)).2.1
  have hd : Set.InjOn (arithmeticProjection (-1)) (↑H : Set ArithmeticPoint) :=
    fun _ hx _ hy he => hdiff (hHG hx) (hHG hy) he
  have hproj : ∀ r ∈ R, ((H.image (arithmeticProjection r)).card : ℝ) ≤ K*U.card := by
    intro r hr
    have hb : ((H.image (arithmeticProjection r)).card : ℝ) ≤ (U.image (cornerOuterProjection p t r)).card := by
      exact_mod_cast corner_first_projection_le_outer U p t r
    exact hb.trans (hp r hr)
  have hh := hSD H hd (K*U.card) (mul_nonneg hK (Nat.cast_nonneg _)) hproj
  have hc : H.card = U.card := corner_fiber_first_card G p s t z hps hdiff U hU hmu
  simpa only [hc] using hh

/-- Finite image cardinality is independent of the equality decision
procedure, allowing the generic refinements to instantiate concrete maps. -/
theorem classical_image_card {A B : Type*} [DecidableEq B] (S : Finset A) (f : A → B) :
    (@Finset.image A B (Classical.decEq B) f S).card = (S.image f).card := by
  congr 1
  ext b
  simp

theorem cornerOuter_image_bound (G : Finset ArithmeticPoint) (H : Finset ArithmeticCorner)
    (W : Finset (ArithmeticPoint × ArithmeticPoint)) (p s t r : ℚ)
    (hH : H ⊆ arithmeticCorners G p s) (hW : ∀ c ∈ H, (c.1,c.2.2) ∈ W) :
    (H.image (cornerOuterProjection p t r)).card ≤
      (G.image (arithmeticProjection r)).card*(W.image (cornerNu p t r)).card := by
  rw [← Finset.card_product]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hv
  apply Finset.mem_product.mpr
  exact ⟨Finset.mem_image.mpr ⟨c.2.1,((mem_arithmeticCorners G p s c).mp (hH hc)).2.1,rfl⟩,
    Finset.mem_image.mpr ⟨(c.1,c.2.2),hW c hc,rfl⟩⟩

/-- The full finite outer-SD versus small-double-fiber comparison. The mu
fiber is selected from an ACTUAL half-mass refinement; neither that fiber
nor its nonlinear lower bound is supplied as a hypothesis. -/
theorem FiniteSDBound.final_corner_comparison {R : Finset ℚ} {β C : ℝ}
    (hSD : FiniteSDBound R β C) (hβ : 1 < β) (hC : 0 < C)
    (G : Finset ArithmeticPoint) (K : Finset ArithmeticCorner)
    (V W : Finset (ArithmeticPoint × ArithmeticPoint)) (p s t : ℚ)
    (N B L : ℕ) (hNpos : 0 < N) (hBpos : 0 < B) (hps : p ≠ s)
    (hdiff : Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint))
    (hR : ∀ r ∈ R, r ≠ p) (hK : K ⊆ arithmeticCorners G p s)
    (hV : ∀ c ∈ K, (c.1,c.2.1) ∈ V) (hW : ∀ c ∈ K, (c.1,c.2.2) ∈ W)
    (hN : ∀ r ∈ R, (G.image (arithmeticProjection r)).card ≤ N)
    (hNt : (G.image (arithmeticProjection t)).card ≤ N)
    (hB : ∀ r ∈ R, (W.image (cornerNu p t r)).card ≤ B)
    (hne : (goodCorners K V s t L).Nonempty) :
    (C*(4*(4*(R.card:ℝ)+1)*N*B/(goodCorners K V s t L).card)^β)^(-1/(β-1)) ≤ N*L := by
  let H := goodCorners K V s t L
  let d := 4*R.card+1
  let A : ℝ := 4*d*N*B/H.card
  have hHK : H ⊆ K := Finset.filter_subset _ _
  have hHC := hHK.trans hK
  have hHpos : (0:ℝ) < H.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hApos : 0 < A := by dsimp [A,d]; positivity
  obtain ⟨Q,hQ,hhalf,hproj⟩ := exists_half_fiber_refinement H R
    (cornerOuterProjection p t) (cornerMu t)
  simp only [classical_image_card] at hproj
  have hQpos : 0 < Q.card := by
    have hh : 0 < H.card := Finset.card_pos.mpr hne
    omega
  obtain ⟨c,hc⟩ := Finset.card_pos.mp hQpos
  let z := cornerMu t c
  let U := Q.filter (fun c => cornerMu t c = z)
  have hUQ : U ⊆ Q := Finset.filter_subset _ _
  have hUH : U ⊆ H := hUQ.trans hQ
  have hUC : U ⊆ arithmeticCorners G p s := hUH.trans hHC
  have hmu : ∀ c ∈ U, cornerMu t c = z := fun c hc => (Finset.mem_filter.mp hc).2
  have hUpos : (0:ℝ) < U.card := by
    have hn : U.Nonempty := ⟨c,Finset.mem_filter.mpr ⟨hc,rfl⟩⟩
    exact_mod_cast Finset.card_pos.mpr hn
  have hp : ∀ r ∈ R, ((U.image (cornerOuterProjection p t r)).card : ℝ) ≤ A*U.card := by
    intro r hr
    have hf := hproj r hr
      (fun c hc e he hce => cornerOuter_determines_mu G p s t r (hR r hr) (hHC hc) (hHC he) hce) z
    have hrange : (H.image (cornerOuterProjection p t r)).card ≤ N*B :=
      (cornerOuter_image_bound G H W p s t r hHC (fun c hc => hW c (hHK hc))).trans
        (Nat.mul_le_mul (hN r hr) (hB r hr))
    change Q.card*(U.image (cornerOuterProjection p t r)).card ≤
      (2*d*(H.image (cornerOuterProjection p t r)).card)*U.card at hf
    have hm1 := Nat.mul_le_mul_right (U.image (cornerOuterProjection p t r)).card hhalf
    have hm2 := Nat.mul_le_mul_right U.card (Nat.mul_le_mul_left (2*d) hrange)
    have hn : H.card*(U.image (cornerOuterProjection p t r)).card ≤ 4*d*N*B*U.card := by nlinarith
    have hn' : (H.card:ℝ)*(U.image (cornerOuterProjection p t r)).card ≤ 4*d*N*B*U.card := by exact_mod_cast hn
    have he : A*(U.card:ℝ)*(H.card:ℝ) = 4*d*N*B*U.card := by dsimp [A]; field_simp
    apply (mul_le_mul_iff_left₀ hHpos).mp
    rw [he]
    nlinarith
  have hfeedback := hSD.corner_fiber G U p s t z hps hdiff hUC hmu A hApos.le hp
  have hlower := power_feedback_lower (U.card:ℝ) C A β hUpos hC hApos hβ hfeedback
  have hu : U.card ≤ N*L := by
    have hsub : U ⊆ H.filter (fun c => cornerMu t c = z) := by
      intro c hc
      exact Finset.mem_filter.mpr ⟨hUH hc,hmu c hc⟩
    exact (Finset.card_le_card hsub).trans
      ((goodCorners_mu_fiber_upper G K V p s t z L hps hdiff hK hV).trans (Nat.mul_le_mul_right L hNt))
  have hu' : (U.card:ℝ) ≤ N*L := by exact_mod_cast hu
  have hresult := hlower.trans hu'
  simpa [A,d,H,Nat.cast_add,Nat.cast_mul] using hresult

end KakeyaTwoScale
#print axioms KakeyaTwoScale.cornerOuter_determines_mu
#print axioms KakeyaTwoScale.corner_fiber_first_card
#print axioms KakeyaTwoScale.corner_first_projection_le_outer
#print axioms KakeyaTwoScale.FiniteSDBound.corner_fiber

#print axioms KakeyaTwoScale.classical_image_card
#print axioms KakeyaTwoScale.cornerOuter_image_bound
#print axioms KakeyaTwoScale.FiniteSDBound.final_corner_comparison
