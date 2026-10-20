module
public import KakeyaTwoScale.CornerFinal

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

theorem FiniteSDBound.final_corner_comparison_real {R : Finset ℚ} {β C : ℝ}
    (hSD : FiniteSDBound R β C) (hβ : 1 < β) (hC : 0 < C)
    (G : Finset ArithmeticPoint) (K : Finset ArithmeticCorner)
    (V W : Finset (ArithmeticPoint × ArithmeticPoint)) (p s t : ℚ)
    (N L : ℕ) (B : ℝ) (hNpos : 0 < N) (hBpos : 0 < B) (hps : p ≠ s)
    (hdiff : Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint))
    (hR : ∀ r ∈ R, r ≠ p) (hK : K ⊆ arithmeticCorners G p s)
    (hV : ∀ c ∈ K, (c.1,c.2.1) ∈ V) (hW : ∀ c ∈ K, (c.1,c.2.2) ∈ W)
    (hN : ∀ r ∈ R, (G.image (arithmeticProjection r)).card ≤ N)
    (hNt : (G.image (arithmeticProjection t)).card ≤ N)
    (hB : ∀ r ∈ R, ((W.image (cornerNu p t r)).card : ℝ) ≤ B)
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
    have hraw := cornerOuter_image_bound G H W p s t r hHC (fun c hc => hW c (hHK hc))
    have hraw' : ((H.image (cornerOuterProjection p t r)).card:ℝ) ≤
        (G.image (arithmeticProjection r)).card*(W.image (cornerNu p t r)).card := by exact_mod_cast hraw
    have hnN : ((G.image (arithmeticProjection r)).card:ℝ) ≤ N := by exact_mod_cast hN r hr
    have hrange : ((H.image (cornerOuterProjection p t r)).card:ℝ) ≤ N*B :=
      hraw'.trans (mul_le_mul hnN (hB r hr) (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    change Q.card*(U.image (cornerOuterProjection p t r)).card ≤
      (2*d*(H.image (cornerOuterProjection p t r)).card)*U.card at hf
    have hf' : (Q.card:ℝ)*(U.image (cornerOuterProjection p t r)).card ≤
      (2*d*(H.image (cornerOuterProjection p t r)).card)*U.card := by exact_mod_cast hf
    have hh' : (H.card:ℝ) ≤ 2*Q.card := by exact_mod_cast hhalf
    have hm1 := mul_le_mul_of_nonneg_right hh' (show (0:ℝ) ≤ (U.image (cornerOuterProjection p t r)).card by positivity)
    have hm2 := mul_le_mul_of_nonneg_left hrange (show (0:ℝ) ≤ 2*d*U.card by positivity)
    have hn' : (H.card:ℝ)*(U.image (cornerOuterProjection p t r)).card ≤ 4*d*N*B*U.card := by
      nlinarith only [hf',hm1,hm2]
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
#print axioms KakeyaTwoScale.FiniteSDBound.final_corner_comparison_real
