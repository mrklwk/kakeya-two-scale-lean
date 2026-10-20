module
public import KakeyaTwoScale.KatzTaoProjection

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

def verticalDoubleFiber (V : Finset (ArithmeticPoint × ArithmeticPoint)) (s t : ℚ)
    (c : ArithmeticCorner) : Finset (ArithmeticPoint × ArithmeticPoint) :=
  V.filter (fun v => arithmeticProjection s v.1 = arithmeticProjection s c.1 ∧
    arithmeticProjection t v.2 = arithmeticProjection t c.2.1)

/-- Corner slices inject into actual double-projection fibers of the chosen
vertical refinement. No uniformity bound is assumed. -/
theorem corner_slice_card_le (G : Finset ArithmeticPoint) (K : Finset ArithmeticCorner)
    (V : Finset (ArithmeticPoint × ArithmeticPoint)) (r s t : ℚ) (hrs : r ≠ s)
    (hdiff : Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint))
    (hK : K ⊆ arithmeticCorners G r s) (hV : ∀ c ∈ K, (c.1,c.2.1) ∈ V)
    {c₀ : ArithmeticCorner} (hc₀ : c₀ ∈ K) :
    (K.filter (fun c => cornerMu t c = cornerMu t c₀ ∧
      arithmeticProjection t c.2.1 = arithmeticProjection t c₀.2.1)).card ≤
      (verticalDoubleFiber V s t c₀).card := by
  apply Finset.card_le_card_of_injOn (fun c : ArithmeticCorner => (c.1,c.2.1))
  · intro c hc
    obtain ⟨hc, hm, hp⟩ := Finset.mem_filter.mp hc
    apply Finset.mem_filter.mpr
    refine ⟨hV c hc, ?_, hp⟩
    have h0 := (mem_arithmeticCorners G r s c₀).mp (hK hc₀)
    have h1 := (mem_arithmeticCorners G r s c).mp (hK hc)
    have hright : c.2.2 = c₀.2.2 := by
      apply hdiff h1.2.2.2.1 h0.2.2.2.1
      unfold cornerMu at hm
      rw [hp] at hm
      exact add_left_cancel hm
    exact h1.2.2.2.2.symm.trans ((congrArg (arithmeticProjection s) hright).trans h0.2.2.2.2)
  · intro c hc d hd he
    obtain ⟨hc, hcm, _⟩ := Finset.mem_filter.mp hc
    obtain ⟨hd, hdm, _⟩ := Finset.mem_filter.mp hd
    apply corner_first_mu_injective G r s t hrs hdiff (hK hc) (hK hd)
    exact Prod.ext (congrArg Prod.snd he) (hcm.trans hdm.symm)

/-- The small-double-fiber corner filter appearing in the rigorous iteration. -/
def goodCorners (K : Finset ArithmeticCorner) (V : Finset (ArithmeticPoint × ArithmeticPoint))
    (s t : ℚ) (L : ℕ) : Finset ArithmeticCorner :=
  K.filter (fun c => (verticalDoubleFiber V s t c).card ≤ L)

/-- Source corner-fiber upper bound for actual filtered/refined corners:
each mu fiber has at most |pi_t(G)| L points. Its small-fiber condition is
implemented by a filter, rather than assumed for the entire corner family. -/
theorem goodCorners_mu_fiber_upper (G : Finset ArithmeticPoint) (K : Finset ArithmeticCorner)
    (V : Finset (ArithmeticPoint × ArithmeticPoint)) (r s t z : ℚ) (L : ℕ) (hrs : r ≠ s)
    (hdiff : Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint))
    (hK : K ⊆ arithmeticCorners G r s) (hV : ∀ c ∈ K, (c.1,c.2.1) ∈ V) :
    ((goodCorners K V s t L).filter (fun c => cornerMu t c = z)).card ≤
      (G.image (arithmeticProjection t)).card * L := by
  let F := (goodCorners K V s t L).filter (fun c => cornerMu t c = z)
  let T := G.image (arithmeticProjection t)
  have hFK : F ⊆ K := fun c hc => (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
  have hmap : ∀ c ∈ F, arithmeticProjection t c.2.1 ∈ T := by
    intro c hc
    exact Finset.mem_image.mpr ⟨c.2.1, ((mem_arithmeticCorners G r s c).mp (hK (hFK hc))).2.1, rfl⟩
  have hbound (y) (_hy : y ∈ T) : (F.filter (fun c => arithmeticProjection t c.2.1 = y)).card ≤ L := by
    by_cases hne : (F.filter (fun c => arithmeticProjection t c.2.1 = y)).Nonempty
    · obtain ⟨c₀, hc₀⟩ := hne
      obtain ⟨hc₀, hp₀⟩ := Finset.mem_filter.mp hc₀
      have hsmall := (Finset.mem_filter.mp (Finset.mem_filter.mp hc₀).1).2
      have hsub : F.filter (fun c => arithmeticProjection t c.2.1 = y) ⊆
          K.filter (fun c => cornerMu t c = cornerMu t c₀ ∧
            arithmeticProjection t c.2.1 = arithmeticProjection t c₀.2.1) := by
        intro c hc
        obtain ⟨hc, hp⟩ := Finset.mem_filter.mp hc
        exact Finset.mem_filter.mpr ⟨hFK hc,
          (Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hc₀).2.symm, hp.trans hp₀.symm⟩
      exact (Finset.card_le_card hsub).trans
        ((corner_slice_card_le G K V r s t hrs hdiff hK hV (hFK hc₀)).trans hsmall)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  have hsum : (∑ y ∈ T, (F.filter (fun c => arithmeticProjection t c.2.1 = y)).card) = F.card := by
    simpa using Finset.sum_fiberwise_of_maps_to hmap (fun _ => (1:ℕ))
  change F.card ≤ T.card*L
  rw [← hsum]
  calc
    _ ≤ ∑ _y ∈ T, L := Finset.sum_le_sum hbound
    _ = _ := by simp
end KakeyaTwoScale
#print axioms KakeyaTwoScale.corner_slice_card_le
#print axioms KakeyaTwoScale.goodCorners_mu_fiber_upper
