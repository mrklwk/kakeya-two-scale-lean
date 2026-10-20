module
public import KakeyaTwoScale.UniformModularModel
public import KakeyaTwoScale.FiberStability

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- PZ modeling with genuinely comparable surviving fibers. A second actual
filter retains whole fibers of size at least half the original uniform size.
At least 3/5 of both pairs and heights survive. -/
theorem exists_stable_modular_model (p : ℕ) [Fact p.Prime]
    (G : Finset (ℤ × ℤ)) (hG : G.Nonempty) (R : Finset ℚ) (hR : R.Nonempty)
    (hp : 20*(G.image Prod.snd).card ≤ p)
    (hP : ∀ r ∈ R, (G.image (integerProjection r)).card ≤ (G.image Prod.snd).card)
    (M : ℕ) (hM : ∀ y ∈ G.image Prod.snd, (G.filter (fun v => v.2 = y)).card = M) :
    ∃ H : Finset (ZMod p × ZMod p),
      (3/5:ℝ)*G.card ≤ (H.card:ℝ) ∧
      (3/5:ℝ)*(G.image Prod.snd).card ≤ ((H.image Prod.snd).card:ℝ) ∧
      (∀ y ∈ H.image Prod.snd,
        M ≤ 2*(H.filter (fun v => v.2 = y)).card ∧ (H.filter (fun v => v.2 = y)).card ≤ M) ∧
      ∀ a b : ℤ, (b:ZMod p) ≠ 0 →
        (H.image (modularRationalProjection p a b)).card ≤
          (G.image (integerProjection ((a:ℚ)/(b:ℚ)))).card * (2*(|b|+|a|+1)+1).toNat := by
  obtain ⟨r,hr⟩ := hR
  have hF : ∀ v ∈ G, (integerFiberXs G v.2).card ≤ (G.image Prod.snd).card :=
    fun v _ => (integer_fiber_le_projection G v.2 r).trans (hP r hr)
  obtain ⟨θ,hθ⟩ := exists_dense_circle_pruning p (G.image Prod.snd).card (Fact.out : p.Prime).pos hp G le_rfl hF
  let S := G.filter (fun v => θ ∈ goodCircleParameters p G v)
  let T := stableFibers G S Prod.snd
  have hSG : S ⊆ G := Finset.filter_subset _ _
  have hTS : T ⊆ S := Finset.filter_subset _ _
  have hTG : T ⊆ G := hTS.trans hSG
  have hSc := Finset.card_le_card hSG
  have hTc := Finset.card_le_card hTG
  have hloss := stableFibers_loss G S Prod.snd hSG
  have hmass : (3/5:ℝ)*G.card ≤ (T.card:ℝ) := by
    have he1 : ((G.card-T.card:ℕ):ℝ) = (G.card:ℝ)-T.card := Nat.cast_sub hTc
    have he2 : ((G.card-S.card:ℕ):ℝ) = (G.card:ℝ)-S.card := Nat.cast_sub hSc
    have hl : (G.card:ℝ)-T.card ≤ 2*((G.card:ℝ)-S.card) := by
      exact_mod_cast hloss
    linarith
  let t := (p:ℝ)*circleRepresentative θ
  let e := modularPair p t
  have he : (fun v : ℤ × ℤ => (circleBin p (v.1 • θ),circleBin p (v.2 • θ))) = e := by
    funext v
    simp only [circleBin_zsmul_eq_modularRound,e,modularPair,t]
  have hi : Set.InjOn e (↑T : Set (ℤ × ℤ)) := by
    rw [← he]
    exact (circle_pruning_injective p G θ).mono hTS
  have hv : ∀ v ∈ T, ∀ w ∈ T, (e v).2 = (e w).2 ↔ v.2 = w.2 := by
    intro v hv w hw
    rw [← he]
    exact circle_pruning_vertical_eq p G θ v w (hTS hv) (hTG hw)
  let H := T.image e
  have hcard : H.card = T.card := Finset.card_image_iff.mpr hi
  have hvert : (H.image Prod.snd).card = (T.image Prod.snd).card := by
    rw [Finset.image_image]
    exact image_card_of_same_fibers T (Prod.snd ∘ e) Prod.snd hv
  have hMpos : 0 < M := by
    obtain ⟨v,hv⟩ := hG
    rw [← hM v.2 (Finset.mem_image.mpr ⟨v,hv,rfl⟩)]
    exact Finset.card_pos.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,rfl⟩⟩
  refine ⟨H,by rwa [hcard],?_,?_,?_⟩
  · have hprodR : (G.card:ℝ) = ((G.image Prod.snd).card:ℝ)*(M:ℝ) := by
      exact_mod_cast uniform_integer_fiber_product G M hM
    have hsubR : (T.card:ℝ) ≤ ((T.image Prod.snd).card:ℝ)*(M:ℝ) := by
      exact_mod_cast subset_card_le_uniform_fibers T G hTG M hM
    have hMposR : (0:ℝ) < M := by exact_mod_cast hMpos
    rw [hvert]
    rw [hprodR] at hmass
    nlinarith
  · intro y hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨v,hvT,rfl⟩ := Finset.mem_image.mp hz
    have hfib : (H.filter (fun w => w.2 = (e v).2)).card = (T.filter (fun w => w.2 = v.2)).card := by
      convert encoded_fiber_card T e Prod.snd Prod.snd hi hv v hvT using 1 <;> congr 1 <;> ext <;> simp [H]
    rw [hfib]
    have hm := hM v.2 (Finset.mem_image.mpr ⟨v,hTG hvT,rfl⟩)
    constructor
    · rw [← hm]
      convert stableFibers_comparable G S Prod.snd hvT using 1 <;> congr 2
      exact Finset.ext (fun x => by simp only [T,Finset.mem_filter])
    · rw [← hm]
      exact Finset.card_le_card (Finset.filter_subset_filter _ hTG)
  · intro a b hb
    have h := modular_rational_projection_card_bound p t a b hb T
    apply h.trans
    apply Nat.mul_le_mul_right
    exact Finset.card_le_card (Finset.image_subset_image hTG)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_stable_modular_model
