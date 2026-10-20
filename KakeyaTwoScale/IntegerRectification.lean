module
public import KakeyaTwoScale.ModularProjectionBound

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

def integerLift (p : ℕ) (v : ZMod p × ZMod p) : ℤ × ℤ := (v.1.val,v.2.val)

theorem integerLift_injective (p : ℕ) [NeZero p] : Function.Injective (integerLift p) := by
  intro v w h
  apply Prod.ext
  · have h1 := congrArg (fun z : ℤ × ℤ => (z.1:ZMod p)) h
    simpa [integerLift] using h1
  · have h2 := congrArg (fun z : ℤ × ℤ => (z.2:ZMod p)) h
    simpa [integerLift] using h2

theorem integer_residue_card_bound (p : ℕ) [NeZero p] (S : Finset ℤ) (M : ℤ)
    (hS : ∀ z ∈ S, |z| ≤ M*(p:ℤ)) :
    S.card ≤ (S.image (fun z : ℤ => (z:ZMod p))).card * (2*M+1).toNat := by
  have hp : (0:ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  let T := (S.image (fun z : ℤ => (z:ZMod p))).product (Finset.Icc (-M) M)
  let e := fun z : ℤ => ((z:ZMod p),z/(p:ℤ))
  have hm : ∀ z ∈ S, e z ∈ T := by
    intro z hz
    refine Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,Finset.mem_Icc.mpr ⟨?_,?_⟩⟩
    · apply (Int.le_ediv_iff_mul_le hp).mpr
      have h := (abs_le.mp (hS z hz)).1
      nlinarith
    · change z/(p:ℤ) ≤ M
      have hzlt : z < (M+1)*(p:ℤ) := by have h := (abs_le.mp (hS z hz)).2; nlinarith
      have h := (Int.ediv_lt_iff_lt_mul hp).mpr hzlt
      omega
  have hi : Function.Injective e := by
    intro x y he
    have hmod : x%(p:ℤ) = y%(p:ℤ) := by
      have h := congrArg (fun z : ZMod p × ℤ => (z.1.val:ℤ)) he
      simpa only [e,ZMod.val_intCast] using h
    have hdiv : x/(p:ℤ) = y/(p:ℤ) := congrArg Prod.snd he
    have hx := Int.emod_add_mul_ediv x (p:ℤ)
    have hy := Int.emod_add_mul_ediv y (p:ℤ)
    rw [hmod,hdiv] at hx
    omega
  calc
    S.card = (S.image e).card := (Finset.card_image_of_injective S hi).symm
    _ ≤ T.card := Finset.card_le_card (by intro z hz; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz; exact hm x hx)
    _ = _ := by
      simpa only [T,Finset.instSProd,SProd.sprod,Int.card_Icc,sub_neg_eq_add,two_mul,add_assoc,add_comm] using
        Finset.card_product (S.image (fun z : ℤ => (z:ZMod p))) (Finset.Icc (-M) M)

/-- Canonical representatives preserve joint and vertical sizes exactly;
integer projection sizes grow by an explicit coefficient-only factor. The
factor is independent of the prime and the set. -/
theorem integerLift_projection_card_bound (p : ℕ) [NeZero p] (a b : ℤ)
    (G : Finset (ZMod p × ZMod p)) :
    ((G.image (integerLift p)).image (integerLinearForm a b)).card ≤
      (G.image (modularLinearForm p a b)).card * (2*(|a|+|b|)+1).toNat := by
  let S := (G.image (integerLift p)).image (integerLinearForm a b)
  have hS : ∀ z ∈ S, |z| ≤ (|a|+|b|)*(p:ℤ) := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
    have hx : |((integerLift p w).1:ℤ)| ≤ (p:ℤ) := by
      simpa only [integerLift,Int.natCast_nonneg,abs_of_nonneg] using
        (show (w.1.val:ℤ) ≤ (p:ℤ) by exact_mod_cast (ZMod.val_lt w.1).le)
    have hy : |((integerLift p w).2:ℤ)| ≤ (p:ℤ) := by
      simpa only [integerLift,Int.natCast_nonneg,abs_of_nonneg] using
        (show (w.2.val:ℤ) ≤ (p:ℤ) by exact_mod_cast (ZMod.val_lt w.2).le)
    have h1 := mul_le_mul_of_nonneg_left hx (abs_nonneg a)
    have h2 := mul_le_mul_of_nonneg_left hy (abs_nonneg b)
    have ht := abs_add_le (a*(integerLift p w).1) (b*(integerLift p w).2)
    simp only [abs_mul] at ht
    dsimp only [integerLinearForm]
    nlinarith
  have he : S.image (fun z : ℤ => (z:ZMod p)) = G.image (modularLinearForm p a b) := by
    simp only [S,Finset.image_image,Function.comp_def,integerLinearForm,integerLift,
      Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val]
    rfl
  have h := integer_residue_card_bound p S (|a|+|b|) hS
  rwa [he] at h

theorem integerLift_vertical_fibers (p : ℕ) [NeZero p] (G : Finset (ZMod p × ZMod p)) :
    (G.image (integerLift p)).card = G.card ∧
    ((G.image (integerLift p)).image Prod.snd).card = (G.image Prod.snd).card ∧
    ∀ v ∈ G,
      ((G.image (integerLift p)).filter (fun w => w.2 = (integerLift p v).2)).card =
        (G.filter (fun w => w.2 = v.2)).card := by
  have he (v w : ZMod p × ZMod p) : (integerLift p v).2 = (integerLift p w).2 ↔ v.2 = w.2 := by
    constructor
    · intro h
      have hh := congrArg (fun z : ℤ => (z:ZMod p)) h
      simpa [integerLift] using hh
    · intro h
      simp only [integerLift,h]
  refine ⟨Finset.card_image_of_injective _ (integerLift_injective p),?_,?_⟩
  · rw [Finset.image_image]
    exact image_card_of_same_fibers G (Prod.snd ∘ integerLift p) Prod.snd (fun v _ w _ => he v w)
  · intro v hv
    convert encoded_fiber_card G (integerLift p) Prod.snd Prod.snd (integerLift_injective p).injOn
      (fun v _ w _ => he v w) v hv using 1 <;> congr 1 <;> ext <;> simp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.integerLift_injective
#print axioms KakeyaTwoScale.integer_residue_card_bound
#print axioms KakeyaTwoScale.integerLift_projection_card_bound
#print axioms KakeyaTwoScale.integerLift_vertical_fibers
