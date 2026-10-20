module
public import KakeyaTwoScale.JointProgressionSampling

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators Pointwise

theorem scaled_sumset_hit_identity (p : ℕ) [Fact p.Prime]
    (A I : Finset (ZMod p)) (y j : ZMod p) (hy : y ≠ 0) :
    ((A.image (fun x => -y⁻¹*x)+I.image (fun i => j⁻¹*i)).image (fun x => -y*x)) =
      A-I.image (fun i => (y*j⁻¹)*i) := by
  ext z
  constructor
  · intro hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_sub.mpr ⟨x,hx,(y*j⁻¹)*i,Finset.mem_image.mpr ⟨i,hi,rfl⟩,?_⟩
    field_simp
    ring
  · intro hz
    obtain ⟨x,hx,b,hb,rfl⟩ := Finset.mem_sub.mp hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_image.mpr ⟨-y⁻¹*x+j⁻¹*i,?_,?_⟩
    · exact Finset.mem_add.mpr ⟨-y⁻¹*x,Finset.mem_image.mpr ⟨x,hx,rfl⟩,
        j⁻¹*i,Finset.mem_image.mpr ⟨i,hi,rfl⟩,rfl⟩
    · field_simp
      ring

theorem scaled_sumset_hit_card (p : ℕ) [Fact p.Prime]
    (A I : Finset (ZMod p)) (y j : ZMod p) (hy : y ≠ 0) :
    (A.image (fun x => -y⁻¹*x)+I.image (fun i => j⁻¹*i)).card =
      (A-I.image (fun i => (y*j⁻¹)*i)).card := by
  rw [← scaled_sumset_hit_identity p A I y j hy]
  symm
  exact Finset.card_image_of_injective _ (fun x z h => mul_left_cancel₀ (neg_ne_zero.mpr hy) h)

theorem natCast_injOn_below (p m : ℕ) [NeZero p] (hmp : m < p) :
    Set.InjOn (fun j : ℕ => (j:ZMod p)) (↑(Finset.Icc 1 m) : Set ℕ) := by
  intro i hi j hj he
  have hi' : i < p := (Finset.mem_Icc.mp hi).2.trans_lt hmp
  have hj' : j < p := (Finset.mem_Icc.mp hj).2.trans_lt hmp
  have h := congrArg ZMod.val he
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hi',Nat.mod_eq_of_lt hj'] using h

def halfFieldInterval (p m : ℕ) : Finset (ZMod p) :=
  (Finset.Icc ((m+1)/2) m).image (fun j : ℕ => (j:ZMod p))

theorem halfFieldInterval_nonzero (p m : ℕ) [NeZero p] (hm : 0 < m) (hmp : m < p) :
    ∀ j ∈ halfFieldInterval p m, j ≠ 0 := by
  intro j hj
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
  have hlo : 1 ≤ i := by have := (Finset.mem_Icc.mp hi).1; omega
  have hhi : i < p := (Finset.mem_Icc.mp hi).2.trans_lt hmp
  intro he
  have h := congrArg ZMod.val he
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hhi,ZMod.val_zero] at h
  omega

/-- PZ's lemma gives the exact lower count of joint samples hitting one
nonzero height fiber; no independence assumption is used. -/
theorem progression_height_hits_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p → ∀ m : ℕ,
      0 < m → m < p → ∀ A : Finset (ZMod p), (p:ℝ)/(m:ℝ) ≤ (A.card:ℝ) →
      ∀ y : ZMod p, y ≠ 0 →
      (Nat.floor ((m:ℝ)*(p:ℝ)^(-ε)):ℝ)*(p:ℝ)^(1-ε) ≤
        ((progressionHeightHits p A (positiveFieldInterval p m) (halfFieldInterval p m) y).card:ℝ) := by
  obtain ⟨N,hN⟩ := pz_restricted_index_lemma ε hε
  refine ⟨N,?_⟩
  intro p _ hpN m hm hmp A ha y hy
  have hpPrime : p.Prime := Fact.out
  let A' := A.image (fun x => -y⁻¹*x)
  have hcard : A'.card = A.card := Finset.card_image_of_injective _
    (fun x z h => mul_left_cancel₀ (neg_ne_zero.mpr (inv_ne_zero hy)) h)
  obtain ⟨G,hG,hGcard,hgood⟩ := hN p hpN hpPrime m hm hmp A' (by rwa [hcard])
  let S := G.image (fun j : ℕ => (j:ZMod p))
  have hGI : G ⊆ Finset.Icc 1 m := by
    intro j hj
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp (hG hj)
    exact Finset.mem_Icc.mpr ⟨by omega,hhi⟩
  have hScard : S.card = G.card := Finset.card_image_iff.mpr ((natCast_injOn_below p m hmp).mono hGI)
  have hSJ : S ⊆ halfFieldInterval p m := Finset.image_subset_image hG
  have hhit (j : ZMod p) (hj : j ∈ S) :
      (p:ℝ)^(1-ε) ≤ ((A-(positiveFieldInterval p m).image (fun i => (y*j⁻¹)*i)).card:ℝ) := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    have h := hgood i hi
    rw [scaled_sumset_hit_card p A (positiveFieldInterval p m) y (i:ZMod p) hy] at h
    exact h
  rw [progression_height_hit_count p A _ _ (halfFieldInterval_nonzero p m hm hmp) y hy,Nat.cast_sum]
  calc
    _ ≤ (S.card:ℝ)*(p:ℝ)^(1-ε) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      rw [hScard]
      exact_mod_cast hGcard
    _ = ∑ _j ∈ S, (p:ℝ)^(1-ε) := by simp
    _ ≤ ∑ j ∈ S, ((A-(positiveFieldInterval p m).image (fun i => (y*j⁻¹)*i)).card:ℝ) :=
      Finset.sum_le_sum hhit
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hSJ (fun j _ _ => Nat.cast_nonneg _)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.scaled_sumset_hit_identity
#print axioms KakeyaTwoScale.scaled_sumset_hit_card
#print axioms KakeyaTwoScale.natCast_injOn_below
#print axioms KakeyaTwoScale.halfFieldInterval_nonzero
#print axioms KakeyaTwoScale.progression_height_hits_lower
