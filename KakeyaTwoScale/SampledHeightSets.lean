module
public import KakeyaTwoScale.ScaledProgressionHits

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators Pointwise

def fieldFiberXs {p : ℕ} (H : Finset (ZMod p × ZMod p)) (y : ZMod p) : Finset (ZMod p) :=
  (H.filter (fun v => v.2=y)).image Prod.fst

def sampledGraph {p : ℕ} (H : Finset (ZMod p × ZMod p))
    (I J : Finset (ZMod p)) (d t : ZMod p) : Finset (ZMod p × ZMod p) :=
  H.filter (fun v => v.1 ∈ fieldProgression I d t ∧ v.2 ∈ J.image (fun j => d*j))

theorem fieldFiberXs_card {p : ℕ} (H : Finset (ZMod p × ZMod p)) (y : ZMod p) :
    (fieldFiberXs H y).card = (H.filter (fun v => v.2=y)).card := by
  apply Finset.card_image_iff.mpr
  intro v hv w hw he
  exact Prod.ext he ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm)

theorem mem_sampled_heights_iff {p : ℕ} [Fact p.Prime]
    (H : Finset (ZMod p × ZMod p)) (I J : Finset (ZMod p)) (d t y : ZMod p) :
    y ∈ (sampledGraph H I J d t).image Prod.snd ↔
      y ∈ H.image Prod.snd ∧ y ∈ J.image (fun j => d*j) ∧
        t ∈ fieldFiberXs H y-I.image (fun i => d*i) := by
  constructor
  · intro h
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp h
    obtain ⟨hv,hx,hy⟩ := Finset.mem_filter.mp hv
    obtain ⟨i,hi,hei⟩ := Finset.mem_image.mp hx
    refine ⟨Finset.mem_image.mpr ⟨v,hv,he⟩,by rwa [← he],?_⟩
    refine Finset.mem_sub.mpr ⟨v.1,Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,he⟩,rfl⟩,
      d*i,Finset.mem_image.mpr ⟨i,hi,rfl⟩,?_⟩
    linear_combination -hei
  · rintro ⟨_,hy,ht⟩
    obtain ⟨x,hx,z,hz,he⟩ := Finset.mem_sub.mp ht
    obtain ⟨v,hv,hvx⟩ := Finset.mem_image.mp hx
    obtain ⟨i,hi,hiz⟩ := Finset.mem_image.mp hz
    obtain ⟨hv,hvy⟩ := Finset.mem_filter.mp hv
    apply Finset.mem_image.mpr
    refine ⟨v,Finset.mem_filter.mpr ⟨hv,?_,by rwa [hvy]⟩,hvy⟩
    exact Finset.mem_image.mpr ⟨i,hi,by rw [← hvx,← hiz] at he; linear_combination -he⟩

theorem sampled_heights_bound {p : ℕ} [Fact p.Prime]
    (H : Finset (ZMod p × ZMod p)) (I J : Finset (ZMod p)) (d t : ZMod p) :
    ((sampledGraph H I J d t).image Prod.snd).card ≤ J.card := by
  calc
    _ ≤ (J.image (fun j => d*j)).card := Finset.card_le_card (by
      intro y hy
      exact (mem_sampled_heights_iff H I J d t y).mp hy |>.2.1)
    _ ≤ J.card := Finset.card_image_le

theorem sampled_height_count_sum (p : ℕ) [Fact p.Prime]
    (H : Finset (ZMod p × ZMod p)) (I J : Finset (ZMod p))
    (hJ : ∀ j ∈ J, j ≠ 0) :
    ∑ z ∈ nonzeroTranslationSamples p, ((sampledGraph H I J z.1 z.2).image Prod.snd).card =
      ∑ y ∈ (H.image Prod.snd).erase 0, (progressionHeightHits p (fieldFiberXs H y) I J y).card := by
  let Y := (H.image Prod.snd).erase 0
  have he (z : ZMod p × ZMod p) (hz : z ∈ nonzeroTranslationSamples p) :
      (sampledGraph H I J z.1 z.2).image Prod.snd =
        Y.filter (fun y => z ∈ progressionHeightHits p (fieldFiberXs H y) I J y) := by
    have hd : z.1 ≠ 0 := (Finset.mem_erase.mp (Finset.mem_product.mp hz).1).1
    ext y
    rw [mem_sampled_heights_iff]
    constructor
    · rintro ⟨hy,hj,ht⟩
      have hy0 : y ≠ 0 := by
        obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hj
        rw [← he]
        exact mul_ne_zero hd (hJ j hj)
      exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hy0,hy⟩,Finset.mem_filter.mpr ⟨hz,hj,ht⟩⟩
    · intro hy
      obtain ⟨hy,hz⟩ := Finset.mem_filter.mp hy
      exact ⟨(Finset.mem_erase.mp hy).2,(Finset.mem_filter.mp hz).2⟩
  rw [Finset.sum_congr rfl (fun z hz => congrArg Finset.card (he z hz))]
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,progressionHeightHits]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [Finset.sum_filter,Finset.mem_filter,hy,true_and,Y]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.fieldFiberXs_card
#print axioms KakeyaTwoScale.mem_sampled_heights_iff
#print axioms KakeyaTwoScale.sampled_heights_bound
#print axioms KakeyaTwoScale.sampled_height_count_sum
