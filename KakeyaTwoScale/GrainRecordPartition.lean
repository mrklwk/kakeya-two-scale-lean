module
public import KakeyaTwoScale.BalancedActualGrains

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

theorem grain_record_image_fiber {T C G P : Type*}
    [DecidableEq T] [DecidableEq G] [DecidableEq P]
    (Y : Finset T) (cube : T → C) (grain : C → G) (piece : T → P) (origin : P → G)
    (ho : ∀ y ∈ Y, origin (piece y)=grain (cube y)) (g : G) :
    (Y.image piece).filter (fun t => origin t=g) = (Y.filter fun y => grain (cube y)=g).image piece := by
  ext t
  simp only [Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨y,hy,rfl⟩,hg⟩
    exact ⟨y,⟨hy,(ho y hy).symm.trans hg⟩,rfl⟩
  · rintro ⟨y,⟨hy,hg⟩,rfl⟩
    exact ⟨⟨y,hy,rfl⟩,(ho y hy).trans hg⟩

theorem total_record_count_eq_grain_sum {T C G P : Type*}
    [DecidableEq T] [DecidableEq G] [DecidableEq P]
    (Y : Finset T) (cube : T → C) (grain : C → G) (piece : T → P) (origin : P → G)
    (ho : ∀ y ∈ Y, origin (piece y)=grain (cube y)) :
    (Y.image piece).card = ∑ g ∈ Y.image (grain ∘ cube), grainRecordCount Y cube grain piece g := by
  have h := Finset.card_eq_sum_card_fiberwise (s:=Y.image piece) (t:=Y.image (grain ∘ cube)) (f:=origin)
    (by
      intro t ht
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
      rw [ho y hy]
      exact Finset.mem_image_of_mem (grain ∘ cube) hy)
  simpa only [grain_record_image_fiber Y cube grain piece origin ho,grainRecordCount] using h

/-- A common factor-two band gives both mean-normalized count bounds. -/
theorem band_average_bounds {G : Type*} (S : Finset G) (c : G → ℝ) {a : ℝ}
    (hS : S.Nonempty) (ha : ∀ g ∈ S, a ≤ c g ∧ c g ≤ 2*a) :
    ∀ g ∈ S, (∑ t ∈ S, c t)/(2*S.card) ≤ c g ∧ c g ≤ 2*(∑ t ∈ S, c t)/S.card := by
  have hs : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hlo := Finset.sum_le_sum (fun g hg => (ha g hg).1)
  have hup := Finset.sum_le_sum (fun g hg => (ha g hg).2)
  simp only [Finset.sum_const,nsmul_eq_mul] at hlo hup
  intro g hg
  constructor
  · apply (div_le_iff₀ (by positivity : (0:ℝ)<2*S.card)).mpr
    nlinarith [(ha g hg).1]
  · apply (le_div_iff₀ hs).mpr
    nlinarith [(ha g hg).2]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.grain_record_image_fiber
#print axioms KakeyaTwoScale.total_record_count_eq_grain_sum
#print axioms KakeyaTwoScale.band_average_bounds
