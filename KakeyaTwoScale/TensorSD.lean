module
public import KakeyaTwoScale.DifferenceImageBound
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

def pairTensor (G : Finset ArithmeticPoint) (n : ℕ) : Finset ((Fin n → ℚ) × (Fin n → ℚ)) :=
  (Fintype.piFinset (fun _ : Fin n => G)).image (fun v => (fun i => (v i).1,fun i => (v i).2))

theorem pairTensor_projection_card (G : Finset ArithmeticPoint) (n : ℕ) (r : ℚ) :
    ((pairTensor G n).image (vectorProjection r)).card = (G.image (arithmeticProjection r)).card^n := by
  have he : (pairTensor G n).image (vectorProjection r) =
      Fintype.piFinset (fun _ : Fin n => G.image (arithmeticProjection r)) := by
    rw [Fintype.piFinset_image]
    simp only [pairTensor,Finset.image_image,Function.comp_def,vectorProjection,
      arithmeticProjection]
    rfl
  rw [he,Fintype.card_piFinset_const]

/-- Tensor powers eliminate a fixed multiplicative constant. -/
theorem le_of_all_powers_bounded (a b C : ℝ) (hb : 0 < b)
    (h : ∀ n : ℕ, a^n ≤ C*b^n) : a ≤ b := by
  by_contra hn
  have hab : b < a := lt_of_not_ge hn
  have hr : 1 < a/b := (one_lt_div hb).mpr hab
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt C hr
  have he : (a/b)^n ≤ C := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos hb n)).mpr (h n)
  exact (not_lt_of_ge he) hn

/-- The projection estimate on arbitrary finite sets has constant one.
The proof uses actual tensor powers and the simultaneous vector encoder. -/
theorem FiniteSDBound.difference_image_bound_one {R : Finset ℚ} {β C : ℝ}
    (hSD : FiniteSDBound R β C) (hβ : 0 < β)
    (G : Finset ArithmeticPoint) (N : ℝ) (hN : 0 ≤ N)
    (hp : ∀ r ∈ R, ((G.image (arithmeticProjection r)).card:ℝ) ≤ N) :
    ((G.image (arithmeticProjection (-1))).card:ℝ) ≤ N^β := by
  by_cases hn : N = 0
  · subst N
    have hh := hSD.difference_image_bound G 0 (le_refl _) hp
    simpa [Real.zero_rpow (ne_of_gt hβ)] using hh
  · have hNp : 0 < N := lt_of_le_of_ne hN (Ne.symm hn)
    apply le_of_all_powers_bounded _ _ C (Real.rpow_pos_of_pos hNp β)
    intro n
    have hh := hSD.vector_difference_image_bound (pairTensor G n) (N^n) (pow_nonneg hN n) (by
      intro r hr
      rw [pairTensor_projection_card,Nat.cast_pow]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hp r hr) n)
    rw [pairTensor_projection_card,Nat.cast_pow] at hh
    have he : (N^n)^β = (N^β)^n := by
      rw [← Real.rpow_natCast_mul hN,← Real.rpow_mul_natCast hN,mul_comm (n:ℝ)]
    rwa [he] at hh

theorem FiniteSDBound.constant_one {R : Finset ℚ} {β C : ℝ}
    (hSD : FiniteSDBound R β C) (hβ : 0 < β) : FiniteSDBound R β 1 := by
  intro G hd N hN hp
  have h := hSD.difference_image_bound_one hβ G N hN hp
  rw [Finset.card_image_iff.mpr hd] at h
  simpa using h

theorem finiteSD_625_373_constant_one :
    ∃ R : Finset ℚ, (∀ r ∈ R, r ≠ -1) ∧ FiniteSDBound R (625/373) 1 := by
  obtain ⟨R,C,_,hproper,hSD⟩ := finiteSD_625_373
  exact ⟨R,hproper,hSD.constant_one (by norm_num)⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.pairTensor_projection_card
#print axioms KakeyaTwoScale.le_of_all_powers_bounded
#print axioms KakeyaTwoScale.FiniteSDBound.difference_image_bound_one
#print axioms KakeyaTwoScale.FiniteSDBound.constant_one
#print axioms KakeyaTwoScale.finiteSD_625_373_constant_one
