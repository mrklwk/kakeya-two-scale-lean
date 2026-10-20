module
public import KakeyaTwoScale.FiniteSDIteration

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

theorem FiniteSDBound.increase_exponent {R : Finset ℚ} {e f C : ℝ}
    (hSD : FiniteSDBound R e C) (hR : R.Nonempty) (hC : 0 ≤ C) (hef : e ≤ f) :
    FiniteSDBound R f C := by
  intro G hd N hN hp
  by_cases hn : 1 ≤ N
  · exact (hSD G hd N hN hp).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn hef) hC)
  · have he : G = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hg
      obtain ⟨r,hr⟩ := hR
      have hi : (G.image (arithmeticProjection r)).Nonempty := hg.image _
      have hc : (1:ℝ) ≤ (G.image (arithmeticProjection r)).card := by
        exact_mod_cast Finset.card_pos.mpr hi
      exact hn (hc.trans (hp r hr))
    rw [he,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg hC (Real.rpow_nonneg hN _)

/-- Katz--Tao's finite rational sums-differences exponent update, with
arbitrarily small positive loss. This is derived from the preceding SD
bound; the improved bound is not an input or an axiom. -/
theorem FiniteSDBound.katzTao_update {R : Finset ℚ} {β C : ℝ}
    (hSD : FiniteSDBound R β C) (hproper : ∀ r ∈ R, r ≠ -1)
    (hβ : 1 < β) (hβ2 : β ≤ 2) (hC : 0 < C) (η : ℝ) (hη : 0 < η) :
    ∃ P : Finset ℚ, ∃ B : ℝ, 0 < B ∧ (∀ r ∈ P, r ≠ -1) ∧
      FiniteSDBound P (realArithmeticStep β+η) B := by
  obtain ⟨M,hM⟩ := exists_nat_gt (max (2:ℝ) (102/η))
  have hm2 : (2:ℝ) < M := (le_max_left _ _).trans_lt hM
  have hm : (0:ℝ) < M := by linarith
  have hM2 : 2 ≤ M := by exact_mod_cast hm2.le
  have hratio : 102/η < (M:ℝ) := (le_max_right _ _).trans_lt hM
  have hsmall : 102/(M:ℝ) ≤ η := by
    apply (div_le_iff₀ hm).mpr
    have h := (div_lt_iff₀ hη).mp hratio
    nlinarith
  obtain ⟨B,hB,hbound⟩ := hSD.improve_with_depth hproper M hM2 hβ hβ2 hC
  refine ⟨nestedGlobalSlopes hSD hproper M,B,hB,nestedGlobalSlopes_proper hSD hproper M,?_⟩
  apply hbound.increase_exponent
  · exact ⟨0,(global_base_slopes hSD hproper M).1⟩
  · exact hB.le
  · linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.FiniteSDBound.increase_exponent
#print axioms KakeyaTwoScale.FiniteSDBound.katzTao_update
