module
public import KakeyaTwoScale.SmoothedSumsetEnergy

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- Real-valued energy selection; zero budget is handled explicitly. -/
theorem real_energy_half_selection {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (e : ι → ℝ) (T : ℝ) (he : ∀ j ∈ J, 0 ≤ e j) (hT : 0 ≤ T)
    (hs : ∑ j ∈ J, e j ≤ T) :
    ∃ G : Finset ι, G ⊆ J ∧ (J.card:ℝ) ≤ 2*(G.card:ℝ) ∧
      ∀ j ∈ G, e j ≤ 2*T/(J.card:ℝ) := by
  by_cases hJ : J.Nonempty
  · have hc : 0 < (J.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hJ
    by_cases hT0 : T = 0
    · refine ⟨J,Finset.Subset.refl _,by linarith,?_⟩
      intro j hj
      have hle : e j ≤ ∑ i ∈ J, e i := Finset.single_le_sum he hj
      rw [hT0] at hs ⊢
      simp only [mul_zero,zero_div]
      exact hle.trans hs
    · have hTp : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
      let G := J.filter (fun j => e j ≤ 2*T/(J.card:ℝ))
      let B := J.filter (fun j => ¬e j ≤ 2*T/(J.card:ℝ))
      have hb : (B.card:ℝ)*(2*T/(J.card:ℝ)) ≤ T := by
        calc
          _ = ∑ _j ∈ B, 2*T/(J.card:ℝ) := by simp
          _ ≤ ∑ j ∈ B, e j := Finset.sum_le_sum (fun j hj => (lt_of_not_ge (Finset.mem_filter.mp hj).2).le)
          _ ≤ ∑ j ∈ J, e j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j hj _ => he j hj)
          _ ≤ T := hs
      have hbc : 2*(B.card:ℝ) ≤ (J.card:ℝ) := by
        have hh := (div_le_iff₀ hc).mp (show (2*(B.card:ℝ)*T)/(J.card:ℝ) ≤ T by convert hb using 1; ring)
        nlinarith
      have hcard : G.card+B.card = J.card := Finset.card_filter_add_card_filter_not _
      have hcardR : (G.card:ℝ)+(B.card:ℝ) = (J.card:ℝ) := by exact_mod_cast hcard
      exact ⟨G,Finset.filter_subset _ _,by linarith,fun j hj => (Finset.mem_filter.mp hj).2⟩
  · have heJ : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    subst J
    exact ⟨∅,by simp,by simp,by simp⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.real_energy_half_selection
