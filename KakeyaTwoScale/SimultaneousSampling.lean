module
public import KakeyaTwoScale.RealEnergySelection

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- Select at half the guaranteed mean, with simultaneous cost control.
This does not assert the invalid tail estimate at the mean. -/
theorem exists_simultaneous_sample {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (hS : S.Nonempty) (height cost : ι → ℝ) (L B M : ℝ)
    (hL : 0 < L) (hB : 0 ≤ B) (hM : 0 < M)
    (hh : ∀ s ∈ S, height s ≤ M) (hc : ∀ s ∈ S, 0 ≤ cost s)
    (hlower : L ≤ ∑ s ∈ S, height s) (hupper : ∑ s ∈ S, cost s ≤ B) :
    ∃ s ∈ S, L/(2*(S.card:ℝ)) ≤ height s ∧ cost s ≤ 2*M*B/L := by
  have hSc : 0 < (S.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  let G := S.filter (fun s => L/(2*(S.card:ℝ)) ≤ height s)
  have hGS : G ⊆ S := Finset.filter_subset _ _
  have hpoint (s : ι) (hs : s ∈ S) :
      height s ≤ (if s ∈ G then M else 0)+L/(2*(S.card:ℝ)) := by
    by_cases hg : s ∈ G
    · simp only [hg,ite_true]
      exact (hh s hs).trans (le_add_of_nonneg_right (by positivity))
    · simp only [hg,ite_false,zero_add]
      by_contra h
      exact hg (Finset.mem_filter.mpr ⟨hs,le_of_not_ge h⟩)
  have hsum : (∑ s ∈ S, if s ∈ G then M else 0) = (G.card:ℝ)*M := by
    rw [Finset.sum_ite_mem,Finset.inter_eq_right.mpr hGS]
    simp
  have hbound : L ≤ (G.card:ℝ)*M+L/2 := by
    have h := hlower.trans (Finset.sum_le_sum hpoint)
    rw [Finset.sum_add_distrib,hsum] at h
    simp only [Finset.sum_const,nsmul_eq_mul] at h
    have he : (S.card:ℝ)*(L/(2*(S.card:ℝ))) = L/2 := by field_simp
    rwa [he] at h
  have hGc : 0 < (G.card:ℝ) := by
    have hn : 0 ≤ (G.card:ℝ) := Nat.cast_nonneg _
    nlinarith
  have hGne : G.Nonempty := Finset.card_pos.mp (by exact_mod_cast hGc)
  have hsumcost : ∑ s ∈ G, cost s ≤ B :=
    (Finset.sum_le_sum_of_subset_of_nonneg hGS (fun s hs _ => hc s hs)).trans hupper
  have hex : ∃ s ∈ G, cost s ≤ B/(G.card:ℝ) := by
    by_contra h
    have hstrict : ∀ s ∈ G, B/(G.card:ℝ) < cost s := by
      intro s hs
      by_contra hn
      exact h ⟨s,hs,le_of_not_gt hn⟩
    have hlt : (∑ _s ∈ G, B/(G.card:ℝ)) < ∑ s ∈ G, cost s :=
      Finset.sum_lt_sum (fun s hs => (hstrict s hs).le)
        (by obtain ⟨s,hs⟩ := hGne; exact ⟨s,hs,hstrict s hs⟩)
    have he : (∑ _s ∈ G, B/(G.card:ℝ)) = B := by simp; field_simp
    rw [he] at hlt
    linarith
  obtain ⟨s,hs,hcost⟩ := hex
  refine ⟨s,hGS hs,(Finset.mem_filter.mp hs).2,hcost.trans ?_⟩
  apply (le_div_iff₀ hL).mpr
  have hcard : L ≤ 2*(G.card:ℝ)*M := by linarith
  have h := mul_le_mul_of_nonneg_left hcard (show 0 ≤ B/(G.card:ℝ) by positivity)
  have he : B/(G.card:ℝ)*(2*(G.card:ℝ)*M) = 2*M*B := by field_simp
  rwa [he] at h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_simultaneous_sample
