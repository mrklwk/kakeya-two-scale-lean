module
public import KakeyaTwoScale.CaptureHeightIntervals

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

/-- The entire bank is fixed before the scale and original line. Every captured
interval of length L/[4(n+2)] in the localized height range contains a full
bank cell of length L/[16(n+2)]. -/
theorem uniform_capture_slab_bank (n : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    ∃ K : ℕ, 0 < K ∧ ∀ L : ℝ, 0 < L → ∀ s : ℝ, |s|≤H*L →
      ∃ q∈Finset.Icc (-(K:ℤ)) (K:ℤ),
        Icc ((q:ℝ)*L/(16*(n+2:ℝ))) ((q:ℝ)*L/(16*(n+2:ℝ))+L/(16*(n+2:ℝ))) ⊆
          Icc s (s+L/(4*(n+2:ℝ))) := by
  let h : ℝ := 1/(16*(n+2:ℝ))
  have hp : 0 < h := by dsimp [h]; positivity
  obtain ⟨K,hK,hbank⟩ := bounded_height_interval H h hH hp
  refine ⟨K,hK,?_⟩
  intro L hL s hs
  have hnorm : |s/L|≤H := by
    rw [abs_div,abs_of_pos hL]
    exact (div_le_iff₀ hL).mpr hs
  obtain ⟨q,hq,hlo,hhi⟩ := hbank (s/L) (4*h) hnorm (by linarith)
  refine ⟨q,hq,Icc_subset_Icc ?_ ?_⟩
  · have hh := (div_le_iff₀ hL).mp hlo
    convert hh using 1
    dsimp [h]
    field_simp
  · have hh := mul_le_mul_of_nonneg_right hhi hL.le
    have he : (s/L+4*h)*L=s+4*h*L := by rw [add_mul,div_mul_cancel₀ _ hL.ne']
    rw [he] at hh
    convert hh using 1 <;> dsimp [h] <;> field_simp
    all_goals ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_capture_slab_bank
