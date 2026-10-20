module
public import KakeyaTwoScale.RestrictedIndexUniform

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators Pointwise

/-- PZ Lemma 5, with actual integer indices, floor count, arbitrary dense A,
and a threshold uniform over all 1≤m<p. -/
theorem pz_restricted_index_lemma (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ p : ℕ, N ≤ p → p.Prime → ∀ m : ℕ,
      0 < m → m < p → ∀ A : Finset (ZMod p),
      (p:ℝ)/(m:ℝ) ≤ (A.card:ℝ) →
      ∃ G : Finset ℕ, G ⊆ Finset.Icc ((m+1)/2) m ∧
        Nat.floor ((m:ℝ)*(p:ℝ)^(-ε)) ≤ G.card ∧
        ∀ j ∈ G, (p:ℝ)^(1-ε) ≤ ((A+(positiveFieldInterval p m).image
          (fun x => (j:ZMod p)⁻¹*x)).card:ℝ) := by
  by_cases hε1 : ε < 1
  · obtain ⟨N,hN⟩ := restricted_index_uniform_nonvacuous ε hε hε1
    refine ⟨N,?_⟩
    intro p hpN hpPrime m hm0 hmp A ha
    have hp : 0 < (p:ℝ) := by exact_mod_cast hpPrime.pos
    by_cases hzero : Nat.floor ((m:ℝ)*(p:ℝ)^(-ε)) = 0
    · exact ⟨∅,by simp,by simp [hzero],by simp⟩
    · have hfloor : 1 ≤ Nat.floor ((m:ℝ)*(p:ℝ)^(-ε)) := by omega
      have hreal : 1 ≤ (m:ℝ)*(p:ℝ)^(-ε) := (Nat.one_le_floor_iff _).mp hfloor
      rw [Real.rpow_neg hp.le,← div_eq_mul_inv] at hreal
      have hem : (p:ℝ)^ε ≤ (m:ℝ) := (one_le_div (Real.rpow_pos_of_pos hp ε)).mp hreal
      exact hN p hpN hpPrime m hem hmp A ha
  · refine ⟨2,?_⟩
    intro p hp2 hpPrime m hm0 hmp A ha
    have hp : 0 < (p:ℝ) := by exact_mod_cast hpPrime.pos
    have hp1 : 1 ≤ (p:ℝ) := by exact_mod_cast (show 1 ≤ p by omega)
    have hpow : (p:ℝ) ≤ (p:ℝ)^ε := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hp1 (show (1:ℝ) ≤ ε by linarith)
    have hsmall : (m:ℝ)*(p:ℝ)^(-ε) < 1 := by
      rw [Real.rpow_neg hp.le,← div_eq_mul_inv]
      apply (div_lt_one (Real.rpow_pos_of_pos hp ε)).mpr
      exact (show (m:ℝ) < p by exact_mod_cast hmp).trans_le hpow
    have hzero : Nat.floor ((m:ℝ)*(p:ℝ)^(-ε)) = 0 := Nat.floor_eq_zero.mpr hsmall
    exact ⟨∅,by simp,by simp [hzero],by simp⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.pz_restricted_index_lemma
