module
public import KakeyaTwoScale.RestrictedIndexFinite
public import KakeyaTwoScale.HalfIntervalPrimes

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators Pointwise

/-- Reduce to an actual subset of cardinality ceil(p/m), preserving the
lower density bound and obtaining the explicit upper bound used in energy. -/
theorem exists_density_subset (p m : ℕ) [NeZero p] (hm0 : 0 < m) (hmp : m ≤ p)
    (A : Finset (ZMod p)) (ha : (p:ℝ)/(m:ℝ) ≤ (A.card:ℝ)) :
    ∃ A' : Finset (ZMod p), A' ⊆ A ∧
      (p:ℝ)/(m:ℝ) ≤ (A'.card:ℝ) ∧ (A'.card:ℝ) ≤ 2*(p:ℝ)/(m:ℝ) := by
  have hm : 0 < (m:ℝ) := by exact_mod_cast hm0
  have hpm : 1 ≤ (p:ℝ)/(m:ℝ) := (one_le_div hm).mpr (by exact_mod_cast hmp)
  have hn : Nat.ceil ((p:ℝ)/(m:ℝ)) ≤ A.card := Nat.ceil_le.mpr ha
  obtain ⟨A',hsub,hcard⟩ := Finset.exists_subset_card_eq hn
  refine ⟨A',hsub,?_,?_⟩
  · rw [hcard]
    exact Nat.le_ceil _
  · rw [hcard]
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ (p:ℝ)/(m:ℝ))
    have : (Nat.ceil ((p:ℝ)/(m:ℝ)):ℝ) ≤ 2*((p:ℝ)/(m:ℝ)) := by linarith
    simpa only [mul_div_assoc] using this

/-- Finite restricted-index counting for arbitrary dense A. Every geometric
and Fourier ingredient is discharged; only explicit arithmetic parameter
inequalities are hypotheses, for the later uniform-threshold specialization. -/
theorem restricted_index_counting (p m U K L B d : ℕ) [Fact p.Prime]
    (hm0 : 0 < m) (hmp : m < p) (J : Finset ℕ) (hJne : J.Nonempty)
    (hprime : ∀ j ∈ J, j.Prime) (hsize : ∀ j ∈ J, L ≤ j ∧ j ≤ m)
    (hL : 1 ≤ L) (hscale : U*m ≤ K*p) (hcut : (K+2)*p < L^(B+1))
    (A : Finset (ZMod p)) (ha : (p:ℝ)/(m:ℝ) ≤ (A.card:ℝ)) :
    ∃ G : Finset ℕ, G ⊆ J ∧ (J.card:ℝ) ≤ 2*(G.card:ℝ) ∧
      ∀ j ∈ G, (p:ℝ)*(J.card:ℝ)/
        (8*((d:ℝ)+1)^2*(((d:ℝ)+2)^(d+1))^2*pzEnergyBracket p m U K B (d+1) J) ≤
          ((A+inverseProgression p m j).card:ℝ) := by
  obtain ⟨A',hsub,ha',haUpper⟩ := exists_density_subset p m hm0 hmp.le A ha
  obtain ⟨G,hG,hGcard,hbound⟩ := restricted_index_finite p m U K L B d hm0 hmp J hJne
    hprime hsize hL hscale hcut A' ha' haUpper
  refine ⟨G,hG,hGcard,?_⟩
  intro j hj
  apply (hbound j hj).trans
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro x hx
  obtain ⟨a,ha,b,hb,he⟩ := Finset.mem_add.mp hx
  exact Finset.mem_add.mpr ⟨a,hsub ha,b,hb,he⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_density_subset
#print axioms KakeyaTwoScale.restricted_index_counting
