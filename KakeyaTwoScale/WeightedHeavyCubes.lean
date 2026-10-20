module
public import KakeyaTwoScale.HeavyCubeSelection

@[expose] public section

noncomputable section
open scoped BigOperators
namespace KakeyaTwoScale

/-- Heavy selection retains a definite fraction of the original nonnegative
cube objective, not merely a fraction of the number of cubes. -/
theorem weighted_heavy_retention {ι : Type*} [DecidableEq ι]
    (Q : Finset ι) (w a : ι → ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hw : ∀ q ∈ Q, 0 ≤ w q) (ha : ∀ q ∈ Q, a q ≤ 1)
    (hmass : θ * (∑ q ∈ Q, w q) ≤ ∑ q ∈ Q, w q * a q) :
    θ / 2 * (∑ q ∈ Q, w q) ≤
      ∑ q ∈ Q.filter (fun q => θ / 2 ≤ a q), w q := by
  classical
  have hb : ∀ q ∈ Q, w q * a q ≤
      (if θ / 2 ≤ a q then w q else 0) + θ / 2 * w q := by
    intro q hq
    by_cases hg : θ / 2 ≤ a q
    · simp only [hg, ↓reduceIte]
      have h := mul_le_mul_of_nonneg_left (ha q hq) (hw q hq)
      have hn : 0 ≤ θ / 2 * w q := mul_nonneg (by positivity) (hw q hq)
      nlinarith
    · simp only [hg, ↓reduceIte, zero_add]
      have h := mul_le_mul_of_nonneg_left (le_of_not_ge hg) (hw q hq)
      nlinarith
  have hs := Finset.sum_le_sum hb
  simp only [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.mul_sum] at hs
  linarith

/-- Algebraic capture preserves weight by retaining all cubes with positive
captured fraction, before paying the geometric diameter enlargement. -/
theorem weighted_positive_retention {ι : Type*} [DecidableEq ι]
    (Q : Finset ι) (w a : ι → ℝ) {θ : ℝ}
    (hw : ∀ q ∈ Q, 0 ≤ w q) (ha : ∀ q ∈ Q, a q ≤ 1)
    (hmass : θ * (∑ q ∈ Q, w q) ≤ ∑ q ∈ Q, w q * a q) :
    θ * (∑ q ∈ Q, w q) ≤ ∑ q ∈ Q.filter (fun q => 0 < a q), w q := by
  classical
  have hb : ∀ q ∈ Q, w q * a q ≤ if 0 < a q then w q else 0 := by
    intro q hq
    split_ifs with h
    · simpa using mul_le_mul_of_nonneg_left (ha q hq) (hw q hq)
    · exact mul_nonpos_of_nonneg_of_nonpos (hw q hq) (le_of_not_gt h)
  have hs := Finset.sum_le_sum hb
  rw [← Finset.sum_filter] at hs
  exact hmass.trans hs

/-- A trimmed-mass bound controls original weight in each heavy cell. -/
theorem weighted_heavy_fiber {ι : Type*} (S : Finset ι) (w a : ι → ℝ)
    {θ B : ℝ} (hθ : 0 < θ) (hw : ∀ q ∈ S, 0 ≤ w q)
    (ha : ∀ q ∈ S, θ / 2 ≤ a q)
    (hmass : ∑ q ∈ S, w q * a q ≤ B) :
    (∑ q ∈ S, w q) ≤ 2 * B / θ := by
  have hb : ∀ q ∈ S, θ / 2 * w q ≤ w q * a q := by
    intro q hq
    nlinarith [mul_le_mul_of_nonneg_left (ha q hq) (hw q hq)]
  have hs := Finset.sum_le_sum hb
  rw [← Finset.mul_sum] at hs
  apply (le_div_iff₀ hθ).2
  nlinarith

/-- Positive lower weight converts the weighted cell estimate to cardinality.
If B=C D^(-m) times total weight and weights lie in [u,v], this costs v/u. -/
theorem weighted_heavy_fiber_count {ι : Type*} (S : Finset ι) (w a : ι → ℝ)
    {θ B u : ℝ} (hθ : 0 < θ) (hu : 0 < u)
    (hw : ∀ q ∈ S, u ≤ w q) (ha : ∀ q ∈ S, θ / 2 ≤ a q)
    (hmass : ∑ q ∈ S, w q * a q ≤ B) :
    (S.card : ℝ) ≤ 2 * B / (θ * u) := by
  have hs := Finset.sum_le_sum hw
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hb := weighted_heavy_fiber S w a hθ (fun q hq => (hu.le.trans (hw q hq))) ha hmass
  have hb' := (le_div_iff₀ hθ).mp hb
  apply (le_div_iff₀ (mul_pos hθ hu)).2
  have ht := mul_le_mul_of_nonneg_right hs hθ.le
  nlinarith

/-- Selecting cubes retains every original tuple above each selected cube. -/
theorem cube_selection_full_fiber {Tuple Cube : Type*} [DecidableEq Cube]
    (Y : Finset Tuple) (cube : Tuple → Cube) (G : Finset Cube) {q : Cube}
    (hq : q ∈ G) :
    (Y.filter fun t => cube t ∈ G).filter (fun t => cube t = q) =
      Y.filter (fun t => cube t = q) := by
  classical
  ext t
  simp only [Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2 ▸ hq⟩,h.2⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.weighted_heavy_retention
#print axioms KakeyaTwoScale.weighted_positive_retention
#print axioms KakeyaTwoScale.weighted_heavy_fiber
#print axioms KakeyaTwoScale.weighted_heavy_fiber_count
#print axioms KakeyaTwoScale.cube_selection_full_fiber
