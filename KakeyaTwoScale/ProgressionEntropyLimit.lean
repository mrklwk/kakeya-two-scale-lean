module
public import KakeyaTwoScale.ProgressionLength
public import KakeyaTwoScale.EntropyModelBounds

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology

/-- Exact logarithmic form of the finite progression comparison. -/
theorem progression_counting_log (β L D m B K : ℝ)
    (hL : 0 < L) (hD : 0 < D) (hm : 0 < m) (hB : 0 < B) (hK : 0 < K)
    (hcomp : L/(2*D) ≤ (2*m*B/L*K)^β) :
    (β+1)*Real.log L ≤ β*(Real.log m+Real.log B+Real.log K)+
      (β+1)*Real.log 2+Real.log D := by
  have h := Real.log_le_log (div_pos hL (by positivity)) hcomp
  have he : Real.log (2*m*B/L*K) = Real.log 2+Real.log m+Real.log B-Real.log L+Real.log K := by
    rw [Real.log_mul (by positivity) (ne_of_gt hK),
      Real.log_div (by positivity) (ne_of_gt hL),
      Real.log_mul (by positivity) (ne_of_gt hB),Real.log_mul (by norm_num) (ne_of_gt hm)]
  rw [Real.log_div (ne_of_gt hL) (by positivity),
    Real.log_mul (by norm_num) (ne_of_gt hD),Real.log_rpow (by positivity),he] at h
  nlinarith only [h]

/-- The analytic limit step for the actual finite comparison. The model-rate
hypotheses are explicit: constructing sequences with these rates is a separate
remaining obligation, not an assumed homogeneous entropy inequality. -/
theorem progression_entropy_limit (β ε V F P K : ℝ) (hK : 0 < K)
    (n L D m B : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hpos : ∀ᶠ i in atTop, 0 < n i ∧ 0 < L i ∧ 0 < D i ∧ 0 < m i ∧ 0 < B i)
    (hcomp : ∀ᶠ i in atTop, L i/(2*D i) ≤ (2*m i*B i/L i*K)^β)
    (hL : Tendsto (fun i => Real.log (L i)/n i) atTop (𝓝 ((3-2*ε)*V-F)))
    (hD : Tendsto (fun i => Real.log (D i)/n i) atTop (𝓝 (2*V)))
    (hm : Tendsto (fun i => Real.log (m i)/n i) atTop (𝓝 (V-F)))
    (hB : Tendsto (fun i => Real.log (B i)/n i) atTop (𝓝 (2*V-F+P))) :
    (1-2*ε*(β+1))*V+(β-1)*F ≤ β*P := by
  have hconst (c : ℝ) : Tendsto (fun i => c/n i) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have he := le_of_tendsto_of_tendsto (hL.const_mul (β+1))
    ((((hm.add hB).add (hconst (Real.log K))).const_mul β).add
      ((hconst (Real.log 2)).const_mul (β+1)) |>.add hD) (by
      filter_upwards [hpos,hcomp] with i hi hc
      have h := div_le_div_of_nonneg_right
        (progression_counting_log β (L i) (D i) (m i) (B i) K hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2 hK hc) hi.1.le
      convert h using 1 <;> ring)
  nlinarith only [he]

/-- Removes a loss known for every sufficiently small positive error. -/
theorem homogeneous_of_small_progression_losses (β V F P ε0 : ℝ)
    (hβ : 0 ≤ β) (hV : 0 ≤ V) (hε0 : 0 < ε0)
    (h : ∀ ε : ℝ, 0 < ε → ε < ε0 →
      (1-2*ε*(β+1))*V+(β-1)*F ≤ β*P) :
    V+(β-1)*F ≤ β*P := by
  by_contra hfail
  let g := V+(β-1)*F-β*P
  have hg : 0 < g := by dsimp [g]; linarith
  let C := (β+1)*V+1
  have hC : 0 < C := by dsimp [C]; positivity
  let ε := min (ε0/2) (g/(4*C))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεlt : ε < ε0 := (min_le_left _ _).trans_lt (by linarith)
  have hsmall : ε*(4*C) ≤ g := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hh := h ε hε hεlt
  dsimp [C] at hsmall
  dsimp [g] at hg hsmall
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.progression_counting_log
#print axioms KakeyaTwoScale.progression_entropy_limit
#print axioms KakeyaTwoScale.homogeneous_of_small_progression_losses
