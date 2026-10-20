module
public import KakeyaTwoScale.SeminormVisibilityBody

@[expose] public section

open Set
open scoped Pointwise
noncomputable section
namespace KakeyaTwoScale

/-- A one-sided operator error yields a quantitative inner body inclusion.
The Euclidean cutoff controls null directions of the original seminorm. -/
theorem visibilityBody_inner_comparison {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q : Seminorm ℝ E) (δ : ℝ) (hδ : 0 ≤ δ)
    (he : ∀ v, q v ≤ p v + δ * ‖v‖) :
    (1+δ)⁻¹ • seminormVisibilityBody p ⊆ seminormVisibilityBody q := by
  have hp : 0 < 1+δ := by positivity
  rintro x ⟨v,hv,rfl⟩
  have hc : 0 ≤ (1+δ)⁻¹ := inv_nonneg.mpr hp.le
  have hci : (1+δ)⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr (by linarith)
  have hq : q v ≤ 1+δ := (he v).trans (by nlinarith [hv.1,hv.2])
  constructor
  · rw [norm_smul,Real.norm_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left hv.1 hc).trans (by simpa using hci)
  · rw [map_smul_eq_mul,Real.norm_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left hq hc).trans_eq (inv_mul_cancel₀ hp.ne')

/-- Two-sided uniform directional error gives multiplicative comparison of the
actual bounded visibility bodies, even when either raw seminorm is degenerate. -/
theorem visibilityBody_comparison {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q : Seminorm ℝ E) (δ : ℝ) (hδ : 0 ≤ δ)
    (he : ∀ v, |p v - q v| ≤ δ * ‖v‖) :
    (1+δ)⁻¹ • seminormVisibilityBody p ⊆ seminormVisibilityBody q ∧
      seminormVisibilityBody q ⊆ (1+δ) • seminormVisibilityBody p := by
  have hqp (v : E) : q v ≤ p v + δ * ‖v‖ := by
    have hh := (abs_le.mp (he v)).1
    linarith
  have hpq (v : E) : p v ≤ q v + δ * ‖v‖ := by
    have hh := (abs_le.mp (he v)).2
    linarith
  refine ⟨visibilityBody_inner_comparison p q δ hδ hqp,?_⟩
  intro v hv
  have hin := visibilityBody_inner_comparison q p δ hδ hpq
  have hx : (1+δ)⁻¹ • v ∈ seminormVisibilityBody p := hin ⟨v,hv,rfl⟩
  refine ⟨(1+δ)⁻¹ • v,hx,?_⟩
  change (1+δ) • ((1+δ)⁻¹ • v) = v
  rw [smul_smul,mul_inv_cancel₀ (by positivity : (1+δ : ℝ) ≠ 0),one_smul]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.visibilityBody_inner_comparison
#print axioms KakeyaTwoScale.visibilityBody_comparison
