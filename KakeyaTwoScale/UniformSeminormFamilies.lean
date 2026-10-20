module
public import KakeyaTwoScale.VisibilityBodyComparison
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- Joint continuity on compact coefficients gives a uniform operator-error
modulus for seminorms. Degenerate seminorms require no special normalization. -/
theorem uniform_seminorm_family_error
    {A E : Type*} [MetricSpace A] [CompactSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (s : A → Seminorm ℝ E) (hs : Continuous (fun z : A × E => s z.1 z.2))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ τ > 0, ∀ p q : A, dist p q < τ → ∀ v, |s p v - s q v| ≤ δ * ‖v‖ := by
  let : CompactSpace (sphere (0 : E) 1) := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E) 1)
  have hf : Continuous (fun z : A × sphere (0 : E) 1 => s z.1 z.2.val) :=
    hs.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  obtain ⟨τ,hτ,ht⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hf) δ hδ
  refine ⟨τ,hτ,?_⟩
  intro p q hpq v
  by_cases hv : v = 0
  · simp [hv]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    let u : sphere (0 : E) 1 := ⟨‖v‖⁻¹ • v,
      mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hv)⟩
    have hh : dist (s p u.val) (s q u.val) < δ := ht (a := (p,u)) (b := (q,u)) (by simpa using hpq)
    have he : ‖v‖ • u.val = v := by
      change ‖v‖ • (‖v‖⁻¹ • v) = v
      rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
    have hh' : |s p u.val - s q u.val| ≤ δ := (Real.dist_eq _ _ ▸ hh).le
    have hscale (a : A) : s a v = ‖v‖ * s a u.val := by
      calc
        s a v = s a (‖v‖ • u.val) := congrArg (s a) he.symm
        _ = ‖v‖ * s a u.val := by rw [map_smul_eq_mul, Real.norm_of_nonneg (norm_nonneg _)]
    calc
      |s p v - s q v| = ‖v‖ * |s p u.val - s q u.val| := by
        rw [hscale p,hscale q,← mul_sub,abs_mul,abs_of_nonneg (norm_nonneg _)]
      _ ≤ ‖v‖ * δ := mul_le_mul_of_nonneg_left hh' (norm_nonneg _)
      _ = _ := mul_comm _ _

end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_seminorm_family_error
