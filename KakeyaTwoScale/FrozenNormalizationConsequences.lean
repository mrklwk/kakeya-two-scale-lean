module
public import KakeyaTwoScale.FrozenNormalizationExistence

@[expose] public section

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
namespace KakeyaTwoScale
namespace FrozenGeometryState

/-- Total lower normalization and actual count balance give the required
per-grain lower bound ONLY for active families. -/
theorem active_grain_lower_count {n k : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    (S : FrozenGeometryState n k T C O) (cube : T → C) (cubes : Finset C)
    (beta : Fin k → ℝ) {p q : ℝ} (hne : S.tuples.Nonempty)
    (hb : S.Balanced cube cubes p) (hl : S.LowerNormalized cube beta q)
    {g : S.Grain} (hg : g ∈ S.grains cube) (j : Fin k) (hj : 0 < S.height j) :
    beta j*((S.grains cube).card:ℝ)^(q-1) ≤
      (grainRecordCount S.tuples cube S.grain (fun y => S.parent y j) g:ℝ) := by
  have hh : (0:ℝ) < (S.grains cube).card := by exact_mod_cast Finset.card_pos.mpr (hne.image _)
  have hlo := hl j hj
  have hbal := (hb g hg).2 j |>.1
  have hdiv : beta j*((S.grains cube).card:ℝ)^q/((S.grains cube).card:ℝ) ≤
      (S.count j:ℝ)/(2*(S.grains cube).card) := by
    apply (div_le_div_iff₀ hh (by positivity : (0:ℝ)<2*(S.grains cube).card)).mpr
    nlinarith
  rw [Real.rpow_sub hh,Real.rpow_one]
  have he : beta j*(((S.grains cube).card:ℝ)^q/((S.grains cube).card:ℝ)) =
      beta j*((S.grains cube).card:ℝ)^q/((S.grains cube).card:ℝ) := by ring
  rw [he]
  exact hdiv.trans hbal

/-- An all-frozen final state has a genuinely delta-scale containing ball.
This records the geometric part of the small terminal branch; cube counting
and the analytic estimates are separate theorems. -/
theorem all_frozen_ball_radius {n k A : ℕ} {T C O : Type}
    (S : FrozenGeometryState n k T C O) (δ : ℝ)
    (hscale : S.ballRadius ≤ (A+n+5:ℝ)*δ*(∑ j, (2:ℝ)^(S.height j)))
    (hzero : ∀ j, S.height j=0) : S.ballRadius ≤ (A+n+5:ℝ)*(k:ℝ)*δ := by
  simpa only [hzero,pow_zero,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,mul_right_comm] using hscale

/-- Distinguish initial height budget from the separate tuple-statistic bin
budget. Together with positive d this controls the constructed full run. -/
theorem normalized_run_round_bound {n k d Bheight R : ℕ} {T C O : Type}
    (S : FrozenGeometryState n k T C O) (hheight : ∀ j, S.height j ≤ Bheight)
    (hR : R*d ≤ frozenHeightPotential d S.height) : R*d ≤ k*(Bheight+d) :=
  hR.trans (frozen_potential_bound S.height hheight)

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.active_grain_lower_count
#print axioms KakeyaTwoScale.FrozenGeometryState.all_frozen_ball_radius
#print axioms KakeyaTwoScale.FrozenGeometryState.normalized_run_round_bound
