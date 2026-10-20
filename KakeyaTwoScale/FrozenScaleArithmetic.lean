module
public import KakeyaTwoScale.FrozenNormalizedReset
public import KakeyaTwoScale.FixedDropHeights

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Exact dyadic shortening factor; the original width cancels. -/
theorem dyadic_length_ratio {δ : ℝ} (hδ : 0 < δ) {h H : ℕ} (hle : H ≤ h) :
    δ*(2:ℝ)^h/(δ*2^H) = (2:ℝ)^(h-H) := by
  have hh : h=H+(h-H) := by omega
  rw [hh,pow_add]
  field_simp
  congr 1
  omega

theorem fixed_drop_ratio_le {δ : ℝ} (hδ : 0 < δ) (h d : ℕ) :
    δ*(2:ℝ)^h/(δ*2^(h-d)) ≤ (2:ℝ)^d := by
  rw [dyadic_length_ratio hδ (Nat.sub_le _ _)]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- Convert the proved reset into normalized count units. -/
theorem normalized_ratio_reset {C C' h h' A q : ℝ} (hh : 0 < h) (hh' : 0 < h')
    (hc : C' ≤ A*C*(h'/h)^q) : C'/h'^q ≤ A*(C/h^q) := by
  rw [Real.div_rpow hh'.le hh.le] at hc
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hh' q)).mpr
  convert hc using 1
  ring

namespace FrozenGeometryState
variable {n k : ℕ} {T C O : Type}

def normalizedCount (S : FrozenGeometryState n k T C O) (cube : T → C) (q : ℝ) (j : Fin k) : ℝ :=
  (S.count j:ℝ)/((S.grains cube).card:ℝ)^q

theorem lower_normalized_iff (S : FrozenGeometryState n k T C O) (cube : T → C)
    (beta : Fin k → ℝ) (q : ℝ) (hne : S.tuples.Nonempty) :
    S.LowerNormalized cube beta q ↔ ∀ j, 0 < S.height j → 2*beta j ≤ S.normalizedCount cube q j := by
  classical
  have hh : (0:ℝ) < (S.grains cube).card := by exact_mod_cast Finset.card_pos.mpr (hne.image _)
  simp only [LowerNormalized,normalizedCount,le_div_iff₀ (Real.rpow_pos_of_pos hh q)]

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.dyadic_length_ratio
#print axioms KakeyaTwoScale.fixed_drop_ratio_le
#print axioms KakeyaTwoScale.normalized_ratio_reset
#print axioms KakeyaTwoScale.FrozenGeometryState.lower_normalized_iff
