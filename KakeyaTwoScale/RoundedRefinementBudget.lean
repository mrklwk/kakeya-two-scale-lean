module
public import KakeyaTwoScale.ThresholdRegime

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Filter
open scoped Topology

/-- For a fixed finite family count, the actual rounded deletion budget
fits inside the current uniform mass, uniformly in every level and every
large balanced dataset. No asymptotic rounding premise is assumed. -/
theorem eventually_rounded_refinement_budget (M F : ℕ) (hM : 2 ≤ M) :
    ∀ᶠ N : ℕ in atTop, ∀ k < M, ∀ W : ℕ, N^2 ≤ W →
      4*(iterationPopularity N M)*F*(iterationMassThreshold N W M (k+1)) +
        4*F*W ≤ (iterationPopularity N M)*(iterationMassThreshold N W M k) := by
  have he := eventually_refinement_loss_dominated M (by omega) (8*F) (4*F) 1
    (by positivity) (by norm_num)
  have heN : ∀ᶠ N : ℕ in atTop, ∀ k ≤ M,
      (8*F:ℝ)*iterationEpsilon N M (k+1)+(4*F:ℝ)*(N:ℝ)^(-100/(M:ℝ)) ≤
        iterationEpsilon N M k := by
    simpa only [one_mul] using (tendsto_natCast_atTop_atTop.eventually he :
      ∀ᶠ N : ℕ in atTop, ∀ k ≤ M,
        (8*F:ℝ)*iterationEpsilon N M (k+1)+(4*F:ℝ)*(N:ℝ)^(-100/(M:ℝ)) ≤
          1*iterationEpsilon N M k)
  filter_upwards [heN,eventually_ge_atTop (2:ℕ)] with N he hN
  intro k hk W hW
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hW' : (N:ℝ)^2 ≤ W := by exact_mod_cast hW
  have hround := (large_family_rounding_inputs N W M (k+1) hN' hW' hM (by omega)).1
  have hE1 := (iterationMassThreshold_bounds N W M (k+1) hround).2
  have hE0 : iterationEpsilon N M k*(W:ℝ) ≤ (iterationMassThreshold N W M k:ℝ) := Nat.le_ceil _
  let d := iterationPopularity N M
  have hd := iterationPopularity_inverse N M hN'
  have hd' : (0:ℝ) < d := by exact_mod_cast hd.1
  have hinv : (1:ℝ) ≤ (d:ℝ)*(N:ℝ)^(-100/(M:ℝ)) := by
    have h := (div_le_iff₀ hd').mp hd.2
    nlinarith only [h]
  have hdom := he k (by omega)
  have h1 := mul_le_mul_of_nonneg_left hE1 (show (0:ℝ) ≤ 4*d*F by positivity)
  have h2 := mul_le_mul_of_nonneg_left hinv (show (0:ℝ) ≤ 4*F*W by positivity)
  have h3 := mul_le_mul_of_nonneg_left hdom (show (0:ℝ) ≤ (d:ℝ)*W by positivity)
  have h4 := mul_le_mul_of_nonneg_left hE0 hd'.le
  have hfinal : (4:ℝ)*d*F*(iterationMassThreshold N W M (k+1)) +4*F*W ≤
      (d:ℝ)*(iterationMassThreshold N W M k) := by nlinarith only [h1,h2,h3,h4]
  exact_mod_cast hfinal

end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_rounded_refinement_budget
