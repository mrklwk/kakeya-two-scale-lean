module
public import KakeyaTwoScale.ProjectionEnvelopes

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology

theorem modelBudgetEnvelope_pos {R V F P} (S : IntegerModelSequence R V F P)
    (T : ModelPrimeSequence S) (hR : R.Nonempty) (hF : 0 < F) (hP : ∀ r ∈ R, P r < V) :
    ∀ᶠ i in atTop, 0 < modelBudgetEnvelope S T hR i := by
  filter_upwards [modelLength_eventual_bounds S T hR hF hP] with i hi
  have hp : (0:ℝ) < ((T.p i-1:ℕ):ℝ) := by
    exact_mod_cast (show 0 < T.p i-1 by have := (T.prime i).two_le; omega)
  have hm : (0:ℝ) < modelLength S T i := by exact_mod_cast hi.1
  have hC : (0:ℝ) < modelProjectionConstant R := by exact_mod_cast modelProjectionConstant_pos R hR
  exact mul_pos (mul_pos (mul_pos hp hm) hC) (Real.exp_pos _)

theorem modelBudgetEnvelope_rate {R V F P} (S : IntegerModelSequence R V F P)
    (T : ModelPrimeSequence S) (hR : R.Nonempty) (hF : 0 < F) (hP : ∀ r ∈ R, P r < V) :
    Tendsto (fun i => Real.log (modelBudgetEnvelope S T hR i)/(S.n i:ℝ))
      atTop (𝓝 (2*V-F+R.sup' hR P)) := by
  have hpp (i : ℕ) : (0:ℝ) < ((T.p i-1:ℕ):ℝ) := by
    exact_mod_cast (show 0 < T.p i-1 by have := (T.prime i).two_le; omega)
  have hC : (0:ℝ) < modelProjectionConstant R := by exact_mod_cast modelProjectionConstant_pos R hR
  have hpm := log_rate_mul (fun i => (S.n i:ℝ)) (fun i => ((T.p i-1:ℕ):ℝ))
    (fun i => (modelLength S T i:ℝ)) V (V-F) (by
      filter_upwards [modelLength_eventual_bounds S T hR hF hP] with i hi
      exact ⟨hpp i,by exact_mod_cast hi.1⟩) T.pred_rate (modelLength_rate S T hR hF hP)
  have hconst : Tendsto (fun i => Real.log (modelProjectionConstant R:ℝ)/(S.n i:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop S.length_tendsto
  have hpmc := log_rate_mul (fun i => (S.n i:ℝ))
    (fun i => ((T.p i-1:ℕ):ℝ)*(modelLength S T i:ℝ)) (fun _ => (modelProjectionConstant R:ℝ)) _ 0 (by
      filter_upwards [modelLength_eventual_bounds S T hR hF hP] with i hi
      exact ⟨mul_pos (hpp i) (by exact_mod_cast hi.1),hC⟩) hpm hconst
  have hh := log_rate_mul (fun i => (S.n i:ℝ))
    (fun i => ((T.p i-1:ℕ):ℝ)*(modelLength S T i:ℝ)*(modelProjectionConstant R:ℝ))
    (projectionEnvelope S hR) _ _ (by
      filter_upwards [modelLength_eventual_bounds S T hR hF hP] with i hi
      exact ⟨mul_pos (mul_pos (hpp i) (by exact_mod_cast hi.1)) hC,Real.exp_pos _⟩)
    hpmc (projectionEnvelope_rate S hR)
  change Tendsto (fun i => Real.log (((T.p i-1:ℕ):ℝ)*(modelLength S T i:ℝ)*(modelProjectionConstant R:ℝ)*projectionEnvelope S hR i)/(S.n i:ℝ))
    atTop (𝓝 (2*V-F+R.sup' hR P))
  convert hh using 1
  congr 1
  ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.modelBudgetEnvelope_pos
#print axioms KakeyaTwoScale.modelBudgetEnvelope_rate
