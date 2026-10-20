module
public import KakeyaTwoScale.BudgetEnvelopeRate
public import KakeyaTwoScale.ProgressionEntropyLimit

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology

def FiniteProgressionCounting (R : Finset ℚ) (β : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ (p : ℕ) [Fact p.Prime], N ≤ p → ∀ m : ℕ,
    0 < m → m < p → 0 < Nat.floor ((m:ℝ)*(p:ℝ)^(-ε)) →
    ∀ H : Finset (ZMod p × ZMod p), ((H.image Prod.snd).erase 0).Nonempty →
    (∀ y ∈ (H.image Prod.snd).erase 0, (p:ℝ)/(m:ℝ) ≤ ((H.filter (fun v => v.2=y)).card:ℝ)) →
    (∀ r ∈ R, (r.den:ZMod p) ≠ 0) →
    samplingHeightMass p m ε H/(2*((p-1)*p:ℕ)) ≤
      (2*(m:ℝ)*(samplingProjectionBudget p m H (R.image slopeCoefficients):ℝ)/
        samplingHeightMass p m ε H*(slopeRectificationBudget R:ℝ))^β

theorem ModelPrimeSequence.tendsto {R V F P} {S : IntegerModelSequence R V F P}
    (T : ModelPrimeSequence S) (hV : 0 < V) : Tendsto (fun i => (T.p i:ℝ)) atTop atTop := by
  apply log_rate_pos_atTop (fun i => (S.n i:ℝ)) _ V hV S.length_tendsto _ T.rate
  exact Eventually.of_forall (fun i => ⟨by exact_mod_cast S.length_pos i,by exact_mod_cast (T.prime i).pos⟩)

theorem constructed_model_comparison {R V F P} (S : IntegerModelSequence R V F P)
    (T : ModelPrimeSequence S) (U : StableModelSequence S T)
    (β : ℝ) (hβ : 0 ≤ β) (hcount : FiniteProgressionCounting R β)
    (hR : R.Nonempty) (hV : 0 < V) (hF : 0 < F) (hP : ∀ r ∈ R, P r < V)
    (ε : ℝ) (hε : 0 < ε) (hgap : 0 < V-F-ε*V) :
    ∀ᶠ i in atTop,
      samplingHeightMass (T.p i) (modelLength S T i) ε (U.H i)/(2*((T.p i-1)*T.p i:ℕ)) ≤
        (2*(modelLength S T i:ℝ)*modelBudgetEnvelope S T hR i/
          samplingHeightMass (T.p i) (modelLength S T i) ε (U.H i)*(slopeRectificationBudget R:ℝ))^β := by
  obtain ⟨N,hN⟩ := hcount ε hε
  have hpN : ∀ᶠ i in atTop, N ≤ T.p i := by
    filter_upwards [(T.tendsto hV).eventually (eventually_ge_atTop (N:ℝ))] with i hi
    exact_mod_cast hi
  filter_upwards [hpN,modelLength_eventual_bounds S T hR hF hP,
    modelGoodCount_eventual_bounds S T hR hF hP ε hgap,U.nonzeroHeights_pos,
    U.halfFiber_density,U.heightMass_pos hR hF hP ε hgap,modelBudgetEnvelope_bound U hR]
    with i hp hm hg hb hf hL hB
  let : Fact (T.p i).Prime := ⟨T.prime i⟩
  have hY : (((U.H i).image Prod.snd).erase 0).Nonempty := Finset.card_pos.mp hb
  have hdensity : ∀ y ∈ ((U.H i).image Prod.snd).erase 0,
      (T.p i:ℝ)/(modelLength S T i:ℝ) ≤ (((U.H i).filter (fun v => v.2=y)).card:ℝ) := by
    intro y hy
    exact hm.2.2.1.trans (by exact_mod_cast hf y (Finset.mem_of_mem_erase hy))
  have hraw := hN (T.p i) hp (modelLength S T i) hm.1 hm.2.1 hg.1 (U.H i) hY hdensity (T.denominators i)
  apply hraw.trans
  apply Real.rpow_le_rpow (by positivity) _ hβ
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply div_le_div_of_nonneg_right _ hL.le
  exact mul_le_mul_of_nonneg_left hB (by positivity)

/-- Every rate and eventual side condition in the analytic comparison is
now supplied by the constructed integer, prime and stable modular models. -/
theorem constructed_model_entropy_loss {R V F P} (S : IntegerModelSequence R V F P)
    (T : ModelPrimeSequence S) (U : StableModelSequence S T)
    (β : ℝ) (hβ : 0 ≤ β) (hcount : FiniteProgressionCounting R β)
    (hR : R.Nonempty) (hV : 0 < V) (hF : 0 < F) (hP : ∀ r ∈ R, P r < V)
    (ε : ℝ) (hε : 0 < ε) (hgap : 0 < V-F-ε*V) :
    (1-2*ε*(β+1))*V+(β-1)*F ≤ β*R.sup' hR P := by
  apply progression_entropy_limit β ε V F (R.sup' hR P) (slopeRectificationBudget R)
    (by exact_mod_cast slopeRectificationBudget_pos R hR)
    (fun i => (S.n i:ℝ))
    (fun i => samplingHeightMass (T.p i) (modelLength S T i) ε (U.H i))
    (fun i => (((T.p i-1)*T.p i:ℕ):ℝ)) (fun i => (modelLength S T i:ℝ))
    (modelBudgetEnvelope S T hR) S.length_tendsto _
    (constructed_model_comparison S T U β hβ hcount hR hV hF hP ε hε hgap)
    (U.heightMass_rate hR hF hP ε hgap) T.sampleCount_rate
    (modelLength_rate S T hR hF hP) (modelBudgetEnvelope_rate S T hR hF hP)
  filter_upwards [U.heightMass_pos hR hF hP ε hgap,modelLength_eventual_bounds S T hR hF hP,
    modelBudgetEnvelope_pos S T hR hF hP] with i hL hm hB
  have hp := (T.prime i).two_le
  exact ⟨by exact_mod_cast S.length_pos i,hL,
    by exact_mod_cast Nat.mul_pos (show 0 < T.p i-1 by omega) (T.prime i).pos,
    by exact_mod_cast hm.1,hB⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.ModelPrimeSequence.tendsto
#print axioms KakeyaTwoScale.constructed_model_comparison
#print axioms KakeyaTwoScale.constructed_model_entropy_loss
