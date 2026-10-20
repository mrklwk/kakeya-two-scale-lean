module
public import KakeyaTwoScale.ModelProgressionRates

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology

theorem log_rate_mul (n x y : ℕ → ℝ) (a b : ℝ)
    (hpos : ∀ᶠ i in atTop, 0 < x i ∧ 0 < y i)
    (hx : Tendsto (fun i => Real.log (x i)/n i) atTop (𝓝 a))
    (hy : Tendsto (fun i => Real.log (y i)/n i) atTop (𝓝 b)) :
    Tendsto (fun i => Real.log (x i*y i)/n i) atTop (𝓝 (a+b)) := by
  apply (hx.add hy).congr'
  filter_upwards [hpos] with i hi
  rw [Real.log_mul (ne_of_gt hi.1) (ne_of_gt hi.2),add_div]

theorem log_rate_rpow (n x : ℕ → ℝ) (a t : ℝ)
    (hpos : ∀ᶠ i in atTop, 0 < x i)
    (hx : Tendsto (fun i => Real.log (x i)/n i) atTop (𝓝 a)) :
    Tendsto (fun i => Real.log ((x i)^t)/n i) atTop (𝓝 (t*a)) := by
  apply (hx.const_mul t).congr'
  filter_upwards [hpos] with i hi
  rw [Real.log_rpow hi]
  ring

theorem ModelPrimeSequence.pred_rate {R V F P} {S : IntegerModelSequence R V F P} (T : ModelPrimeSequence S) :
    Tendsto (fun i => Real.log ((T.p i-1:ℕ):ℝ)/(S.n i:ℝ)) atTop (𝓝 V) := by
  apply log_rate_comparable (fun i => (S.n i:ℝ)) (fun i => (T.p i:ℝ))
    (fun i => ((T.p i-1:ℕ):ℝ)) V (1/2) 1 S.length_tendsto (by norm_num) (by norm_num) _ _ T.rate
  · apply Eventually.of_forall
    intro i
    have hp := (T.prime i).two_le
    exact ⟨by exact_mod_cast S.length_pos i,by exact_mod_cast (T.prime i).pos,
      by exact_mod_cast (show 0 < T.p i-1 by omega)⟩
  · apply Eventually.of_forall
    intro i
    have hp := (T.prime i).two_le
    have he : ((T.p i-1:ℕ):ℝ) = (T.p i:ℝ)-1 := by rw [Nat.cast_sub (show 1 ≤ T.p i by omega),Nat.cast_one]
    have hpR : (2:ℝ) ≤ T.p i := by exact_mod_cast hp
    rw [he]
    constructor <;> linarith

theorem ModelPrimeSequence.sampleCount_rate {R V F P} {S : IntegerModelSequence R V F P} (T : ModelPrimeSequence S) :
    Tendsto (fun i => Real.log (((T.p i-1)*T.p i:ℕ):ℝ)/(S.n i:ℝ)) atTop (𝓝 (2*V)) := by
  have hh := log_rate_mul (fun i => (S.n i:ℝ)) (fun i => ((T.p i-1:ℕ):ℝ)) (fun i => (T.p i:ℝ)) V V
    (Eventually.of_forall (fun i => ⟨by exact_mod_cast (show 0 < T.p i-1 by have := (T.prime i).two_le; omega),
      by exact_mod_cast (T.prime i).pos⟩)) T.pred_rate T.rate
  simpa only [Nat.cast_mul,two_mul] using hh

theorem StableModelSequence.heightMass_pos {R V F P} {S : IntegerModelSequence R V F P}
    {T : ModelPrimeSequence S} (U : StableModelSequence S T)
    (hR : R.Nonempty) (hF : 0 < F) (hP : ∀ r ∈ R, P r < V) (ε : ℝ) (hgap : 0 < V-F-ε*V) :
    ∀ᶠ i in atTop, 0 < samplingHeightMass (T.p i) (modelLength S T i) ε (U.H i) := by
  filter_upwards [U.nonzeroHeights_pos,modelGoodCount_eventual_bounds S T hR hF hP ε hgap] with i hb hg
  change 0 < (U.nonzeroHeights i:ℝ)*(modelGoodCount S T ε i:ℝ)*(T.p i:ℝ)^(1-ε)
  exact mul_pos (mul_pos (by exact_mod_cast hb) (by exact_mod_cast hg.1))
    (Real.rpow_pos_of_pos (by exact_mod_cast (T.prime i).pos) _)

theorem StableModelSequence.heightMass_rate {R V F P} {S : IntegerModelSequence R V F P}
    {T : ModelPrimeSequence S} (U : StableModelSequence S T)
    (hR : R.Nonempty) (hF : 0 < F) (hP : ∀ r ∈ R, P r < V) (ε : ℝ) (hgap : 0 < V-F-ε*V) :
    Tendsto (fun i => Real.log (samplingHeightMass (T.p i) (modelLength S T i) ε (U.H i))/(S.n i:ℝ))
      atTop (𝓝 ((3-2*ε)*V-F)) := by
  have hbg := log_rate_mul (fun i => (S.n i:ℝ)) (fun i => (U.nonzeroHeights i:ℝ))
    (fun i => (modelGoodCount S T ε i:ℝ)) V (V-F-ε*V) (by
      filter_upwards [U.nonzeroHeights_pos,modelGoodCount_eventual_bounds S T hR hF hP ε hgap] with i hb hg
      exact ⟨by exact_mod_cast hb,by exact_mod_cast hg.1⟩)
    U.nonzeroHeights_rate (modelGoodCount_rate S T hR hF hP ε hgap)
  have hpow := log_rate_rpow (fun i => (S.n i:ℝ)) (fun i => (T.p i:ℝ)) V (1-ε)
    (Eventually.of_forall (fun i => by exact_mod_cast (T.prime i).pos)) T.rate
  have h := log_rate_mul (fun i => (S.n i:ℝ))
    (fun i => (U.nonzeroHeights i:ℝ)*(modelGoodCount S T ε i:ℝ))
    (fun i => (T.p i:ℝ)^(1-ε)) _ _ (by
      filter_upwards [U.nonzeroHeights_pos,modelGoodCount_eventual_bounds S T hR hF hP ε hgap] with i hb hg
      exact ⟨mul_pos (by exact_mod_cast hb) (by exact_mod_cast hg.1),
        Real.rpow_pos_of_pos (by exact_mod_cast (T.prime i).pos) _⟩) hbg hpow
  change Tendsto (fun i => Real.log ((U.nonzeroHeights i:ℝ)*(modelGoodCount S T ε i:ℝ)*(T.p i:ℝ)^(1-ε))/(S.n i:ℝ))
    atTop (𝓝 ((3-2*ε)*V-F))
  convert h using 1
  congr 1
  ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.log_rate_mul
#print axioms KakeyaTwoScale.log_rate_rpow
#print axioms KakeyaTwoScale.ModelPrimeSequence.pred_rate
#print axioms KakeyaTwoScale.ModelPrimeSequence.sampleCount_rate
#print axioms KakeyaTwoScale.StableModelSequence.heightMass_pos
#print axioms KakeyaTwoScale.StableModelSequence.heightMass_rate
