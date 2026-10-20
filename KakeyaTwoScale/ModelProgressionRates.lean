module
public import KakeyaTwoScale.HalfFiberRates

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology

def modelLength {R V F P} (S : IntegerModelSequence R V F P) (T : ModelPrimeSequence S) (i : ℕ) : ℕ :=
  modelProgressionLength (T.p i) (S.halfFiberSize i)

theorem modelLength_eventual_bounds {R V F P} (S : IntegerModelSequence R V F P)
    (T : ModelPrimeSequence S) (hR : R.Nonempty) (hF : 0 < F) (hP : ∀ r ∈ R, P r < V) :
    ∀ᶠ i in atTop, 0 < modelLength S T i ∧ modelLength S T i < T.p i ∧
      (T.p i:ℝ)/(modelLength S T i:ℝ) ≤ S.halfFiberSize i ∧
      (T.p i:ℝ)/(S.halfFiberSize i:ℝ) ≤ modelLength S T i ∧
      (modelLength S T i:ℝ) ≤ 2*((T.p i:ℝ)/(S.halfFiberSize i:ℝ)) := by
  filter_upwards [S.eventual_halfFiber_bounds T hR hF hP] with i hi
  exact modelProgressionLength_bounds (T.p i) (S.halfFiberSize i) hi.1 hi.2.1 hi.2.2

theorem modelLength_rate {R V F P} (S : IntegerModelSequence R V F P)
    (T : ModelPrimeSequence S) (hR : R.Nonempty) (hF : 0 < F) (hP : ∀ r ∈ R, P r < V) :
    Tendsto (fun i => Real.log (modelLength S T i:ℝ)/(S.n i:ℝ)) atTop (𝓝 (V-F)) := by
  have hx : Tendsto (fun i => Real.log ((T.p i:ℝ)/(S.halfFiberSize i:ℝ))/(S.n i:ℝ)) atTop (𝓝 (V-F)) := by
    apply (T.rate.sub S.halfFiber_rate).congr'
    apply Eventually.of_forall
    intro i
    dsimp only
    rw [Real.log_div (by exact_mod_cast (T.prime i).ne_zero)
      (by exact_mod_cast Nat.ne_of_gt (S.halfFiber_bounds i).1),sub_div]
  apply log_rate_comparable (fun i => (S.n i:ℝ)) _ _ (V-F) 1 2 S.length_tendsto (by norm_num) (by norm_num) _ _ hx
  · filter_upwards [modelLength_eventual_bounds S T hR hF hP] with i hi
    exact ⟨by exact_mod_cast S.length_pos i,div_pos (by exact_mod_cast (T.prime i).pos)
      (by exact_mod_cast (S.halfFiber_bounds i).1),by exact_mod_cast hi.1⟩
  · filter_upwards [modelLength_eventual_bounds S T hR hF hP] with i hi
    exact ⟨by simpa only [one_mul] using hi.2.2.2.1,hi.2.2.2.2⟩

def modelFloorArgument {R V F P} (S : IntegerModelSequence R V F P)
    (T : ModelPrimeSequence S) (ε : ℝ) (i : ℕ) : ℝ :=
  (modelLength S T i:ℝ)*(T.p i:ℝ)^(-ε)

def modelGoodCount {R V F P} (S : IntegerModelSequence R V F P)
    (T : ModelPrimeSequence S) (ε : ℝ) (i : ℕ) : ℕ := Nat.floor (modelFloorArgument S T ε i)

theorem modelFloorArgument_rate {R V F P} (S : IntegerModelSequence R V F P)
    (T : ModelPrimeSequence S) (hR : R.Nonempty) (hF : 0 < F) (hP : ∀ r ∈ R, P r < V) (ε : ℝ) :
    Tendsto (fun i => Real.log (modelFloorArgument S T ε i)/(S.n i:ℝ)) atTop (𝓝 (V-F-ε*V)) := by
  have hh := (modelLength_rate S T hR hF hP).add (T.rate.const_mul (-ε))
  have he : V-F+(-ε)*V = V-F-ε*V := by ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [modelLength_eventual_bounds S T hR hF hP] with i hi
  have hp : (0:ℝ) < T.p i := by exact_mod_cast (T.prime i).pos
  have hm : (0:ℝ) < modelLength S T i := by exact_mod_cast hi.1
  dsimp [modelFloorArgument]
  rw [Real.log_mul (ne_of_gt hm) (ne_of_gt (Real.rpow_pos_of_pos hp _)),Real.log_rpow hp]
  ring

theorem modelGoodCount_eventual_bounds {R V F P} (S : IntegerModelSequence R V F P)
    (T : ModelPrimeSequence S) (hR : R.Nonempty) (hF : 0 < F) (hP : ∀ r ∈ R, P r < V)
    (ε : ℝ) (hgap : 0 < V-F-ε*V) :
    ∀ᶠ i in atTop, 0 < modelGoodCount S T ε i ∧
      modelFloorArgument S T ε i/2 ≤ (modelGoodCount S T ε i:ℝ) ∧
      (modelGoodCount S T ε i:ℝ) ≤ modelFloorArgument S T ε i := by
  have hpos : ∀ᶠ i in atTop, 0 < (S.n i:ℝ) ∧ 0 < modelFloorArgument S T ε i := by
    filter_upwards [modelLength_eventual_bounds S T hR hF hP] with i hi
    exact ⟨by exact_mod_cast S.length_pos i,mul_pos (by exact_mod_cast hi.1)
      (Real.rpow_pos_of_pos (by exact_mod_cast (T.prime i).pos) _)⟩
  have ht := log_rate_pos_atTop _ _ _ hgap S.length_tendsto hpos (modelFloorArgument_rate S T hR hF hP ε)
  filter_upwards [ht.eventually (eventually_ge_atTop (2:ℝ))] with i hi
  have hlo := floor_ge_half _ hi
  have hhi := Nat.floor_le (show 0 ≤ modelFloorArgument S T ε i by linarith)
  refine ⟨?_,hlo,hhi⟩
  have h : (0:ℝ) < (modelGoodCount S T ε i:ℝ) := by
    change 0 < (Nat.floor (modelFloorArgument S T ε i):ℝ)
    linarith
  exact_mod_cast h

theorem modelGoodCount_rate {R V F P} (S : IntegerModelSequence R V F P)
    (T : ModelPrimeSequence S) (hR : R.Nonempty) (hF : 0 < F) (hP : ∀ r ∈ R, P r < V)
    (ε : ℝ) (hgap : 0 < V-F-ε*V) :
    Tendsto (fun i => Real.log (modelGoodCount S T ε i:ℝ)/(S.n i:ℝ)) atTop (𝓝 (V-F-ε*V)) := by
  apply log_rate_comparable (fun i => (S.n i:ℝ)) (modelFloorArgument S T ε)
    (fun i => (modelGoodCount S T ε i:ℝ)) _ (1/2) 1 S.length_tendsto (by norm_num) (by norm_num) _ _
      (modelFloorArgument_rate S T hR hF hP ε)
  · filter_upwards [modelLength_eventual_bounds S T hR hF hP,modelGoodCount_eventual_bounds S T hR hF hP ε hgap]
      with i hi hg
    exact ⟨by exact_mod_cast S.length_pos i,mul_pos (by exact_mod_cast hi.1)
      (Real.rpow_pos_of_pos (by exact_mod_cast (T.prime i).pos) _),by exact_mod_cast hg.1⟩
  · filter_upwards [modelGoodCount_eventual_bounds S T hR hF hP ε hgap] with i hi
    exact ⟨by linarith [hi.2.1],by simpa only [one_mul] using hi.2.2⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.modelLength_eventual_bounds
#print axioms KakeyaTwoScale.modelLength_rate
#print axioms KakeyaTwoScale.modelFloorArgument_rate
#print axioms KakeyaTwoScale.modelGoodCount_eventual_bounds
#print axioms KakeyaTwoScale.modelGoodCount_rate
