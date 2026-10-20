module
public import KakeyaTwoScale.EntropyModelBounds

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped Topology BigOperators

theorem tendsto_of_abs_error {x e : ℕ → ℝ} {a : ℝ}
    (he : Tendsto e atTop (𝓝 0)) (h : ∀ᶠ i in atTop, |x i-a| ≤ e i) :
    Tendsto x atTop (𝓝 a) := by
  have hlo : Tendsto (fun i => a-e i) atTop (𝓝 a) := by simpa using tendsto_const_nhds.sub he
  have hhi : Tendsto (fun i => a+e i) atTop (𝓝 a) := by simpa using tendsto_const_nhds.add he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [h] with i hi
    have := (abs_le.mp hi).1
    linarith
  · filter_upwards [h] with i hi
    have := (abs_le.mp hi).2
    linarith

structure IntegerModelSequence (R : Finset ℚ) (V F : ℝ) (P : ℚ → ℝ) where
  n : ℕ → ℕ
  G : ℕ → Finset (ℤ × ℤ)
  M : ℕ → ℕ
  length_large : ∀ i, i+1 ≤ n i
  nonempty : ∀ i, (G i).Nonempty
  fiber_pos : ∀ i, 0 < M i
  uniform : ∀ i, ∀ y ∈ (G i).image Prod.snd, ((G i).filter (fun v => v.2=y)).card = M i
  height_rate : Tendsto (fun i => Real.log (((G i).image Prod.snd).card:ℝ)/(n i:ℝ)) atTop (𝓝 V)
  fiber_rate : Tendsto (fun i => Real.log (M i:ℝ)/(n i:ℝ)) atTop (𝓝 F)
  projection_rate : ∀ r ∈ R, Tendsto (fun i => Real.log (((G i).image (integerProjection r)).card:ℝ)/(n i:ℝ)) atTop (𝓝 (P r))

theorem IntegerModelSequence.length_pos {R V F P} (S : IntegerModelSequence R V F P) (i : ℕ) :
    0 < S.n i := by have := S.length_large i; omega

theorem IntegerModelSequence.length_tendsto {R V F P} (S : IntegerModelSequence R V F P) :
    Tendsto (fun i => (S.n i:ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun (i : ℕ) => show (i:ℝ) ≤ (S.n i:ℝ) by exact_mod_cast (Nat.le_of_lt (S.length_large i)))
    tendsto_natCast_atTop_atTop

theorem IntegerEntropyModel.uniform_size {R : Finset ℚ} {H V : ℝ} {P : ℚ → ℝ}
    {n : ℕ} {e : ℝ} {G : Finset (ℤ × ℤ)} (h : IntegerEntropyModel R H V P n e G) :
    ∃ M : ℕ, 0 < M ∧
      (∀ y ∈ G.image Prod.snd, (G.filter (fun v => v.2=y)).card = M) ∧
      |Real.log (M:ℝ)/(n:ℝ)-(H-V)| < e := by
  rcases h with ⟨hG,_hJ,_hV,_hP,hF,hU⟩
  obtain ⟨v,hv⟩ := hG
  have hy : v.2 ∈ G.image Prod.snd := Finset.mem_image.mpr ⟨v,hv,rfl⟩
  refine Exists.intro ((G.filter (fun w : ℤ × ℤ => w.2=v.2)).card) ?_
  constructor
  · apply Finset.card_pos.mpr
    exact ⟨v,Finset.mem_filter.mpr ⟨hv,rfl⟩⟩
  constructor
  · intro y hy'
    exact hU y hy' v.2 hy
  · exact hF v.2 hy

set_option maxHeartbeats 1000000 in
/-- Constructs actual uniformly fibered integer sets at increasing lengths.
All displayed logarithmic rates are proved from the finite-law discretization;
none is a supplied model-rate hypothesis. -/
theorem exists_integer_model_sequence {A : Type*} [Fintype A]
    (q : A → ℝ) (hq : ∀ a, 0 ≤ q a) (hsum : ∑ a, q a = 1)
    (f : A → ArithmeticPoint) (R : Finset ℚ) :
    Nonempty (IntegerModelSequence R (pushEntropy q (Prod.snd ∘ f))
      (pushEntropy q f-pushEntropy q (Prod.snd ∘ f))
      (fun r => pushEntropy q (arithmeticProjection r ∘ f))) := by
  let e : ℕ → ℝ := fun i => 1/((i:ℝ)+1)
  have hepos (i : ℕ) : 0 < e i := by dsimp [e]; positivity
  have hex (i : ℕ) := finite_probability_integer_discretization q hq hsum f R (e i) (hepos i) (i+1)
  choose n hn hnpos G hG using hex
  have hM (i : ℕ) := (hG i).uniform_size
  choose M hMpos hMuni hMerr using hM
  have he : Tendsto e atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  refine ⟨⟨n,G,M,hn,fun i => (hG i).1,hMpos,hMuni,?_,?_,?_⟩⟩
  · exact tendsto_of_abs_error he (Eventually.of_forall (fun i => (hG i).2.2.1.le))
  · exact tendsto_of_abs_error he (Eventually.of_forall (fun i => (hMerr i).le))
  · intro r hr
    exact tendsto_of_abs_error he (Eventually.of_forall (fun i => ((hG i).2.2.2.1 r hr).le))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.tendsto_of_abs_error
#print axioms KakeyaTwoScale.IntegerModelSequence.length_pos
#print axioms KakeyaTwoScale.IntegerModelSequence.length_tendsto
#print axioms KakeyaTwoScale.exists_integer_model_sequence

#print axioms KakeyaTwoScale.IntegerEntropyModel.uniform_size
