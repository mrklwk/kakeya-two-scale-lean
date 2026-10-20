module
public import KakeyaTwoScale.ConstructedModelComparison

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- Closed homogeneous scalar entropy inequality. One finite rational slope
family works for every normalized finite real law, including zero masses.
The integer, prime, cyclic and progression models and all their rates are
constructed in the proof; no model-rate or homogenization premise remains. -/
theorem finite_homogeneous_entropy_625_373 :
    ∃ R : Finset ℚ, ∃ hR : R.Nonempty,
      ∀ (A : Type) [Fintype A] (q : A → ℝ), (∀ a, 0 ≤ q a) → (∑ a, q a = 1) →
      ∀ f : A → ArithmeticPoint,
        (252/373:ℝ)*pushEntropy q f+(121/373:ℝ)*pushEntropy q (Prod.snd ∘ f) ≤
          (625/373:ℝ)*R.sup' hR (fun r => pushEntropy q (arithmeticProjection r ∘ f)) := by
  obtain ⟨R,hR,hordinary,hcount⟩ := finite_progression_and_entropy_625_373
  refine ⟨R,hR,?_⟩
  intro A _ q hq hsum f
  let V := pushEntropy q (Prod.snd ∘ f)
  let F := pushEntropy q f-V
  let P := fun r => pushEntropy q (arithmeticProjection r ∘ f)
  let M := R.sup' hR P
  obtain ⟨r,hr⟩ := (show R.Nonempty from hR)
  have hb := finite_conditional_entropy_bounds q hq hsum f r
  have hFnonneg : 0 ≤ F := hb.1
  have hFM : F ≤ M := hb.2.trans (Finset.le_sup' P hr)
  suffices hfinal : V+((625/373:ℝ)-1)*F ≤ (625/373:ℝ)*M by
    dsimp [V,F,M,P] at hfinal
    nlinarith only [hfinal]
  by_cases hVM : V ≤ M
  · nlinarith only [hVM,hFM]
  by_cases hFzero : F = 0
  · have ho := hordinary A q hq hsum f
    change V ≤ (625/373:ℝ)*M at ho
    rw [hFzero]
    simpa only [mul_zero,add_zero] using ho
  have hFV : 0 < F := lt_of_le_of_ne hFnonneg (Ne.symm hFzero)
  have hMV : M < V := lt_of_not_ge hVM
  have hV : 0 < V := by linarith
  have hP : ∀ r ∈ R, P r < V := fun r hr => (Finset.le_sup' P hr).trans_lt hMV
  obtain ⟨S⟩ := exists_integer_model_sequence q hq hsum f R
  obtain ⟨T⟩ := exists_model_prime_sequence S hV
  obtain ⟨U⟩ := exists_stable_model_sequence S T hR hV hP
  let ε0 := (V-M)/(2*V)
  have hε0 : 0 < ε0 := div_pos (sub_pos.mpr hMV) (by positivity)
  apply homogeneous_of_small_progression_losses (625/373) V F M ε0 (by norm_num) hV.le hε0
  intro ε hε hεsmall
  have he : ε*(2*V) < V-M := (lt_div_iff₀ (by positivity : 0 < 2*V)).mp hεsmall
  have hgap : 0 < V-F-ε*V := by nlinarith only [he,hFM,hMV]
  exact constructed_model_entropy_loss S T U (625/373) (by norm_num) hcount hR hV hFV hP ε hε hgap

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_homogeneous_entropy_625_373
