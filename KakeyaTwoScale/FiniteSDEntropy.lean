module
public import KakeyaTwoScale.CountedLaws

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical Filter
open scoped BigOperators Topology

/-- Ordinary SD entropy for every finite probability space and every
rational pair-valued variable. Zero masses and noninjective variables are
allowed. The entropy bridge is proved, not assumed. -/
theorem FiniteSDBound.finite_probability_entropy {R : Finset ℚ} {β C : ℝ}
    (hSD : FiniteSDBound R β C) (hβ : 0 < β) (hR : R.Nonempty)
    {A : Type*} [Fintype A] (q : A → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hsum : ∑ a, q a = 1) (f : A → ArithmeticPoint) :
    finiteEntropy (Finset.univ.image (arithmeticProjection (-1) ∘ f))
      (finitePushLaw Finset.univ q (arithmeticProjection (-1) ∘ f)) ≤
      β*R.sup' hR (fun r => finiteEntropy (Finset.univ.image (arithmeticProjection r ∘ f))
        (finitePushLaw Finset.univ q (arithmeticProjection r ∘ f))) := by
  let c := fun k a => roundedCount (q a) k
  have hqseq := normalized_roundedCounts_tendsto q hq hsum
  have ht (r : ℚ) : Tendsto (fun k : ℕ =>
      finiteEntropy (Finset.univ.image (arithmeticProjection r ∘ f))
        (finitePushLaw Finset.univ (normalizedCounts (c k)) (arithmeticProjection r ∘ f))) atTop
      (𝓝 (finiteEntropy (Finset.univ.image (arithmeticProjection r ∘ f))
        (finitePushLaw Finset.univ q (arithmeticProjection r ∘ f)))) :=
    ((continuous_projection_entropy Finset.univ (arithmeticProjection r ∘ f)).tendsto q).comp hqseq
  have hs := Tendsto.finset_sup'_nhds_apply hR (fun r _ => ht r)
  apply le_of_tendsto_of_tendsto (ht (-1)) (hs.const_mul β)
  filter_upwards [roundedCount_total_eventually_pos q hq hsum] with k hk
  exact hSD.counted_entropy hβ hR (c k) hk f

/-- The source exponent now has a genuine finite-probability ordinary
entropy theorem. This is still the ordinary, not homogeneous, inequality. -/
theorem finite_entropy_625_373 :
    ∃ R : Finset ℚ, ∃ hR : R.Nonempty, (∀ r ∈ R, r ≠ -1) ∧
      ∀ (A : Type) [Fintype A] (q : A → ℝ), (∀ a, 0 ≤ q a) → (∑ a, q a = 1) →
      ∀ f : A → ArithmeticPoint,
        finiteEntropy (Finset.univ.image (arithmeticProjection (-1) ∘ f))
          (finitePushLaw Finset.univ q (arithmeticProjection (-1) ∘ f)) ≤
        (625/373:ℝ)*R.sup' hR (fun r =>
          finiteEntropy (Finset.univ.image (arithmeticProjection r ∘ f))
            (finitePushLaw Finset.univ q (arithmeticProjection r ∘ f))) := by
  obtain ⟨R,hproper,hSD⟩ := finiteSD_625_373_constant_one
  have hR := hSD.slopes_nonempty (by norm_num)
  exact ⟨R,hR,hproper,fun A _ q hq hsum f => hSD.finite_probability_entropy (by norm_num) hR q hq hsum f⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.FiniteSDBound.finite_probability_entropy
#print axioms KakeyaTwoScale.finite_entropy_625_373
