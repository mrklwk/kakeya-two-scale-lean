module
public import KakeyaTwoScale.BoundedScaleWedgeBands
public import KakeyaTwoScale.DyadicPublishedAssembly

@[expose] public section

open Filter MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Complete the small dyadic scales uniformly, so the remaining analytic
obligation may be restricted to sufficiently large q. The large-scale
constant and threshold must both precede every finite family and band. -/
theorem dyadic_positive_bands_of_eventual (n k : ℕ) (hn : 0<n) (hk : 0<k)
    (B loss : ℝ) (hB : 1<B) (hBd : B≤n+1) (hloss : 0≤loss)
    (hlarge :
  ∃ Cband : ℝ, 0≤Cband ∧ ∀ᶠ q : ℕ in Filter.atTop, 1≤q →
    ∀ (N : ℕ) (b u : Fin N → EuclideanSpace ℝ (Fin (n+1))),
    (∀ i, ‖u i‖=1) →
    (∀ i j, i≠j → dyadicWeightCut q≤Real.arccos |inner ℝ (u i) (u j)|) →
    ∀ j < (n+1)*q,
      (∫⁻ x, ENNReal.ofReal ((originalWedgeBand k u
        (fun i => flatCylinder (b i) (u i) 1 (dyadicWeightCut q)) B j x)^
          (B/((k:ℝ)*(B-1))))) ≤
        ENNReal.ofReal (Cband*(dyadicWeightCut q)^((B/(B-1))*(1-(n+1:ℝ)/B-loss))*
          (∑ i, volume.real (flatCylinder (b i) (u i) 1 (dyadicWeightCut q)))^((n+1:ℝ)/n))) : DyadicPositiveBandEstimate n k B loss := by
  obtain ⟨C,hC,hlarge⟩ := hlarge
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp hlarge
  have heta : 0<dyadicWeightCut Q := by unfold dyadicWeightCut; positivity
  have heta1 : dyadicWeightCut Q≤1 := by
    unfold dyadicWeightCut
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hg : (1:ℝ)≤(n+1:ℝ)/n := by
    apply (le_div_iff₀ (by exact_mod_cast hn : (0:ℝ)<n)).mpr
    linarith
  have he : B/(B-1)*(1-(n+1:ℝ)/B-loss)≤0 := by
    have hdiv : (1:ℝ)≤(n+1:ℝ)/B := (le_div_iff₀ (by linarith : 0<B)).mpr (by simpa using hBd)
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    linarith
  obtain ⟨Cs,hCs,hsmall⟩ := bounded_scale_wedge_bands n k hk B ((n+1:ℝ)/n)
    (B/(B-1)*(1-(n+1:ℝ)/B-loss)) (dyadicWeightCut Q) hB hg he heta heta1
  refine ⟨max C Cs,le_trans hC (le_max_left _ _),?_⟩
  intro q hq N b u hu hsep j hj
  have hd : 0<dyadicWeightCut q := by unfold dyadicWeightCut; positivity
  by_cases hqQ : Q≤q
  · have hh := hQ q hqQ hq N b u hu hsep j hj
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
    exact le_max_left C Cs
  · have hlow : dyadicWeightCut Q≤dyadicWeightCut q := by
      unfold dyadicWeightCut
      apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
      exact pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega)
    have hhalf : dyadicWeightCut q≤1/2 := by
      unfold dyadicWeightCut
      rw [one_div]
      apply (inv_le_inv₀ (by positivity) (by norm_num)).mpr
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hq
    have hh := hsmall (dyadicWeightCut q) hlow hhalf N b u hu hsep j
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
    exact le_max_right C Cs

end KakeyaTwoScale
#print axioms KakeyaTwoScale.dyadic_positive_bands_of_eventual
