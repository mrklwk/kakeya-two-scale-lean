module
public import KakeyaTwoScale.FiniteWedgeBands
public import KakeyaTwoScale.TinyWedgeCylinderEstimate

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- One literal original ordered-tuple wedge band, with the source weight. -/
def originalWedgeBand {n N : ℕ} (k : ℕ)
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B : ℝ) (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  dyadicWeightBandSum Finset.univ
    (fun f : Fin k → Fin N => tupleWedgeVolume (fun i => u (f i)))
    (fun f => (tupleWedgeVolume (fun i => u (f i)))^((k:ℝ)/B)*
      ∏ i, (T (f i)).indicator (fun _ => (1:ℝ)) x) j

theorem originalWedgeBand_nonneg {n N : ℕ} (k : ℕ)
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B : ℝ) (j : ℕ) (x) :
    0 ≤ originalWedgeBand k u T B j x := by
  apply Finset.sum_nonneg
  intro f hf
  exact mul_nonneg (Real.rpow_nonneg (tupleWedgeVolume_nonneg _) _)
    (Finset.prod_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => by norm_num) x)

theorem measurable_originalWedgeBand {n N : ℕ} (k : ℕ)
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B : ℝ) (j : ℕ)
    (hT : ∀ i, MeasurableSet (T i)) : Measurable (originalWedgeBand k u T B j) := by
  unfold originalWedgeBand dyadicWeightBandSum
  apply Finset.measurable_sum
  intro f hf
  apply Measurable.const_mul
  apply Finset.measurable_prod
  intro i hi
  exact measurable_const.indicator (hT (f i))

theorem measurable_tinyWedgeSum {n N : ℕ} (k : ℕ)
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B η : ℝ)
    (hT : ∀ i, MeasurableSet (T i)) : Measurable (tinyWedgeSum k u T B η) := by
  unfold tinyWedgeSum
  apply Finset.measurable_sum
  intro f hf
  apply Measurable.const_mul
  apply Finset.measurable_prod
  intro i hi
  exact measurable_const.indicator (hT (f i))

/-- Integrate the exact original tuple decomposition at a concave power.
Every integral remains ENNReal; no finiteness convention can erase divergence. -/
theorem original_wedge_dyadic_lintegral_le {n N k : ℕ}
    (u : Fin N → EuclideanSpace ℝ (Fin n)) (hu : ∀ i, ‖u i‖=1)
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B : ℝ)
    (hT : ∀ i, MeasurableSet (T i)) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (J : ℕ) {beta : ℝ} (hb : 0<beta) (hb1 : beta ≤ 1) :
    (∫⁻ x, ENNReal.ofReal ((∑ f : Fin k → Fin N,
      (tupleWedgeVolume (fun i => u (f i)))^((k:ℝ)/B)*
        ∏ i, (T (f i)).indicator (fun _ => (1:ℝ)) x)^beta) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal ((tinyWedgeSum k u T B (dyadicWeightCut J) x)^beta) ∂μ)+
      ∑ j ∈ Finset.range J, ∫⁻ x, ENNReal.ofReal ((originalWedgeBand k u T B j x)^beta) ∂μ := by
  have ht := ((measurable_tinyWedgeSum k u T B (dyadicWeightCut J) hT).pow_const beta).ennreal_ofReal
  have hm (j : ℕ) := ((measurable_originalWedgeBand k u T B j hT).pow_const beta).ennreal_ofReal
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal ((tinyWedgeSum k u T B (dyadicWeightCut J) x)^beta)+
        ∑ j ∈ Finset.range J, ENNReal.ofReal ((originalWedgeBand k u T B j x)^beta) ∂μ := by
      apply lintegral_mono
      intro x
      have hh := ENNReal.ofReal_le_ofReal (original_wedge_dyadic_rpow_le (k:=k) u hu T B x J hb hb1)
      have ht0 := Real.rpow_nonneg (tinyWedgeSum_nonneg (k:=k) u T B (dyadicWeightCut J) x) beta
      have hb0 (j : ℕ) := Real.rpow_nonneg (originalWedgeBand_nonneg k u T B j x) beta
      change ENNReal.ofReal _ ≤ ENNReal.ofReal
        ((tinyWedgeSum k u T B (dyadicWeightCut J) x)^beta +
          ∑ j ∈ Finset.range J, (originalWedgeBand k u T B j x)^beta) at hh
      rw [ENNReal.ofReal_add ht0 (Finset.sum_nonneg (fun j _ => hb0 j)),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => hb0 j)] at hh
      exact hh
    _ = _ := by rw [lintegral_add_left ht,lintegral_finsetSum _ (fun j _ => hm j)]

/-- Per-band analytic bounds remain explicit. Only their finite sum is
assembled here; no estimate of a non-tiny band is asserted by this lemma. -/
theorem original_wedge_integral_of_band_bounds {n N k : ℕ}
    (u : Fin N → EuclideanSpace ℝ (Fin n)) (hu : ∀ i, ‖u i‖=1)
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B : ℝ)
    (hT : ∀ i, MeasurableSet (T i)) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (J : ℕ) {beta : ℝ} (hb : 0<beta) (hb1 : beta ≤ 1)
    (tail band : ℝ≥0∞)
    (htail : (∫⁻ x, ENNReal.ofReal ((tinyWedgeSum k u T B (dyadicWeightCut J) x)^beta) ∂μ) ≤ tail)
    (hband : ∀ j < J, (∫⁻ x, ENNReal.ofReal ((originalWedgeBand k u T B j x)^beta) ∂μ) ≤ band) :
    (∫⁻ x, ENNReal.ofReal ((∑ f : Fin k → Fin N,
      (tupleWedgeVolume (fun i => u (f i)))^((k:ℝ)/B)*
        ∏ i, (T (f i)).indicator (fun _ => (1:ℝ)) x)^beta) ∂μ) ≤ tail+(J:ℝ≥0∞)*band := by
  apply (original_wedge_dyadic_lintegral_le u hu T B hT μ J hb hb1).trans
  apply add_le_add htail
  calc
    _ ≤ ∑ _j ∈ Finset.range J, band := Finset.sum_le_sum (fun j hj => hband j (Finset.mem_range.mp hj))
    _ = _ := by simp

/-- At J=(n+1)q the tiny tail is proved by the cylinder theorem. The only
remaining analytic input is the displayed bound for each original non-tiny
band; the recombination loss is exactly the number of bands. -/
theorem dyadic_cylinder_wedge_integral_assembly (n k : ℕ) (hn : 0<n) (hk : 0<k)
    (B : ℝ) (hB : 1<B) (hBd : B≤n+1)
    (hbeta : B/((k:ℝ)*(B-1))≤1) :
    ∃ Ct : ℝ, 0<Ct ∧ ∀ (q : ℕ), 1≤q → ∀ (ε Cband : ℝ), 0≤ε → 0≤Cband →
      ∀ (N : ℕ) (b u : Fin N → EuclideanSpace ℝ (Fin (n+1))),
      (∀ j, ‖u j‖=1) →
      (∀ i j, i≠j → dyadicWeightCut q≤Real.arccos |inner ℝ (u i) (u j)|) →
      let δ := dyadicWeightCut q
      let T := fun j => flatCylinder (b j) (u j) 1 δ
      let V := ∑ j, volume.real (T j)
      (∀ j < (n+1)*q,
        (∫⁻ x, ENNReal.ofReal ((originalWedgeBand k u T B j x)^(B/((k:ℝ)*(B-1))))) ≤
          ENNReal.ofReal (Cband*δ^((B/(B-1))*(1-(n+1:ℝ)/B-ε))*V^((n+1:ℝ)/n))) →
      (∫⁻ x, ENNReal.ofReal ((∑ f : Fin k → Fin N,
        (tupleWedgeVolume (fun i => u (f i)))^((k:ℝ)/B)*
          ∏ i, (T (f i)).indicator (fun _ => (1:ℝ)) x)^(B/((k:ℝ)*(B-1))))) ≤
        ENNReal.ofReal ((Ct+((n+1)*q:ℕ)*Cband)*δ^((B/(B-1))*(1-(n+1:ℝ)/B-ε))*V^((n+1:ℝ)/n)) := by
  obtain ⟨Ct,hCt,htiny⟩ := tiny_wedge_cylinder_estimate n k hn hk B hB hBd
  refine ⟨Ct,hCt,?_⟩
  intro q hq ε Cband hε hCband N b u hu hsep
  dsimp only
  let δ := dyadicWeightCut q
  let T := fun j => flatCylinder (b j) (u j) 1 δ
  let V := ∑ j, volume.real (T j)
  intro hband
  have hδ : 0<δ := by dsimp [δ,dyadicWeightCut]; positivity
  have hδhalf : δ≤1/2 := by
    have hh : (2:ℝ)^1≤(2:ℝ)^q := pow_le_pow_right₀ (by norm_num) hq
    dsimp [δ,dyadicWeightCut]
    simpa only [one_div] using (inv_le_inv₀ (by positivity : (0:ℝ)<2^q) (by norm_num : (0:ℝ)<2)).mpr (by simpa using hh)
  have hβ : 0<B/((k:ℝ)*(B-1)) := by
    have hk' : (0:ℝ)<k := by exact_mod_cast hk
    positivity
  have hV : 0≤V := Finset.sum_nonneg (fun j _ => measureReal_nonneg)
  let Z := δ^((B/(B-1))*(1-(n+1:ℝ)/B-ε))*V^((n+1:ℝ)/n)
  have hZ : 0≤Z := by dsimp [Z]; positivity
  have htail := htiny δ hδ hδhalf N b u hu hsep
  have he : dyadicWeightCut ((n+1)*q)=δ^(n+1) := dyadicWeightCut_mul (n+1) q
  rw [← he] at htail
  have hrpow : δ^((B/(B-1))*(1-(n+1:ℝ)/B))≤δ^((B/(B-1))*(1-(n+1:ℝ)/B-ε)) := by
    apply Real.rpow_le_rpow_of_exponent_ge hδ (by linarith)
    have hp : 0≤B/(B-1) := by positivity
    nlinarith
  have htail' : (∫⁻ x, ENNReal.ofReal ((tinyWedgeSum k u T B (dyadicWeightCut ((n+1)*q)) x)^
      (B/((k:ℝ)*(B-1))))) ≤ ENNReal.ofReal (Ct*Z) := by
    apply htail.trans
    apply ENNReal.ofReal_le_ofReal
    dsimp [Z]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrpow hCt.le)
      (Real.rpow_nonneg hV ((n+1:ℝ)/n))
    simpa only [mul_assoc] using hh
  have hh := original_wedge_integral_of_band_bounds u hu T B
    (fun j => (isOpen_flatCylinder _ _ _ _ (hu j)).measurableSet) volume ((n+1)*q) hβ hbeta
    (ENNReal.ofReal (Ct*Z)) (ENNReal.ofReal (Cband*Z)) htail' (fun j hj => by
      simpa only [Z,mul_assoc] using hband j hj)
  have hcast : (((n+1)*q:ℕ):ℝ≥0∞)=ENNReal.ofReal (((n+1)*q:ℕ):ℝ) := by
    exact (ENNReal.ofReal_toReal (ENNReal.natCast_ne_top ((n+1)*q))).symm
  rw [hcast,← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_add (by positivity) (by positivity)] at hh
  have hid : Ct*Z+(((n+1)*q:ℕ):ℝ)*(Cband*Z)=(Ct+((n+1)*q:ℕ)*Cband)*Z := by ring
  rw [hid] at hh
  simpa only [Z,T,V,δ,mul_assoc] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.original_wedge_dyadic_lintegral_le
#print axioms KakeyaTwoScale.original_wedge_integral_of_band_bounds
#print axioms KakeyaTwoScale.dyadic_cylinder_wedge_integral_assembly
