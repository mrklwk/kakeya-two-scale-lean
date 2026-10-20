module
public import KakeyaTwoScale.WedgeBandIntegralAssembly
public import KakeyaTwoScale.WedgeBandLossAbsorption
public import KakeyaTwoScale.PublishedZahlIntegral

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The remaining non-tiny band estimate, with one constant chosen before all
scales, families and band indices. This definition does not assert it. The
ambient dimension is n+1 and the original ordered tuples are unchanged. -/
def DyadicPositiveBandEstimate (n k : ℕ) (B loss : ℝ) : Prop :=
  ∃ Cband : ℝ, 0≤Cband ∧ ∀ q : ℕ, 1≤q →
    ∀ (N : ℕ) (b u : Fin N → EuclideanSpace ℝ (Fin (n+1))),
    (∀ i, ‖u i‖=1) →
    (∀ i j, i≠j → dyadicWeightCut q≤Real.arccos |inner ℝ (u i) (u j)|) →
    ∀ j < (n+1)*q,
      (∫⁻ x, ENNReal.ofReal ((originalWedgeBand k u
        (fun i => flatCylinder (b i) (u i) 1 (dyadicWeightCut q)) B j x)^
          (B/((k:ℝ)*(B-1))))) ≤
        ENNReal.ofReal (Cband*(dyadicWeightCut q)^((B/(B-1))*(1-(n+1:ℝ)/B-loss))*
          (∑ i, volume.real (flatCylinder (b i) (u i) 1 (dyadicWeightCut q)))^((n+1:ℝ)/n))

/-- Uniform non-tiny band estimates at epsilon/2, the proved tiny tail, finite
concave recombination and band-count absorption give the exact dyadic norm
estimate at epsilon. No all-radius statement or positive-band proof is claimed. -/
theorem dyadic_norm_estimate_of_positive_bands (n k : ℕ) (hn : 0<n) (hk : 0<k)
    (B : ℝ) (hB : 1<B) (hBd : B≤n+1) (hbeta : B/((k:ℝ)*(B-1))≤1)
    (ε : ℝ) (hε : 0<ε) (H : DyadicPositiveBandEstimate n k B (ε/2)) :
    ∃ Cnorm : ℝ, 0<Cnorm ∧ ∀ q : ℕ, 1≤q →
      ∀ (N : ℕ) (b u : Fin N → EuclideanSpace ℝ (Fin (n+1))),
      (∀ i, ‖u i‖=1) →
      (∀ i j, i≠j → dyadicWeightCut q≤Real.arccos |inner ℝ (u i) (u j)|) →
      eLpNorm (multilinearKakeyaFunction k u
        (fun i => flatCylinder (b i) (u i) 1 (dyadicWeightCut q)) B)
        (ENNReal.ofReal (B/(B-1))) volume ≤
      ENNReal.ofReal (Cnorm*(dyadicWeightCut q)^(1-(n+1:ℝ)/B-ε)*
        (∑ i, volume.real (flatCylinder (b i) (u i) 1 (dyadicWeightCut q)))^
          ((n+1:ℝ)*(B-1)/(((n+1:ℝ)-1)*B))) := by
  obtain ⟨Cband,hCband,hband⟩ := H
  obtain ⟨Ct,hCt,hassembly⟩ := dyadic_cylinder_wedge_integral_assembly n k hn hk B hB hBd hbeta
  let p := B/(B-1)
  have hp : 0<p := by dsimp [p]; positivity
  obtain ⟨K,hK,habsorb⟩ := dyadic_band_integral_loss_absorption (n+1) Ct Cband p (ε/2)
    hCt hCband hp (by positivity)
  let Cnorm := K^(1/p)
  have hCnorm : 0<Cnorm := by dsimp [Cnorm]; positivity
  have hpower : Cnorm^p=K := by
    dsimp [Cnorm]
    rw [←Real.rpow_mul hK.le,one_div_mul_cancel hp.ne',Real.rpow_one]
  refine ⟨Cnorm,hCnorm,?_⟩
  intro q hq N b u hu hsep
  let δ := dyadicWeightCut q
  let T := fun i => flatCylinder (b i) (u i) 1 δ
  let V := ∑ i, volume.real (T i)
  have hδ : 0<δ := by dsimp [δ,dyadicWeightCut]; positivity
  have hV : 0≤V := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  have hfull := hassembly q hq (ε/2) Cband (by positivity) hCband N b u hu hsep
    (hband q hq N b u hu hsep)
  have htarget := habsorb q (1-(n+1:ℝ)/B) (ε/2) ((n+1:ℝ)/n) V _ hV hfull
  rw [show ε/2+ε/2=ε by ring] at htarget
  have hdim : (1:ℝ)<n+1 := by exact_mod_cast Nat.succ_lt_succ hn
  apply (multilinear_norm_le_iff_integral_le u T B p _ hp (by positivity)
    (fun i => (isOpen_flatCylinder _ _ _ _ (hu i)).measurableSet)).mpr
  rw [published_bound_power hdim hB hCnorm.le hδ.le hV]
  change weightedTuplePowerIntegral k u T B p ≤ ENNReal.ofReal (Cnorm^p*δ^(p*(1-(n+1:ℝ)/B-ε))*V^((n+1:ℝ)/((n+1:ℝ)-1)))
  rw [hpower,add_sub_cancel_right]
  have hexp : p/(k:ℝ)=B/((k:ℝ)*(B-1)) := by dsimp [p]; rw [div_div,mul_comm (B-1)]
  unfold weightedTuplePowerIntegral
  rw [hexp]
  exact htarget

/-- Specialization to the published B supplies the exponent range instead
of assuming it. The explicitly named positive-band estimate remains open. -/
theorem dyadic_zahl_norm_of_positive_bands (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1)
    (ε : ℝ) (hε : 0<ε) (H : DyadicPositiveBandEstimate n k (zahlB (n+1) k) (ε/2)) :
    ∃ Cnorm : ℝ, 0<Cnorm ∧ ∀ q : ℕ, 1≤q →
      ∀ (N : ℕ) (b u : Fin N → EuclideanSpace ℝ (Fin (n+1))),
      (∀ i, ‖u i‖=1) →
      (∀ i j, i≠j → dyadicWeightCut q≤Real.arccos |inner ℝ (u i) (u j)|) →
      eLpNorm (multilinearKakeyaFunction k u
        (fun i => flatCylinder (b i) (u i) 1 (dyadicWeightCut q)) (zahlB (n+1) k))
        (ENNReal.ofReal (zahlB (n+1) k/(zahlB (n+1) k-1))) volume ≤
      ENNReal.ofReal (Cnorm*(dyadicWeightCut q)^(1-(n+1:ℝ)/zahlB (n+1) k-ε)*
        (∑ i, volume.real (flatCylinder (b i) (u i) 1 (dyadicWeightCut q)))^
          ((n+1:ℝ)*(zahlB (n+1) k-1)/(((n+1:ℝ)-1)*zahlB (n+1) k))) := by
  have hn : 0<n := by omega
  have hnR : (0:ℝ)<n+1 := by positivity
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hknR : (k:ℝ)≤n+1 := by exact_mod_cast hkn
  exact dyadic_norm_estimate_of_positive_bands n k hn (by omega) (zahlB (n+1) k)
    (zahlB_gt_one hnR hkR hknR) (zahlB_le_n hnR (by linarith) hknR)
    (by simpa only [Nat.cast_add,Nat.cast_one] using (zahl_integral_power_range hk hkn).2) ε hε H

end KakeyaTwoScale
#print axioms KakeyaTwoScale.dyadic_norm_estimate_of_positive_bands
#print axioms KakeyaTwoScale.dyadic_zahl_norm_of_positive_bands
