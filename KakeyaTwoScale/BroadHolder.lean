module
public import KakeyaTwoScale.BroadPointwise
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Actual finite-set Holder adapter. Integrability is derived from the
finite extended-real norm bound, not assumed. -/
theorem broad_integral_of_norm_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (hS : MeasurableSet S) (hfinite : μ S≠⊤)
    (f M : X → ℝ) (hf : Measurable f) (hM : Measurable M)
    (c B A : ℝ) (hc : 0<c) (hB : 1<B) (hA : 0≤A)
    (hfnonneg : ∀ x∈S, 0≤f x) (hMnonneg : ∀ x∈S, 0≤M x)
    (hpoint : ∀ x∈S, c*f x≤M x)
    (hnorm : eLpNorm M (ENNReal.ofReal (B/(B-1))) μ≤ENNReal.ofReal A) :
    Integrable f (μ.restrict S) ∧
      (∫ x in S, f x ∂μ) ≤ A*(μ.real S)^(1/B)/c := by
  let ν := μ.restrict S
  let g := fun x => c*f x
  have hgm : Measurable g := hf.const_mul c
  have hpR : 1<B/(B-1) := (zahl_holder_conjugacy hB).1
  have hp : (1:ℝ≥0∞)≤ENNReal.ofReal (B/(B-1)) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hpR.le
  have hexp : 1/(1:ℝ≥0∞).toReal-1/(ENNReal.ofReal (B/(B-1))).toReal=1/B := by
    rw [ENNReal.toReal_one,ENNReal.toReal_ofReal (by linarith : 0≤B/(B-1))]
    field_simp
    ring
  have hM1 : eLpNorm M 1 ν≤ENNReal.ofReal A*(μ S)^(1/B) := by
    have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (hM.aestronglyMeasurable (μ:=ν))
    rw [hexp] at hh
    have hnorm' := (eLpNorm_mono_measure (ν:=ν) M Measure.restrict_le_self).trans hnorm
    apply hh.trans
    simpa only [ν,Measure.restrict_apply_univ] using
      (mul_le_mul hnorm' (le_refl ((μ S)^(1/B))) zero_le zero_le)
  have hg1 : eLpNorm g 1 ν≤ENNReal.ofReal A*(μ S)^(1/B) := by
    apply le_trans _ hM1
    apply eLpNorm_mono_ae hgm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hS] with x hx
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (show 0≤g x from mul_nonneg hc.le (hfnonneg x hx)),
      abs_of_nonneg (hMnonneg x hx)]
    exact hpoint x hx
  have htop : ENNReal.ofReal A*(μ S)^(1/B)≠⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hfinite)
  have hgint : Integrable g ν := memLp_one_iff_integrable.mp
    (lt_of_le_of_lt hg1 (lt_top_iff_ne_top.mpr htop))
  have hfint : Integrable f ν := by
    have hh := hgint.div_const c
    simpa [g,hc.ne',mul_div_cancel_left₀] using hh
  refine ⟨hfint,?_⟩
  have hreal := ENNReal.toReal_mono htop hg1
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hA,← ENNReal.toReal_rpow] at hreal
  have hint : (eLpNorm g 1 ν).toReal=∫ x, g x ∂ν := by
    rw [eLpNorm_one_eq_lintegral_enorm hgm.aestronglyMeasurable,
      ← integral_norm_eq_lintegral_enorm hgm.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hS] with x hx
    exact Real.norm_of_nonneg (mul_nonneg hc.le (hfnonneg x hx))
  rw [hint] at hreal
  change (∫ x, c*f x ∂ν)≤A*(μ.real S)^(1/B) at hreal
  rw [integral_const_mul] at hreal
  apply (le_div_iff₀ hc).mpr
  nlinarith only [hreal]

theorem measurable_finite_family_card {X : Type*} [MeasurableSpace X] {N : ℕ}
    (G : X → Finset (Fin N)) (hG : ∀ j, MeasurableSet {x | j∈G x}) :
    Measurable (fun x => ((G x).card:ℝ)) := by
  have he : (fun x => ((G x).card:ℝ))=
      fun x => ∑ j : Fin N, ({x | j∈G x}).indicator (fun _ => (1:ℝ)) x := by
    funext x
    simp [Set.indicator]
  rw [he]
  exact Finset.measurable_sum _ (fun j _ => measurable_const.indicator (hG j))

/-- Source broad-set integral bound for an actual varying incident family.
The finite tuple generation, Gram bound, Holder inequality and integrability
are all proved; only the genuine global multilinear norm upper bound remains. -/
theorem broad_family_integral_of_norm_bound {n N k : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : MeasurableSet S) (hfinite : volume S≠⊤)
    (G : EuclideanSpace ℝ (Fin n) → Finset (Fin N))
    (hG : ∀ j, MeasurableSet {x | j∈G x})
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (hT : ∀ j, MeasurableSet (T j))
    (rho B A : ℝ) (hrho : 0<rho) (hB : 1<B) (hA : 0≤A)
    (hk : 1≤k) (hkn : k≤n) (hu : ∀ j, ‖u j‖=1)
    (hbroad : ∀ x∈S, ∀ H : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
      Module.finrank ℝ H=k-1 →
      (((G x).filter fun j => planeAngle H (u j)≤rho).card:ℝ)<((G x).card:ℝ)/2)
    (hincident : ∀ x∈S, ∀ j∈G x, x∈T j)
    (hnorm : eLpNorm (multilinearKakeyaFunction k u T B)
      (ENNReal.ofReal (B/(B-1))) volume≤ENNReal.ofReal A) :
    Integrable (fun x => ((G x).card:ℝ)) (volume.restrict S) ∧
      (∫ x in S, ((G x).card:ℝ)) ≤
        (broadCoefficient (k-1) B)⁻¹*rho^(-((k:ℝ)-1)/B)*(volume.real S)^(1/B)*A := by
  have hc0 := broadCoefficient_pos (k-1) B
  have hh := broad_integral_of_norm_bound volume S hS hfinite
    (fun x => ((G x).card:ℝ)) (multilinearKakeyaFunction k u T B)
    (measurable_finite_family_card G hG) (measurable_multilinearKakeyaFunction k u T B hT)
    (broadCoefficient (k-1) B*rho^(((k:ℝ)-1)/B)) B A (by positivity) hB hA
    (fun x _ => by positivity) (fun x _ => multilinearKakeyaFunction_nonneg k u T B x)
    (fun x hx => broad_multilinear_pointwise_k (G x) u T rho B hrho (by linarith) hk hkn
      (fun j _ => hu j) (hbroad x hx) x (hincident x hx)) hnorm
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  rw [show -((k:ℝ)-1)/B= -(((k:ℝ)-1)/B) by ring,Real.rpow_neg hrho.le]
  ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.broad_integral_of_norm_bound

#print axioms KakeyaTwoScale.measurable_finite_family_card
#print axioms KakeyaTwoScale.broad_family_integral_of_norm_bound
