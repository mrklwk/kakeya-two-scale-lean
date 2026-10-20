module
public import KakeyaTwoScale.PublishedZahlAdapter

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Literal determinant-weighted ordered tuple sum at its target integral power.
No norm is converted through `toReal`; infinite integrals remain infinite. -/
def weightedTuplePowerIntegral {n N : ℕ} (k : ℕ)
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B p : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((∑ f : Fin k → Fin N,
    (tupleWedgeVolume (fun i => u (f i)))^((k:ℝ)/B) *
      ∏ i : Fin k, (T (f i)).indicator (fun _ => (1:ℝ)) x)^(p/(k:ℝ)))

/-- Exact pth-power norm identity for the original ordered tuple function. -/
theorem multilinear_norm_power_eq_integral {n N k : ℕ}
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B p : ℝ)
    (hp : 0<p) (hT : ∀ j, MeasurableSet (T j)) :
    eLpNorm (multilinearKakeyaFunction k u T B) (ENNReal.ofReal p) volume ^ p =
      weightedTuplePowerIntegral k u T B p := by
  have hm := (measurable_multilinearKakeyaFunction k u T B hT).aestronglyMeasurable (μ:=volume)
  rw [eLpNorm_eq_eLpNorm' (by positivity) ENNReal.ofReal_ne_top hm,
    ENNReal.toReal_ofReal hp.le, ←lintegral_rpow_enorm_eq_rpow_eLpNorm' hp]
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal (multilinearKakeyaFunction_nonneg k u T B x)]
  rw [ENNReal.ofReal_rpow_of_nonneg (multilinearKakeyaFunction_nonneg k u T B x) hp.le]
  unfold multilinearKakeyaFunction
  rw [←Real.rpow_mul (by
    apply Finset.sum_nonneg
    intro f _
    exact mul_nonneg (Real.rpow_nonneg (tupleWedgeVolume_nonneg _) _)
      (Finset.prod_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => by norm_num) x)))]
  congr 2
  ring

/-- Exact equivalence between a finite real norm bound and its integral bound,
including zero right-hand side and arbitrarily large (even infinite) integrals. -/
theorem multilinear_norm_le_iff_integral_le {n N k : ℕ}
    (u : Fin N → EuclideanSpace ℝ (Fin n))
    (T : Fin N → Set (EuclideanSpace ℝ (Fin n))) (B p R : ℝ)
    (hp : 0<p) (hR : 0≤R) (hT : ∀ j, MeasurableSet (T j)) :
    eLpNorm (multilinearKakeyaFunction k u T B) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal R ↔
      weightedTuplePowerIntegral k u T B p ≤ ENNReal.ofReal (R^p) := by
  rw [←multilinear_norm_power_eq_integral u T B p hp hT,
    ←ENNReal.ofReal_rpow_of_nonneg hR hp.le]
  exact (ENNReal.rpow_le_rpow_iff hp).symm

/-- Raising the precise published right side to its conjugate power gives
volume exponent n/(n-1), with the epsilon loss multiplied by that power. -/
theorem published_bound_power {n B C r V ε : ℝ}
    (hn : 1<n) (hB : 1<B) (hC : 0≤C) (hr : 0≤r) (hV : 0≤V) :
    (C*r^(1-n/B-ε)*V^(n*(B-1)/((n-1)*B)))^(B/(B-1)) =
      C^(B/(B-1))*r^((B/(B-1))*(1-n/B-ε))*V^(n/(n-1)) := by
  rw [Real.mul_rpow (mul_nonneg hC (Real.rpow_nonneg hr _))
    (Real.rpow_nonneg hV _), Real.mul_rpow hC (Real.rpow_nonneg hr _),
    ←Real.rpow_mul hr, ←Real.rpow_mul hV]
  have hv : (n*(B-1)/((n-1)*B))*(B/(B-1))=n/(n-1) := by
    have hb0 : B≠0 := by linarith
    have hbm : B-1≠0 := by linarith
    field_simp
  rw [hv, mul_comm (1-n/B-ε) (B/(B-1))]

/-- The exact integral form of the published estimate. Its determinant power,
original ordered tuples, cylinders, separation, and constant order are unchanged.
This definition is an obligation, not an asserted analytic theorem. -/
def PublishedZahlIntegralEstimate (n k : ℕ) : Prop :=
  2 ≤ k ∧ k ≤ n ∧ ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧ ∀ r : ℝ, 0<r → r<1/2 →
    ∀ (N : ℕ) (b u : Fin N → EuclideanSpace ℝ (Fin n)),
    (∀ j, ‖u j‖=1) →
    (∀ i j, i≠j → r≤Real.arccos |inner ℝ (u i) (u j)|) →
    weightedTuplePowerIntegral k u (fun j => flatCylinder (b j) (u j) 1 r)
      (zahlB n k) (zahlB n k/(zahlB n k-1)) ≤
      ENNReal.ofReal (C*r^((zahlB n k/(zahlB n k-1))*(1-(n:ℝ)/zahlB n k-ε))*
        (∑ j, volume.real (flatCylinder (b j) (u j) 1 r))^((n:ℝ)/((n:ℝ)-1)))

/-- The published tuple-integral power lies in the concave range required
by the literal finite-band recombination. -/
theorem zahl_integral_power_range {n k : ℕ} (hk : 2≤k) (hkn : k≤n) :
    0<zahlB n k/((k:ℝ)*(zahlB n k-1)) ∧
    zahlB n k/((k:ℝ)*(zahlB n k-1))≤1 := by
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hknR : (k:ℝ)≤n := by exact_mod_cast hkn
  have hn : (0:ℝ)<n := by linarith
  have hB := zahlB_gt_one hn hkR hknR
  have hBk := zahlB_ge_k hn hknR
  constructor
  · positivity
  · apply (div_le_one (by positivity)).mpr
    nlinarith

/-- The scalar optimizer's radius exponent is exactly the norm's pth-power
exponent; an epsilon norm loss costs p*epsilon in the integral. -/
theorem published_integral_radius_exponent {B : ℝ} (hB : 1<B) (n ε : ℝ) :
    (B/(B-1))*(1-n/B-ε)=(B-n)/(B-1)-(B/(B-1))*ε := by
  have hB0 : B≠0 := by linarith
  have hB1 : B-1≠0 := by linarith
  field_simp

/-- Exact equivalence of the full quantified integral and norm obligations.
Constants transform by a fixed positive power before radius/family choices. -/
theorem published_zahl_iff_integral (n k : ℕ) :
    PublishedZahlCylinderEstimate n k ↔ PublishedZahlIntegralEstimate n k := by
  constructor
  · rintro ⟨hklo,hkhi,hZ⟩
    have hn : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hB : 1<zahlB n k := zahlB_gt_one (by linarith)
      (by exact_mod_cast hklo) (by exact_mod_cast hkhi)
    have hp : 0<zahlB n k/(zahlB n k-1) := by positivity
    refine ⟨hklo,hkhi,?_⟩
    intro ε hε
    obtain ⟨C,hC,hbound⟩ := hZ ε hε
    refine ⟨C^(zahlB n k/(zahlB n k-1)),by positivity,?_⟩
    intro r hr hrhalf N b u hu hsep
    have hV : 0≤∑ j,volume.real (flatCylinder (b j) (u j) 1 r) :=
      Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
    have hh := (multilinear_norm_le_iff_integral_le u
      (fun j => flatCylinder (b j) (u j) 1 r) (zahlB n k) _
      (C*r^(1-(n:ℝ)/zahlB n k-ε)*
        (∑ j,volume.real (flatCylinder (b j) (u j) 1 r))^
          ((n:ℝ)*(zahlB n k-1)/(((n:ℝ)-1)*zahlB n k)))
      hp (by positivity) (fun j => (isOpen_flatCylinder _ _ _ _ (hu j)).measurableSet)).mp
      (hbound r hr hrhalf N b u hu hsep)
    rwa [published_bound_power hn hB hC.le hr.le hV] at hh
  · rintro ⟨hklo,hkhi,hZ⟩
    have hn : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hB : 1<zahlB n k := zahlB_gt_one (by linarith)
      (by exact_mod_cast hklo) (by exact_mod_cast hkhi)
    have hp : 0<zahlB n k/(zahlB n k-1) := by positivity
    refine ⟨hklo,hkhi,?_⟩
    intro ε hε
    obtain ⟨C,hC,hbound⟩ := hZ ε hε
    let D := C^(1/(zahlB n k/(zahlB n k-1)))
    have hD : 0<D := by dsimp [D]; positivity
    have hDp : D^(zahlB n k/(zahlB n k-1))=C := by
      dsimp [D]
      rw [←Real.rpow_mul hC.le, one_div_mul_cancel hp.ne', Real.rpow_one]
    refine ⟨D,hD,?_⟩
    intro r hr hrhalf N b u hu hsep
    have hV : 0≤∑ j,volume.real (flatCylinder (b j) (u j) 1 r) :=
      Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
    apply (multilinear_norm_le_iff_integral_le u
      (fun j => flatCylinder (b j) (u j) 1 r) (zahlB n k) _ _ hp
      (by positivity) (fun j => (isOpen_flatCylinder _ _ _ _ (hu j)).measurableSet)).mpr
    rw [published_bound_power hn hB hD.le hr.le hV,hDp]
    exact hbound r hr hrhalf N b u hu hsep

end KakeyaTwoScale
#print axioms KakeyaTwoScale.multilinear_norm_power_eq_integral
#print axioms KakeyaTwoScale.multilinear_norm_le_iff_integral_le

#print axioms KakeyaTwoScale.published_bound_power
#print axioms KakeyaTwoScale.published_zahl_iff_integral

#print axioms KakeyaTwoScale.zahl_integral_power_range
#print axioms KakeyaTwoScale.published_integral_radius_exponent
