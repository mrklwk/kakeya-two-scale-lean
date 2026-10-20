module
public import KakeyaTwoScale.MultilinearIntegral

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

def weightedTubeFunctionRadius {n k : ℕ} (L : Fin k → ℕ)
    (b : (j : Fin k) → Fin (L j) → Fin (n+1) → ℝ)
    (u : (j : Fin k) → Fin (L j) → EuclideanSpace ℝ (Fin (n+1)))
    (a : (j : Fin k) → Fin (L j) → ℝ) (r : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  ∑f : (j : Fin k) → Fin (L j), tupleWedgeVolume (fun j => u j (f j))*
    ∏j, (infiniteLineTube (b j (f j)) (WithLp.ofLp (u j (f j))) r).indicator (fun _ => a j (f j)) x

theorem infiniteLineTube_inverse_dilation {N : ℕ} (b u x : Fin N → ℝ)
    (r : ℝ) (hr : 0<r) :
    x∈infiniteLineTube b u r ↔ r⁻¹ • x∈infiniteLineTube (r⁻¹ • b) u 1 := by
  rw [infiniteLineTube_iff_projection b x (WithLp.toLp 2 u),
    infiniteLineTube_iff_projection (r⁻¹ • b) (r⁻¹ • x) (WithLp.toLp 2 u)]
  have he : (WithLp.toLp 2 (r⁻¹ • x-r⁻¹ • b) : EuclideanSpace ℝ (Fin N))=
      r⁻¹ • WithLp.toLp 2 (x-b) := by ext i; simp [mul_sub]
  rw [he,map_smul,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]
  constructor
  · intro h
    apply (inv_mul_le_iff₀ hr).mpr
    simpa only [mul_one] using h
  · intro h
    simpa only [mul_one] using (inv_mul_le_iff₀ hr).mp h

theorem weightedTubeFunctionRadius_normalize {n k : ℕ} (L : Fin k → ℕ) (b u a)
    (r : ℝ) (hr : 0<r) (x : Fin (n+1) → ℝ) :
    weightedTubeFunctionRadius L b u a r x=
      weightedTubeFunction L (fun j t => r⁻¹ • b j t) u a (r⁻¹ • x) := by
  unfold weightedTubeFunctionRadius weightedTubeFunction
  apply Finset.sum_congr rfl
  intro f _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp only [Set.indicator,infiniteLineTube_inverse_dilation _ _ _ r hr]

/-- Exact positive dilation for coordinate Lebesgue measure. -/
theorem coordinate_lintegral_inverse_dilation {N : ℕ}
    (f : (Fin N → ℝ) → ℝ≥0∞) (hf : Measurable f) (r : ℝ) (hr : 0<r) :
    (∫⁻x, f (r⁻¹ • x))=ENNReal.ofReal (r^N)*(∫⁻x, f x) := by
  have hd : Measurable (fun x : Fin N → ℝ => r⁻¹ • x) := by fun_prop
  have hmap : Measure.map (fun x : Fin N → ℝ => r⁻¹ • x) volume=
      ENNReal.ofReal (r^N) • volume := by
    rw [Measure.map_addHaar_smul volume (inv_ne_zero hr.ne')]
    simp [inv_pow,abs_of_pos (pow_pos hr N)]
  rw [← lintegral_map hf hd,hmap,lintegral_smul_measure]
  rfl

/-- Dependency-closed weighted multilinear Kakeya integral estimate, for every
positive radius. Ambient dimension is n+1 and 2≤k≤n+1. The scale power is
exactly r^(n+1), the tuple wedge has power one, and the integrand exponent is
1/(k-1). This is the general multilinear input, not Zahl's stronger estimate. -/
theorem weighted_multilinear_kakeya (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1) :
    ∃C : ℝ, 0<C ∧ ∀(r : ℝ), 0<r → ∀(L : Fin k → ℕ)
      (b : (j : Fin k) → Fin (L j) → Fin (n+1) → ℝ)
      (u : (j : Fin k) → Fin (L j) → EuclideanSpace ℝ (Fin (n+1)))
      (a : (j : Fin k) → Fin (L j) → ℝ), (∀j t, ‖u j t‖=1) → (∀j t, 0≤a j t) →
      (∫⁻x, ENNReal.ofReal ((weightedTubeFunctionRadius L b u a r x)^(1/((k-1:ℕ):ℝ))))≤
        ENNReal.ofReal (C*r^(n+1)*(∏j, ∑t, a j t)^(1/((k-1:ℕ):ℝ))) := by
  obtain ⟨C,hC,hunit⟩ := weighted_multilinear_kakeya_unit n k hk hkn
  refine ⟨C,hC,?_⟩
  intro r hr L b u a hu ha
  let b' := fun j t => r⁻¹ • b j t
  have hm : Measurable (fun x => ENNReal.ofReal ((weightedTubeFunction L b' u a x)^(1/((k-1:ℕ):ℝ)))) :=
    ((weightedTubeFunction_measurable L b' u a).pow_const _).ennreal_ofReal
  simp_rw [weightedTubeFunctionRadius_normalize L b u a r hr]
  rw [coordinate_lintegral_inverse_dilation _ hm r hr]
  have hh := mul_le_mul_of_nonneg_left (hunit L b' u a hu ha)
    (show 0≤ENNReal.ofReal (r^(n+1)) from zero_le)
  apply hh.trans_eq
  rw [← ENNReal.ofReal_mul (pow_nonneg hr.le _)]
  congr 1
  ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.infiniteLineTube_inverse_dilation
#print axioms KakeyaTwoScale.weightedTubeFunctionRadius_normalize
#print axioms KakeyaTwoScale.coordinate_lintegral_inverse_dilation
#print axioms KakeyaTwoScale.weighted_multilinear_kakeya
