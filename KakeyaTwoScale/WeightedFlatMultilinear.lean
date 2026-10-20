module
public import KakeyaTwoScale.FlatCylinderMultilinear

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Independent labeled families of finite cylinders, with genuine nonnegative
real weights; different slots need not have the same cardinality. -/
def weightedFlatCylinderFunction {n k : ℕ} (L : Fin k → ℕ)
    (b u : (j : Fin k) → Fin (L j) → EuclideanSpace ℝ (Fin (n+1)))
    (ell a : (j : Fin k) → Fin (L j) → ℝ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin (n+1))) : ℝ :=
  ∑f : (j : Fin k) → Fin (L j), tupleWedgeVolume (fun j => u j (f j))*
    ∏j, (flatCylinder (b j (f j)) (u j (f j)) (ell j (f j)) r).indicator
      (fun _ => a j (f j)) x

/-- CV for the physical finite cylinders used in individual grains. Radius and
all physical data are quantified after the constant. -/
theorem weighted_flat_multilinear (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1) :
    ∃ C : ℝ, 0<C ∧ ∀ r : ℝ, 0<r → ∀ (L : Fin k → ℕ)
      (b u : (j : Fin k) → Fin (L j) → EuclideanSpace ℝ (Fin (n+1)))
      (ell a : (j : Fin k) → Fin (L j) → ℝ),
      (∀j t, ‖u j t‖=1) → (∀j t, 0≤a j t) →
      (∫⁻x, ENNReal.ofReal ((weightedFlatCylinderFunction L b u ell a r x)^
        (1/((k-1:ℕ):ℝ)))) ≤
      ENNReal.ofReal (C*r^(n+1)*(∏j, ∑t, a j t)^(1/((k-1:ℕ):ℝ))) := by
  obtain ⟨C,hC,hmain⟩ := weighted_multilinear_kakeya n k hk hkn
  refine ⟨C,hC,?_⟩
  intro r hr L b u ell a hu ha
  have hm : Measurable (fun x => ENNReal.ofReal
      ((weightedFlatCylinderFunction L b u ell a r x)^(1/((k-1:ℕ):ℝ)))) := by
    apply Measurable.ennreal_ofReal
    apply Measurable.pow_const
    apply Finset.measurable_sum
    intro f _
    apply Measurable.const_mul
    apply Finset.measurable_prod
    intro j _
    exact measurable_const.indicator (isOpen_flatCylinder _ _ _ _ (hu j (f j))).measurableSet
  rw [←(PiLp.volume_preserving_toLp (Fin (n+1))).lintegral_comp hm]
  apply le_trans (lintegral_mono (fun x => ?_))
    (hmain r hr L (fun j t => WithLp.ofLp (b j t)) u a hu ha)
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow
  · exact Finset.sum_nonneg (fun f _ => mul_nonneg (tupleWedgeVolume_nonneg _)
      (Finset.prod_nonneg (fun j _ => Set.indicator_nonneg (fun _ _ => ha j (f j)) _)))
  · apply Finset.sum_le_sum
    intro f _
    apply mul_le_mul_of_nonneg_left _ (tupleWedgeVolume_nonneg _)
    apply Finset.prod_le_prod₀
    · intro j _
      exact Set.indicator_nonneg (fun _ _ => ha j (f j)) _
    · intro j _
      by_cases hx : WithLp.toLp 2 x∈flatCylinder (b j (f j)) (u j (f j)) (ell j (f j)) r
      · have hh : x∈infiniteLineTube (WithLp.ofLp (b j (f j))) (WithLp.ofLp (u j (f j))) r :=
          flatCylinder_subset_infiniteLineTube _ _ _ _ hx
        simp only [Set.indicator_of_mem hx,Set.indicator_of_mem hh,le_refl]
      · rw [Set.indicator_of_notMem hx]
        exact Set.indicator_nonneg (fun _ _ => ha j (f j)) _
  · positivity

/-- Finite grainwise assembly, retaining each grain's actual independent
weighted families. Restricting each integral to any owned domain only improves
this bound, so no tuple saturation or marginal lower-count hypothesis occurs. -/
theorem finite_grain_multilinear (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1) :
    ∃ C : ℝ, 0<C ∧ ∀ r : ℝ, 0<r → ∀ (G : ℕ) (L : Fin G → Fin k → ℕ)
      (b u : (g : Fin G) → (j : Fin k) → Fin (L g j) → EuclideanSpace ℝ (Fin (n+1)))
      (ell a : (g : Fin G) → (j : Fin k) → Fin (L g j) → ℝ)
      (E : Fin G → Set (EuclideanSpace ℝ (Fin (n+1)))),
      (∀g j t, ‖u g j t‖=1) → (∀g j t, 0≤a g j t) →
      (∑g, ∫⁻x in E g, ENNReal.ofReal ((weightedFlatCylinderFunction (L g) (b g) (u g)
        (ell g) (a g) r x)^(1/((k-1:ℕ):ℝ)))) ≤
      ∑g, ENNReal.ofReal (C*r^(n+1)*(∏j, ∑t, a g j t)^(1/((k-1:ℕ):ℝ))) := by
  obtain ⟨C,hC,hmain⟩ := weighted_flat_multilinear n k hk hkn
  refine ⟨C,hC,?_⟩
  intro r hr G L b u ell a E hu ha
  apply Finset.sum_le_sum
  intro g _
  exact (setLIntegral_le_lintegral _ _).trans
    (hmain r hr (L g) (b g) (u g) (ell g) (a g) (hu g) (ha g))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.weighted_flat_multilinear
#print axioms KakeyaTwoScale.finite_grain_multilinear
