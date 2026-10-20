module
public import KakeyaTwoScale.MultilinearKakeya
public import KakeyaTwoScale.PublishedZahlIntegral

@[expose] public section

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Open finite cylinders are contained in the actual closed infinite-line tube.
No longitudinal bound or unit-direction hypothesis is needed for this inclusion. -/
theorem flatCylinder_subset_infiniteLineTube {d : ℕ}
    (b u : EuclideanSpace ℝ (Fin d)) (L r : ℝ) :
    flatCylinder b u L r ⊆ WithLp.ofLp ⁻¹'
      infiniteLineTube (WithLp.ofLp b) (WithLp.ofLp u) r := by
  rintro x ⟨t,_,_,_,ht⟩
  refine ⟨t,?_⟩
  have he : WithLp.toLp 2 (WithLp.ofLp x-(WithLp.ofLp b+t • WithLp.ofLp u))=x-(b+t • u) := by
    ext i
    rfl
  simpa only [he] using ht.le

/-- Actual flat-cylinder ordered tuples, in the exact existing integral API.
The constant precedes radius, lengths, locations and the whole finite family.
This is the CV exponent B=k, not the stronger Zahl exponent. -/
theorem flatCylinder_multilinear_integral (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1) :
    ∃ C : ℝ, 0<C ∧ ∀ r : ℝ, 0<r → ∀ (N : ℕ)
      (b u : Fin N → EuclideanSpace ℝ (Fin (n+1))) (ell : Fin N → ℝ),
      (∀ j, ‖u j‖=1) →
      weightedTuplePowerIntegral k u (fun j => flatCylinder (b j) (u j) (ell j) r)
        k ((k:ℝ)/(k-1)) ≤
      ENNReal.ofReal (C*r^(n+1)*((N:ℝ)^k)^(1/((k-1:ℕ):ℝ))) := by
  obtain ⟨C,hC,hmain⟩ := weighted_multilinear_kakeya n k hk hkn
  refine ⟨C,hC,?_⟩
  intro r hr N b u ell hu
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hexp : (k:ℝ)/(k-1)/(k:ℝ)=1/((k-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1≤k),Nat.cast_one]
    field_simp
  let T := fun j => flatCylinder (b j) (u j) (ell j) r
  let F := fun x => ENNReal.ofReal ((∑f : Fin k → Fin N,
    tupleWedgeVolume (fun j => u (f j))*∏j, (T (f j)).indicator (fun _ => (1:ℝ)) x)^
      (1/((k-1:ℕ):ℝ)))
  have hF : Measurable F := by
    apply Measurable.ennreal_ofReal
    apply Measurable.pow_const
    apply Finset.measurable_sum
    intro f _
    apply Measurable.const_mul
    apply Finset.measurable_prod
    intro j _
    exact measurable_const.indicator (isOpen_flatCylinder _ _ _ _ (hu (f j))).measurableSet
  have he : weightedTuplePowerIntegral k u T k ((k:ℝ)/(k-1))=∫⁻x, F x := by
    simp only [weightedTuplePowerIntegral,div_self hkR.ne',Real.rpow_one,hexp,F]
  rw [he,←(PiLp.volume_preserving_toLp (Fin (n+1))).lintegral_comp hF]
  have hbound := hmain r hr (fun _ => N) (fun _ j => WithLp.ofLp (b j))
    (fun _ j => u j) (fun _ _ => 1) (fun _ j => hu j) (by intros; norm_num)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
    Finset.prod_const] at hbound
  apply le_trans (lintegral_mono (fun x => ?_)) hbound
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow
  · exact Finset.sum_nonneg (fun f _ => mul_nonneg (tupleWedgeVolume_nonneg _)
      (Finset.prod_nonneg (fun j _ => Set.indicator_nonneg (by intros; norm_num) _)))
  · apply Finset.sum_le_sum
    intro f _
    apply mul_le_mul_of_nonneg_left _ (tupleWedgeVolume_nonneg _)
    apply Finset.prod_le_prod₀
    · intro j _
      exact Set.indicator_nonneg (by intros; norm_num) _
    · intro j _
      by_cases hx : WithLp.toLp 2 x ∈ T (f j)
      · have hh := flatCylinder_subset_infiniteLineTube (b (f j)) (u (f j)) (ell (f j)) r hx
        have hh' : x∈infiniteLineTube (WithLp.ofLp (b (f j))) (WithLp.ofLp (u (f j))) r := hh
        simp only [Set.indicator_of_mem hx,Set.indicator_of_mem hh',le_refl]
      · rw [Set.indicator_of_notMem hx]
        exact Set.indicator_nonneg (by intros; norm_num) _
  · positivity

/-- The genuine extended-real Lp norm, raised to its positive exponent.
No conversion through `toReal` can hide an infinite norm. -/
theorem flatCylinder_multilinear_norm_power (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1) :
    ∃ C : ℝ, 0<C ∧ ∀ r : ℝ, 0<r → ∀ (N : ℕ)
      (b u : Fin N → EuclideanSpace ℝ (Fin (n+1))) (ell : Fin N → ℝ),
      (∀ j, ‖u j‖=1) →
      eLpNorm (multilinearKakeyaFunction k u
        (fun j => flatCylinder (b j) (u j) (ell j) r) k)
        (ENNReal.ofReal ((k:ℝ)/(k-1))) volume ^ ((k:ℝ)/(k-1)) ≤
      ENNReal.ofReal (C*r^(n+1)*((N:ℝ)^k)^(1/((k-1:ℕ):ℝ))) := by
  obtain ⟨C,hC,hbound⟩ := flatCylinder_multilinear_integral n k hk hkn
  refine ⟨C,hC,?_⟩
  intro r hr N b u ell hu
  have hkR : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  rw [multilinear_norm_power_eq_integral u _ k _ (by positivity)
    (fun j => (isOpen_flatCylinder _ _ _ _ (hu j)).measurableSet)]
  exact hbound r hr N b u ell hu

end KakeyaTwoScale
#print axioms KakeyaTwoScale.flatCylinder_multilinear_integral

#print axioms KakeyaTwoScale.flatCylinder_multilinear_norm_power
