module
public import KakeyaTwoScale.MultilinearScale
public import KakeyaTwoScale.TubeCapture

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Exact basepoint translation invariance of capsule volume. -/
theorem euclideanTube_volume_translate {d : ℕ}
    (b u : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    volume (euclideanTube b u r)=volume (euclideanTube 0 u r) := by
  have he : (fun x => b+x) ⁻¹' euclideanTube b u r=euclideanTube 0 u r := by
    ext x
    simp only [Set.mem_preimage,euclideanTube,Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t,ht,hx⟩
      exact ⟨t,ht,by simpa only [zero_add,dist_add_left] using hx⟩
    · rintro ⟨t,ht,hx⟩
      exact ⟨t,ht,by simpa only [zero_add,dist_add_left] using hx⟩
  rw [← he,measure_preimage_add]

 theorem euclideanTube_volume_lower_unrestricted (n : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∀ r : ℝ, 0<r →
      ∀ b u : EuclideanSpace ℝ (Fin (n+1)), ‖u‖=1 →
      c*r^n≤volume.real (euclideanTube b u r) := by
  obtain ⟨c,hc,hvol⟩ := euclideanTube_volume_lower n 0 (by norm_num)
  refine ⟨c,hc,?_⟩
  intro r hr b u hu
  have hh := hvol r hr 0 u (by simp) hu
  simpa only [Measure.real,euclideanTube_volume_translate b u r] using hh

/-- Flat cylinders lie in capsules with the same axis and any larger radius. -/
theorem flatCylinder_subset_unit_capsule {d : ℕ}
    (b u : EuclideanSpace ℝ (Fin d)) (r δ : ℝ) (hr : r≤δ) :
    flatCylinder b u 1 r ⊆ euclideanTube b u δ := by
  rintro x ⟨t,ht0,ht1,_hi,hres⟩
  exact ⟨t,⟨ht0.le,ht1.le⟩,(by simpa [dist_eq_norm] using hres.trans_le hr)⟩

theorem flatCylinder_unit_finite {d : ℕ}
    (b u : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    volume (flatCylinder b u 1 r) ≠ ⊤ :=
  measure_ne_top_of_subset (flatCylinder_subset_unit_capsule b u r r le_rfl)
    (euclideanTube_finite b u r)

/-- Uniform per-tube mass comparison after the actual fixed normalization.
No bound on either original or normalized basepoint is required. -/
theorem normalized_cylinder_mass_le (n : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀ C δ : ℝ, 0≤C → 0<δ → δ≤1/2 →
      ∀ b u : EuclideanSpace ℝ (Fin (n+1)), ‖u‖=1 →
      volume.real (flatCylinder ((2*C+3)⁻¹ • (b-(C*δ) • u)) u 1 (C*δ/(2*C+3))) ≤
        K*volume.real (euclideanTube b u δ) := by
  obtain ⟨c,hc,hvol⟩ := euclideanTube_volume_lower_unrestricted n
  let A : ℝ := 3*(2*(n+3:ℝ))^n
  refine ⟨A/c,by dsimp [A]; positivity,?_⟩
  intro C δ hC hδ hδhalf b u hu
  let b' := (2*C+3)⁻¹ • (b-(C*δ) • u)
  have hs := flatCylinder_subset_unit_capsule b' u (C*δ/(2*C+3)) δ
    (rescaled_cylinder_width_le hC hδ.le)
  have hv := (measureReal_mono hs (euclideanTube_finite b' u δ)).trans
    (euclideanTube_volume_upper b' u hδ hδhalf hu)
  have hlo := hvol δ hδ b u hu
  have hh := mul_le_mul_of_nonneg_left hlo (show 0≤A/c by dsimp [A]; positivity)
  have he : A/c*(c*δ^n)=A*δ^n := by field_simp
  rw [he] at hh
  exact hv.trans hh

/-- Summation preserves the same dimension-only constant. -/
theorem normalized_cylinder_mass_sum_le (n : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀ C δ : ℝ, 0≤C → 0<δ → δ≤1/2 →
      ∀ {J : Type*} (G : Finset J) (b u : J → EuclideanSpace ℝ (Fin (n+1))),
      (∀ j∈G, ‖u j‖=1) →
      (∑ j∈G, volume.real (flatCylinder ((2*C+3)⁻¹ • (b j-(C*δ) • u j))
        (u j) 1 (C*δ/(2*C+3)))) ≤ K*(∑ j∈G,volume.real (euclideanTube (b j) (u j) δ)) := by
  obtain ⟨K,hK,hbound⟩ := normalized_cylinder_mass_le n
  refine ⟨K,hK,?_⟩
  intro C δ hC hδ hδhalf J G b u hu
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j hj => hbound C δ hC hδ hδhalf (b j) (u j) (hu j hj))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.euclideanTube_volume_translate
#print axioms KakeyaTwoScale.euclideanTube_volume_lower_unrestricted
#print axioms KakeyaTwoScale.flatCylinder_subset_unit_capsule
#print axioms KakeyaTwoScale.normalized_cylinder_mass_le
#print axioms KakeyaTwoScale.normalized_cylinder_mass_sum_le

#print axioms KakeyaTwoScale.flatCylinder_unit_finite
