module
public import KakeyaTwoScale.HighBandBrush
public import KakeyaTwoScale.ActualBrushBands

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Low and intermediate bands use the base plane itself. The extra power
of r needed for the common brush exponent is a monotonicity consequence,
not a shortening assertion at an inadmissible angular scale. -/
theorem low_band_brush_volume (n k : ℕ) (R B : ℝ) (hR : 0 ≤ R) (hB : 0 < B) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1)))),
      Module.finrank ℝ H=k+1 → ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ {J : Type*} (G : Finset J) (b u : J → EuclideanSpace ℝ (Fin (n+1))) (w : J → ℝ),
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖u j‖=1) → (∀ j ∈ G, 0 ≤ w j) →
      (∀ j ∈ G, planeAngle H (u j) ≤ (16*Real.pi)*r) →
      (∀ v : EuclideanSpace ℝ (Fin (n+1)), ‖v‖=1 →
        (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ r), w j) ≤ B) →
      c*r^n*(r^(k+1))^theta*(∑ j ∈ G, w j) ≤
        volume.real (⋃ j ∈ G, euclideanTube (b j) (u j) r) := by
  obtain ⟨c,hc,hvol⟩ := plane_weighted_capsule_volume n k R 1 B (16*Real.pi)
    hR (by norm_num) (by norm_num) hB (by positivity)
  refine ⟨c,hc,?_⟩
  intro H hdim r hr hrone J G b u w hb hu hw ha hcap
  have hv := hvol H hdim r hr hrone G b u w hb hu hw ha hcap
  simp only [one_smul] at hv
  have hp : r^(k+1) ≤ r^k := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hr.le k) hrone
  have hpow := Real.rpow_le_rpow (pow_nonneg hr.le _) hp (by norm_num [theta] : 0 ≤ theta)
  have hW : 0 ≤ ∑ j ∈ G, w j := Finset.sum_nonneg hw
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (show 0 ≤ c*r^n by positivity)) hW).trans hv

/-- Uniform actual volume estimate on every selected dyadic angle band.
High bands use constructed quarter pieces; low/intermediate bands use the
base plane. No scale-dependent constant or band-volume premise remains. -/
theorem dyadic_band_brush_volume (n k : ℕ) (R B C : ℝ)
    (hR : 0 ≤ R) (hB : 0 < B) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 1 ≤ q →
      ∀ (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))))
        (p : EuclideanSpace ℝ (Fin (n+1))),
      Module.finrank ℝ H=k+1 → ∀ band : ℕ,
      ∀ {J : Type*} (G : Finset J) (b u : J → EuclideanSpace ℝ (Fin (n+1))) (w : J → ℝ),
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖u j‖=1) → (∀ j ∈ G, 0 ≤ w j) →
      (∀ j ∈ G, dyadicAngleBand q (planeAngle H (u j))=band) →
      (∀ j ∈ G, (euclideanTube (b j) (u j) (dyadicRadius q) ∩
        Metric.thickening (C*dyadicRadius q) (affinePlane H p)).Nonempty) →
      (∀ v : EuclideanSpace ℝ (Fin (n+1)), ‖v‖=1 →
        (∑ j ∈ G.filter (fun j => Real.arccos |inner ℝ (u j) v| ≤ dyadicRadius q), w j) ≤ B) →
      c*(dyadicRadius q)^n*((dyadicRadius q)^(k+1))^theta*(∑ j ∈ G, w j) ≤
        volume.real (⋃ j ∈ G, euclideanTube (b j) (u j) (dyadicRadius q)) := by
  obtain ⟨cl,hcl,hlow⟩ := low_band_brush_volume n k R B hR hB
  obtain ⟨ch,hch,hhigh⟩ := high_band_brush_volume n k R B C hR hB hC
  refine ⟨min cl ch,lt_min hcl hch,?_⟩
  intro q hq H p hdim band J G b u w hb hu hw hband hmeet hcap
  let r := dyadicRadius q
  have hr : 0 < r := Real.exp_pos _
  have hrone : r ≤ 1 := (dyadicRadius_le_half hq).trans (by norm_num)
  have hW : 0 ≤ ∑ j ∈ G, w j := Finset.sum_nonneg hw
  have hmono (c : ℝ) (hc : min cl ch ≤ c) :
      min cl ch*r^n*(r^(k+1))^theta*(∑ j ∈ G, w j) ≤
      c*r^n*(r^(k+1))^theta*(∑ j ∈ G, w j) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (pow_nonneg hr.le n))
        (Real.rpow_nonneg (pow_nonneg hr.le _) _)) hW
  have hspec : ∀ j ∈ G, planeAngle H (u j) ≤ (2:ℝ)^band*r ∧
      (0 < band → (2:ℝ)^(band-1)*r < planeAngle H (u j)) := by
    intro j hj
    have hs := (dyadicAngleBand_spec q (planeAngle H (u j))
      ((planeAngle_range H (u j)).2.trans (by linarith [Real.pi_lt_four]))).2
    rwa [hband j hj] at hs
  by_cases hz : band=0
  · apply (hmono cl (min_le_left _ _)).trans
    apply hlow H hdim r hr hrone G b u w hb hu hw _ hcap
    intro j hj
    have hh := (hspec j hj).1
    rw [hz,pow_zero,one_mul] at hh
    have hp : 1 ≤ 16*Real.pi := by linarith [Real.pi_gt_three]
    exact hh.trans (by nlinarith only [hp,hr])
  · let s := (2:ℝ)^(band-1)*r
    have hs : 0 < s := by dsimp [s]; positivity
    have htwo : (2:ℝ)^band*r=2*s := by
      have hn : band=(band-1)+1 := by omega
      calc
        _ = (2:ℝ)^((band-1)+1)*r := by congr 2
        _ = 2*s := by rw [pow_succ]; dsimp [s]; ring
    have ha : ∀ j ∈ G, s ≤ planeAngle H (u j) ∧ planeAngle H (u j) ≤ 2*s := by
      intro j hj
      exact ⟨((hspec j hj).2 (by omega)).le, (hspec j hj).1.trans_eq htwo⟩
    by_cases hscale : r ≤ s/(8*Real.pi)
    · exact (hmono ch (min_le_right _ _)).trans
        (hhigh H p hdim r s hr hrone hs hscale G b u w hb hu hw ha hmeet hcap)
    · apply (hmono cl (min_le_left _ _)).trans
      apply hlow H hdim r hr hrone G b u w hb hu hw _ hcap
      intro j hj
      have hsmall := (div_lt_iff₀ (show 0 < 8*Real.pi by positivity)).mp (lt_of_not_ge hscale)
      exact (ha j hj).2.trans (by nlinarith only [hsmall])

end KakeyaTwoScale
#print axioms KakeyaTwoScale.low_band_brush_volume
#print axioms KakeyaTwoScale.dyadic_band_brush_volume
