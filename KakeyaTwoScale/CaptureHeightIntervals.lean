module
public import KakeyaTwoScale.LocalizedCylinderDirectionBall
public import KakeyaTwoScale.TubeChartSelection

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- Positive-height coordinates send the middle half to this exact interval. -/
theorem middleHalfHeights_eq {n : ℕ} (h : Fin (n+1))
    (b u center : EuclideanSpace ℝ (Fin (n+1))) (L : ℝ) (hu : 0 < u h) :
    middleHalfHeights h b u center L =
      Icc ((b-center) h+(L/4)*u h) ((b-center) h+(3*L/4)*u h) := by
  ext t
  constructor
  · rintro ⟨s,hs,rfl⟩
    simp only [mem_Icc,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    constructor <;> nlinarith [hs.1,hs.2]
  · intro ht
    refine ⟨(t-(b-center) h)/u h,⟨?_,?_⟩,?_⟩
    · apply (le_div_iff₀ hu).mpr
      linarith [ht.1]
    · apply (div_le_iff₀ hu).mpr
      linarith [ht.2]
    · simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
      field_simp
      ring

/-- Rational large-coordinate selection supplies a fixed fraction of ancestor
length, uniformly before scale. -/
theorem middleHalfHeights_fixed_interval {n : ℕ} (h : Fin (n+1))
    (b u center : EuclideanSpace ℝ (Fin (n+1))) (L : ℝ)
    (hL : 0 < L) (hu : 1/(n+2:ℝ) ≤ u h) :
    Icc ((b-center) h+(L/4)*u h)
      ((b-center) h+(L/4)*u h+L/(4*(n+2:ℝ))) ⊆ middleHalfHeights h b u center L := by
  have hn : 0 < (n+2:ℝ) := by positivity
  have hup : 0 < u h := (one_div_pos.mpr hn).trans_le hu
  rw [middleHalfHeights_eq h b u center L hup]
  apply Icc_subset_Icc le_rfl
  have hh := mul_le_mul_of_nonneg_left hu hL.le
  have he : L/(4*(n+2:ℝ))=(L*(1/(n+2:ℝ)))/4 := by field_simp
  rw [he]
  nlinarith

/-- The scale-dependent height bound used by the universal start constraints
comes from the actual cylinder and localized witness, not an extra assumption. -/
theorem localized_middleHalfHeights_bound {n : ℕ} (h : Fin (n+1))
    (b u center w : EuclideanSpace ℝ (Fin (n+1))) (L ell delta C : ℝ)
    (hu : ‖u‖=1) (hL : 0 < L) (hdelta : 0 < delta) (hdeltaL : delta≤L)
    (hell : ell≤L) (hC : 0≤C)
    (hw : w∈flatCylinder b u L delta) (hwball : dist w center<C*ell) :
    ∀ t∈middleHalfHeights h b u center L, |t|≤(C+3)*L := by
  rintro t ⟨s,hs,rfl⟩
  have hp : b+s • u∈flatCylinder b u L delta := by
    refine ⟨s,by linarith [hs.1],by linarith [hs.2],?_,?_⟩
    · simp
    · simpa using hdelta
  have hd := flatCylinder_pair_dist_lt b u (b+s • u) w L delta hu hp hw
  have ht := dist_triangle (b+s • u) w center
  have hc : |(b+s • u-center) h|≤dist (b+s • u) center := by
    simpa only [Real.norm_eq_abs,dist_eq_norm] using PiLp.norm_apply_le (b+s • u-center) h
  have hscale := mul_le_mul_of_nonneg_left hell hC
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.middleHalfHeights_fixed_interval
#print axioms KakeyaTwoScale.localized_middleHalfHeights_bound
