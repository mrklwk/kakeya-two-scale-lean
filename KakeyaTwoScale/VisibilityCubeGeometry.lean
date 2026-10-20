module
public import KakeyaTwoScale.ScaledVisibilityTests

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

def visibilityCube {N : ℕ} (z : Fin N → ℝ) : Set (Fin N → ℝ) := closedBall z (1/2)
def visibilityCenters {N : ℕ} (z : Fin N → ℝ) : Set (Fin N → ℝ) := closedBall z (1/8)

theorem visibilityCube_volume {N : ℕ} (z : Fin N → ℝ) : volume (visibilityCube z)=1 := by
  simp [visibilityCube]

theorem visibilityCenters_volume {N : ℕ} (z : Fin N → ℝ) :
    volume (visibilityCenters z)=ENNReal.ofReal ((1/4:ℝ)^N) := by
  rw [visibilityCenters,Real.volume_pi_closedBall z (by norm_num : (0:ℝ)≤1/8)]
  norm_num

theorem scaled_bank_test_in_cube {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (q : ℝ)
    (hB : B ∈ boundedEllipsoidClass N (1/4) q)
    (η : ℝ) (hη : 0<η) (hηsmall : η≤1/16) (z b : Fin N → ℝ)
    (hb : b ∈ visibilityCenters z) :
    affineEllipsoid (scaledEllipsoidMap B η hη) b ⊆ visibilityCube z := by
  rintro y ⟨x,hx,rfl⟩
  have hx' : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖<1 := by
    simpa [coordinateEuclideanBall] using hx
  have he := bankShape_outer_bound B q hB x
  have hp : ‖B x‖ ≤ ‖(WithLp.toLp 2 (B x) : EuclideanSpace ℝ (Fin N))‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact PiLp.norm_apply_le (WithLp.toLp 2 (B x) : EuclideanSpace ℝ (Fin N)) i
  have ht : ‖scaledEllipsoidMap B η hη x‖ ≤ 1/8 := by
    rw [scaledEllipsoidMap_apply,norm_smul,Real.norm_eq_abs,abs_of_pos hη]
    nlinarith
  have hb' : ‖b-z‖≤1/8 := by simpa [visibilityCenters,dist_eq_norm] using hb
  have htri := norm_add_le (b-z) (scaledEllipsoidMap B η hη x)
  change dist (b+scaledEllipsoidMap B η hη x) z ≤ 1/2
  rw [dist_eq_norm]
  have heq : b+scaledEllipsoidMap B η hη x-z = (b-z)+scaledEllipsoidMap B η hη x := by abel
  rw [heq]
  linarith

/-- Every finite family of actual cubes has a common enclosing Euclidean radius. -/
theorem finite_visibility_cubes_bounded {N J : ℕ} (z : Fin J → Fin N → ℝ) :
    ∃ r : ℝ, ∃ _hr : 0≤r, ∀ j x, x∈visibilityCube (z j) →
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖≤r := by
  have hc : IsCompact (⋃ j, visibilityCube (z j)) :=
    isCompact_iUnion (fun j => isCompact_closedBall _ _)
  obtain ⟨r,hr,hbound⟩ := (hc.image (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ))).isBounded.exists_pos_norm_le
  exact ⟨r,hr.le,fun j x hx => hbound _ ⟨x,mem_iUnion.mpr ⟨j,hx⟩,rfl⟩⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.scaled_bank_test_in_cube
