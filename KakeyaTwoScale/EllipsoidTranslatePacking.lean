module
public import KakeyaTwoScale.CompactBallPacking
public import KakeyaTwoScale.AffineEllipsoidSignMass

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Radius-parametrized affine image of the Euclidean ball. -/
def affineCoordinateBall {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ) (r : ℝ) :=
  (fun y => b+B y) '' coordinateEuclideanBall N r

theorem affineCoordinateBall_volume {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (b : Fin N → ℝ) (r : ℝ) (hr : 0<r) :
    volume (affineCoordinateBall B b r) =
      ENNReal.ofReal (r^N) * volume (affineEllipsoid B 0) := by
  rw [affineCoordinateBall,volume_affine_image,coordinateEuclideanBall_scale N r hr,
    affineEllipsoid_volume]
  ring

private theorem euclidean_linear_image_ball {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ))
    (x : EuclideanSpace ℝ (Fin N)) (r : ℝ) :
    let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).trans B
    L '' ball x r = affineCoordinateBall B (L x) r := by
  dsimp only
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).trans B
  change L '' ball x r = _
  ext z
  constructor
  · rintro ⟨y,hy,rfl⟩
    refine ⟨WithLp.ofLp (y-x),?_,?_⟩
    · simpa [coordinateEuclideanBall,mem_ball_zero_iff,dist_eq_norm] using hy
    · change L x + L (y-x) = L y
      simp
  · rintro ⟨y,hy,rfl⟩
    refine ⟨x+WithLp.toLp 2 y,?_,?_⟩
    · simpa [coordinateEuclideanBall,mem_ball_zero_iff,dist_eq_norm] using hy
    · change L (x+WithLp.toLp 2 y) = L x + B y
      simp only [map_add]
      rfl

/-- A finite family of actual disjoint translates is constructed inside U.
Its total volume is bounded above by U and below by 3^(-N) times the volume
of the compact center region C. B may have arbitrary eccentricity. -/
theorem exists_ellipsoid_translate_packing {N : ℕ}
    (B : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ))
    (C U : Set (Fin N → ℝ)) (hC : IsCompact C)
    (hCU : ∀ b ∈ C, affineEllipsoid B b ⊆ U) :
    ∃ F : Finset (Fin N → ℝ), (↑F : Set (Fin N → ℝ)) ⊆ C ∧
      (↑F : Set (Fin N → ℝ)).PairwiseDisjoint (affineEllipsoid B) ∧
      (∀ b ∈ F, affineEllipsoid B b ⊆ U) ∧
      (F.card : ℝ≥0∞) * volume (affineEllipsoid B 0) ≤ volume U ∧
      volume C ≤ (F.card : ℝ≥0∞) * ENNReal.ofReal ((3:ℝ)^N) *
        volume (affineEllipsoid B 0) := by
  classical
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).trans B
  obtain ⟨G,hG,hdis,hcover⟩ := compact_disjoint_unit_ball_cover
    (L.symm '' C) (hC.image L.symm.continuous)
  let F := G.map L.toLinearEquiv.toEquiv.toEmbedding
  have hF : ∀ b ∈ F, b ∈ C := by
    intro b hb
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hb
    obtain ⟨y,hy,hxy⟩ := hG hx
    simpa [← hxy] using hy
  have hD : (↑F : Set (Fin N → ℝ)).PairwiseDisjoint (affineEllipsoid B) := by
    intro b hb c hc hbc
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hb
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hc
    have hh : Disjoint (L '' ball x 1) (L '' ball y 1) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
      have hvu := L.injective he
      exact Set.disjoint_left.mp (hdis hx hy (fun h => hbc (congrArg L h))) hu (hvu ▸ hv)
    change Disjoint (affineCoordinateBall B (L x) 1) (affineCoordinateBall B (L y) 1)
    rw [← euclidean_linear_image_ball B x 1,← euclidean_linear_image_ball B y 1]
    exact hh
  have hcov : C ⊆ ⋃ b ∈ F, affineCoordinateBall B b 3 := by
    intro y hy
    obtain ⟨x,hx,hxy⟩ := mem_iUnion₂.mp (hcover (mem_image_of_mem L.symm hy))
    refine mem_iUnion₂.mpr ⟨L x,Finset.mem_map.mpr ⟨x,hx,rfl⟩,?_⟩
    rw [← euclidean_linear_image_ball]
    exact ⟨L.symm y,hxy,L.apply_symm_apply y⟩
  refine ⟨F, hF, hD, fun b hb => hCU b (hF b hb),?_,?_⟩
  · calc
      _ = volume (⋃ b ∈ F, affineEllipsoid B b) := by
        rw [measure_biUnion_finset hD (fun b _ => (affineEllipsoid_open B b).measurableSet)]
        simp [affineEllipsoid_volume]
      _ ≤ volume U := measure_mono (iUnion₂_subset fun b hb => hCU b (hF b hb))
  · calc
      volume C ≤ volume (⋃ b ∈ F, affineCoordinateBall B b 3) := measure_mono hcov
      _ ≤ ∑ b ∈ F, volume (affineCoordinateBall B b 3) := measure_biUnion_finset_le _ _
      _ = _ := by simp [affineCoordinateBall_volume B _ 3 (by norm_num),mul_assoc]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.affineCoordinateBall_volume
#print axioms KakeyaTwoScale.exists_ellipsoid_translate_packing
