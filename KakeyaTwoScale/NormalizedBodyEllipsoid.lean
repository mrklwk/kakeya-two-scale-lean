module
public import KakeyaTwoScale.ConvexCoordinateEllipsoid
public import KakeyaTwoScale.FiniteEllipsoidBank

@[expose] public section

open Set Metric
noncomputable section
namespace KakeyaTwoScale

/-- Normalize the constructed comparison to an actual unit-ball ellipsoid.
The closed outer radius is N² and is uniform over every eligible convex body. -/
theorem exists_normalized_body_ellipsoid {N : ℕ} (hN : 0<N)
    (K : Set (Fin N → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hneg : ∀ x ∈ K, -x ∈ K) (ρ : ℝ) (hρ : 0<ρ)
    (hinner : coordinateEuclideanBall N ρ ⊆ K) :
    ∃ A : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ),
      affineEllipsoid A 0 ⊆ K ∧
      ∀ x ∈ K, ‖(WithLp.toLp 2 (A.symm x) : EuclideanSpace ℝ (Fin N))‖ ≤ (N:ℝ)^2 := by
  obtain ⟨B,hi,ho⟩ := exists_coordinate_ellipsoid_comparison hN K hK hconv hneg ρ hρ hinner
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  let A := (LinearEquiv.smulOfNeZero ℝ (Fin N → ℝ) (1/(N:ℝ)) (by positivity) :
    (Fin N → ℝ) ≃ₗ[ℝ] (Fin N → ℝ)).toContinuousLinearEquiv.trans B
  have happ (x) : A x = (1/(N:ℝ)) • B x := by
    change B ((1/(N:ℝ)) • x) = _
    exact B.map_smul _ _
  have hinv (x) : A.symm x = (N:ℝ) • B.symm x := by
    apply A.injective
    rw [A.apply_symm_apply,happ,B.map_smul,B.apply_symm_apply,smul_smul]
    rw [div_mul_cancel₀ _ hNr.ne',one_smul]
  refine ⟨A,?_,?_⟩
  · rintro y ⟨x,hx,rfl⟩
    apply hi
    refine ⟨(1/(N:ℝ)) • x,?_,by simp only [zero_add,happ,map_smul]⟩
    have hnorm : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ < 1 := by
      simpa [coordinateEuclideanBall] using hx
    have he : (WithLp.toLp 2 ((1/(N:ℝ)) • x) : EuclideanSpace ℝ (Fin N)) =
        (1/(N:ℝ)) • WithLp.toLp 2 x := rfl
    simp only [coordinateEuclideanBall,mem_ofPred_eq,mem_ball_zero_iff,he,norm_smul,
      Real.norm_eq_abs,abs_of_pos (by positivity : (0:ℝ)<1/(N:ℝ))]
    exact (mul_lt_mul_of_pos_left hnorm (by positivity)).trans_eq (mul_one _)
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := ho hx
    rw [hinv,B.symm_apply_apply]
    have he : (WithLp.toLp 2 ((N:ℝ) • y) : EuclideanSpace ℝ (Fin N)) =
        (N:ℝ) • WithLp.toLp 2 y := rfl
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hNr]
    exact (mul_le_mul_of_nonneg_left hy hNr.le).trans_eq (by ring)

/-- A concrete, nonoptimal uniform bound from an open-ball bound. -/
theorem coordinate_linear_bound_from_ball {N : ℕ}
    (L : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) (r c : ℝ) (hr : 0<r)
    (hL : ∀ x ∈ coordinateEuclideanBall N r,
      ‖(WithLp.toLp 2 (L x) : EuclideanSpace ℝ (Fin N))‖ ≤ c) (x : Fin N → ℝ) :
    ‖(WithLp.toLp 2 (L x) : EuclideanSpace ℝ (Fin N))‖ ≤
      (2*c/r)*‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ := by
  by_cases hx : x=0
  · simp [hx]
  let t := ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖
  have ht : 0<t := norm_pos_iff.mpr (by simpa using hx)
  let s := r/(2*t)
  have hs : 0<s := by dsimp [s]; positivity
  have hst : s*t=r/2 := by dsimp [s]; field_simp
  have hmem : s • x ∈ coordinateEuclideanBall N r := by
    have he : (WithLp.toLp 2 (s • x) : EuclideanSpace ℝ (Fin N)) = s • WithLp.toLp 2 x := rfl
    simp only [coordinateEuclideanBall,mem_ofPred_eq,mem_ball_zero_iff,he,norm_smul,
      Real.norm_eq_abs,abs_of_pos hs]
    change s*t<r
    rw [hst]
    linarith
  have hh := hL (s • x) hmem
  have he : (WithLp.toLp 2 (L (s • x)) : EuclideanSpace ℝ (Fin N)) =
      s • WithLp.toLp 2 (L x) := by rw [map_smul]; rfl
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hs] at hh
  have hh' : ‖(WithLp.toLp 2 (L x) : EuclideanSpace ℝ (Fin N))‖ ≤ c/s :=
    (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using hh)
  apply hh'.trans_eq
  change c/(r/(2*t))=(2*c/r)*t
  field_simp

/-- Inner/outer body radii put the actual constructed ellipsoid in the bounded
inverse-form class used by the finite bank. Its parameters are fixed before K. -/
theorem exists_banked_body_ellipsoid {N : ℕ} (hN : 0<N)
    (K : Set (Fin N → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hneg : ∀ x ∈ K, -x ∈ K) (ρ : ℝ) (hρ : 0<ρ)
    (hinner : coordinateEuclideanBall N ρ ⊆ K)
    (houter : ∀ x ∈ K, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ ≤ 1) :
    ∃ A : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ),
      affineEllipsoid A 0 ⊆ K ∧
      (∀ x ∈ K, ‖(WithLp.toLp 2 (A.symm x) : EuclideanSpace ℝ (Fin N))‖ ≤ (N:ℝ)^2) ∧
      A ∈ boundedEllipsoidClass N (1/4) ((2*(N:ℝ)^2/ρ)^2) := by
  obtain ⟨A,hi,ho⟩ := exists_normalized_body_ellipsoid hN K hK hconv hneg ρ hρ hinner
  refine ⟨A,hi,ho,?_⟩
  intro x
  have hf (y : Fin N → ℝ) :
      ‖(WithLp.toLp 2 (A y) : EuclideanSpace ℝ (Fin N))‖ ≤
        2*‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin N))‖ := by
    simpa using coordinate_linear_bound_from_ball A 1 1 zero_lt_one
      (fun z hz => houter _ (hi ⟨z,hz,by simp⟩)) y
  have hb := coordinate_linear_bound_from_ball A.symm ρ ((N:ℝ)^2) hρ
    (fun z hz => ho z (hinner hz)) x
  have hf' := hf (A.symm x)
  rw [A.apply_symm_apply] at hf'
  constructor
  · nlinarith [norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N)),
      norm_nonneg (WithLp.toLp 2 (A.symm x) : EuclideanSpace ℝ (Fin N))]
  · have hc : 0 ≤ 2*(N:ℝ)^2/ρ := by positivity
    nlinarith [norm_nonneg (WithLp.toLp 2 (A.symm x) : EuclideanSpace ℝ (Fin N)),
      norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N)),
      mul_nonneg hc (norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N)))]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_normalized_body_ellipsoid
#print axioms KakeyaTwoScale.coordinate_linear_bound_from_ball
#print axioms KakeyaTwoScale.exists_banked_body_ellipsoid
