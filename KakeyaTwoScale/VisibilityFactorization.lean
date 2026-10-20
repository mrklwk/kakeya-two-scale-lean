module
public import KakeyaTwoScale.PrescribedVisibility

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Actual convex-body factorization for the next multilinear step. The map
is constructed; determinant/volume and every directional bound share it. -/
theorem seminorm_visibility_factorization {N : ℕ} (hN : 0<N)
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N))) (hp : Continuous p)
    (C : ℝ) (hC : 0≤C) (hbound : ∀ v, p v≤C*‖v‖) :
    ∃ A : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ),
      |A.toContinuousLinearMap.det| *volume.real (coordinateEuclideanBall N 1)≤
        volume.real (coordinateVisibilityBody p) ∧
      ∀ x : Fin N → ℝ,
        ‖(WithLp.toLp 2 (A.symm x) : EuclideanSpace ℝ (Fin N))‖≤
          (N:ℝ)^2*(‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖+p (WithLp.toLp 2 x)) := by
  have hi : coordinateEuclideanBall N (1/(1+C)) ⊆ coordinateVisibilityBody p := by
    intro x hx
    exact closedBall_subset_seminormVisibilityBody p C hC hbound (ball_subset_closedBall hx)
  obtain ⟨A,hAi,hAo⟩ := exists_normalized_body_ellipsoid hN (coordinateVisibilityBody p)
    (coordinateVisibilityBody_compact p hp) (coordinateVisibilityBody_convex p)
    (fun x hx => (seminormVisibilityBody_neg p (WithLp.toLp 2 x)).mpr hx)
    (1/(1+C)) (by positivity) hi
  refine ⟨A,?_,?_⟩
  · have hv : volume.real (affineEllipsoid A 0)≤volume.real (coordinateVisibilityBody p) :=
      measureReal_mono hAi (coordinateVisibilityBody_compact p hp).measure_lt_top.ne
    simpa only [Measure.real,affineEllipsoid_volume,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _)] using hv
  · intro x
    by_cases hx : x=0
    · simp [hx]
    let g := ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖+p (WithLp.toLp 2 x)
    have hxpos : 0<‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ :=
      norm_pos_iff.mpr (by simpa using hx)
    have hg : 0<g := add_pos_of_pos_of_nonneg hxpos (apply_nonneg p _)
    have hn : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖≤g := by
      dsimp [g]; exact le_add_of_nonneg_right (apply_nonneg p _)
    have hpg : p (WithLp.toLp 2 x)≤g := by dsimp [g]; exact le_add_of_nonneg_left (norm_nonneg _)
    have hmem : g⁻¹ • x ∈ coordinateVisibilityBody p := by
      change ‖g⁻¹ • (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖≤1 ∧
        p (g⁻¹ • WithLp.toLp 2 x)≤1
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hg),map_smul_eq_mul,
        Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hg)]
      constructor
      · exact (inv_mul_le_iff₀ hg).mpr (by simpa using hn)
      · exact (inv_mul_le_iff₀ hg).mpr (by simpa using hpg)
    have hh := hAo _ hmem
    have he : (WithLp.toLp 2 (A.symm (g⁻¹ • x)) : EuclideanSpace ℝ (Fin N)) =
        g⁻¹ • WithLp.toLp 2 (A.symm x) := by rw [map_smul]; rfl
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hg)] at hh
    have h := (inv_mul_le_iff₀ hg).mp hh
    simpa only [mul_comm] using h

/-- If the directional seminorm dominates the norm, the same constructed map
has a pure seminorm bound. This is the nondegenerate factorization used by the
visibility-to-geometric-mean step; norm domination is explicit. -/
theorem nondegenerate_visibility_factorization {N : ℕ} (hN : 0<N)
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N))) (hp : Continuous p)
    (C : ℝ) (hC : 0≤C) (hbound : ∀ v, p v≤C*‖v‖)
    (hlower : ∀ v, ‖v‖≤p v) :
    ∃ A : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ),
      |A.toContinuousLinearMap.det| *volume.real (coordinateEuclideanBall N 1)≤
        volume.real (coordinateVisibilityBody p) ∧
      ∀ x : Fin N → ℝ,
        ‖(WithLp.toLp 2 (A.symm x) : EuclideanSpace ℝ (Fin N))‖≤
          (2*(N:ℝ)^2)*p (WithLp.toLp 2 x) := by
  obtain ⟨A,hdet,hdir⟩ := seminorm_visibility_factorization hN p hp C hC hbound
  refine ⟨A,hdet,?_⟩
  intro x
  have hh := hdir x
  have hl := mul_le_mul_of_nonneg_left (hlower (WithLp.toLp 2 x)) (sq_nonneg (N:ℝ))
  nlinarith

/-- Products of actual directional values control the product after the same
invertible change of coordinates, uniformly in the number of directions. -/
theorem visibility_factor_direction_product {N k : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N)))
    (A : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ))
    (hA : ∀ x, ‖(WithLp.toLp 2 (A.symm x) : EuclideanSpace ℝ (Fin N))‖≤
      (2*(N:ℝ)^2)*p (WithLp.toLp 2 x)) (v : Fin k → Fin N → ℝ) :
    (∏ i, ‖(WithLp.toLp 2 (A.symm (v i)) : EuclideanSpace ℝ (Fin N))‖)≤
      (2*(N:ℝ)^2)^k*(∏ i, p (WithLp.toLp 2 (v i))) := by
  calc
    _ ≤ ∏ i, (2*(N:ℝ)^2)*p (WithLp.toLp 2 (v i)) :=
      Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hA (v i))
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- The factorization for the literal averaged polynomial-area family, with
continuity and the finite norm bound supplied by the proved analytic theory. -/
theorem mollified_visibility_factorization {d n D : ℕ}
    (m : Fin d → (Fin (n+1) →₀ ℕ)) (hm : Function.Injective m)
    (hdegree : ∀ i, (m i).sum (fun _ e => e)≤D)
    (U : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U) (hreg : IsOpen U ∨ IsClosed U)
    (r : ℝ) (hr : 0≤r)
    (hb : ∀ x∈U, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖≤r)
    (ε : ℝ) (hε : 0<ε) (hε2 : ε<2)
    (p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    ∃ A : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ),
      |A.toContinuousLinearMap.det| *volume.real (coordinateEuclideanBall (n+1) 1)≤
        volume.real (coordinateVisibilityBody
          (mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hb ε p)) ∧
      ∀ x : Fin (n+1) → ℝ,
        ‖(WithLp.toLp 2 (A.symm x) : EuclideanSpace ℝ (Fin (n+1)))‖≤
          ((n+1:ℕ):ℝ)^2*(‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (n+1)))‖+
            mollifiedCoefficientArea m hm U hU r hr hb ε p (WithLp.toLp 2 x)) := by
  have hc : Continuous (mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hb ε p) := by
    have hh := (continuous_mollifiedArea_joint m hm hdegree U hU hreg r hr hb ε hε hε2).comp
      (show Continuous (fun v : EuclideanSpace ℝ (Fin (n+1)) => (p,v)) from
        continuous_const.prodMk continuous_id)
    exact hh
  obtain ⟨A,hdet,hdir⟩ := seminorm_visibility_factorization (by omega : 0<n+1)
    (mollifiedAreaSeminorm m hm hdegree U hU hreg r hr hb ε p) hc
    (((D:ℝ≥0∞)*volume (closedBall (0:Fin n→ℝ) r)).toReal) ENNReal.toReal_nonneg
    (mollifiedAreaSeminorm_le m hm hdegree U hU hreg r hr hb ε hε p)
  refine ⟨A,hdet,?_⟩
  intro x
  simpa only [mollifiedAreaSeminorm_apply m hm hdegree U hU hreg r hr hb ε p] using hdir x

end KakeyaTwoScale
#print axioms KakeyaTwoScale.seminorm_visibility_factorization
#print axioms KakeyaTwoScale.nondegenerate_visibility_factorization
#print axioms KakeyaTwoScale.visibility_factor_direction_product

#print axioms KakeyaTwoScale.mollified_visibility_factorization
