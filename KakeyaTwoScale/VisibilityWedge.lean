module
public import KakeyaTwoScale.VisibilityFactorization
public import KakeyaTwoScale.UnitWedgeBound

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Hadamard's inequality for the actual Gram volume, with dependent tuples included. -/
theorem tupleWedgeVolume_le_prod_norm {N k : ℕ}
    (v : Fin k → EuclideanSpace ℝ (Fin N)) :
    tupleWedgeVolume v ≤ ∏ i, ‖v i‖ := by
  induction k with
  | zero => simp [tupleWedgeVolume, Matrix.gram]
  | succ k ih =>
    rw [← Fin.cons_self_tail v, tupleWedgeVolume_cons]
    have hp := (Submodule.span ℝ (Set.range (Fin.tail v)))ᗮ.norm_starProjection_apply_le (v 0)
    change ‖normalProjection (Submodule.span ℝ (Set.range (Fin.tail v))) (v 0)‖ ≤ ‖v 0‖ at hp
    have hh := mul_le_mul (ih (Fin.tail v)) hp (norm_nonneg _)
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    simpa [Fin.prod_univ_succ, Fin.tail_def, mul_comm] using hh

/-- The full-dimensional Gram volume is the absolute coordinate determinant. -/
theorem tupleWedgeVolume_full_eq_det {N : ℕ}
    (v : Fin N → EuclideanSpace ℝ (Fin N)) :
    tupleWedgeVolume v = |(Matrix.of (fun i j => v j i)).det| := by
  unfold tupleWedgeVolume
  rw [Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun (Fin N) ℝ), Matrix.det_mul,
    Matrix.det_conjTranspose]
  simp only [EuclideanSpace.basisFun_repr, star_trivial]
  rw [← sq, Real.sqrt_sq_eq_abs]

/-- Exact determinant covariance for one invertible coordinate map. -/
theorem tupleWedgeVolume_full_map {N : ℕ}
    (A : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ))
    (v : Fin N → Fin N → ℝ) :
    tupleWedgeVolume (fun i => WithLp.toLp 2 (A (v i))) =
      |A.toContinuousLinearMap.det| * tupleWedgeVolume (fun i => WithLp.toLp 2 (v i)) := by
  rw [tupleWedgeVolume_full_eq_det, tupleWedgeVolume_full_eq_det]
  have he : Matrix.of (fun i j => A (v j) i) =
      LinearMap.toMatrix' A.toContinuousLinearMap.toLinearMap * Matrix.of (fun i j => v j i) := by
    ext i j
    exact (congrFun (LinearMap.toMatrix'_mulVec A.toContinuousLinearMap.toLinearMap (v j)) i).symm
  change |(Matrix.of (fun i j => A (v j) i)).det| = _
  rw [he, Matrix.det_mul, abs_mul, LinearMap.det_toMatrix']

/-- Complete a shorter tuple by a unit normal without changing its Gram volume. -/
theorem exists_unit_normal_tuple {N k : ℕ} (hk : k<N)
    (v : Fin k → EuclideanSpace ℝ (Fin N)) :
    ∃ u : EuclideanSpace ℝ (Fin N), ‖u‖=1 ∧
      tupleWedgeVolume (Fin.cons u v)=tupleWedgeVolume v := by
  let H := Submodule.span ℝ (Set.range v)
  have hd : Module.finrank ℝ H≤k := by
    simpa [H, Set.finrank] using (finrank_range_le_card (R:=ℝ) v)
  have hlt : Module.finrank ℝ H < Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) := by
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    omega
  obtain ⟨x,hx⟩ := H.exists_of_finrank_lt hlt
  have hxout : x∉H := by simpa using hx 1 one_ne_zero
  have hn : 0<‖normalProjection H x‖ := by
    apply norm_pos_iff.mpr
    intro he
    have he' : x=H.starProjection x := by
      simpa only [normalProjection,Submodule.starProjection_orthogonal_val,sub_eq_zero] using he
    exact hxout (he' ▸ H.starProjection_apply_mem x)
  refine ⟨normalDirection H x,normalDirection_unit H hn,?_⟩
  rw [tupleWedgeVolume_cons]
  change tupleWedgeVolume v * ‖normalProjection H (normalDirection H x)‖ = _
  rw [normalDirection_projection,normalDirection_unit H hn,mul_one]

/-- The full-dimensional determinant estimate for the actual visibility body. -/
theorem visibility_full_wedge_bound {N : ℕ} (hN : 0<N)
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N))) (hp : Continuous p)
    (C : ℝ) (hC : 0≤C) (hupper : ∀v, p v≤C*‖v‖)
    (hlower : ∀v, ‖v‖≤p v) (v : Fin N → EuclideanSpace ℝ (Fin N)) :
    tupleWedgeVolume v * volume.real (coordinateEuclideanBall N 1) ≤
      volume.real (coordinateVisibilityBody p) * (2*(N:ℝ)^2)^N * ∏i, p (v i) := by
  obtain ⟨A,hdet,hdir⟩ := nondegenerate_visibility_factorization hN p hp C hC hupper hlower
  have he := tupleWedgeVolume_full_map A (fun i => A.symm (WithLp.ofLp (v i)))
  simp only [ContinuousLinearEquiv.apply_symm_apply, WithLp.toLp_ofLp] at he
  have hprod := visibility_factor_direction_product p A hdir (fun i => WithLp.ofLp (v i))
  simp only [WithLp.toLp_ofLp] at hprod
  have hw := (tupleWedgeVolume_le_prod_norm (fun i => WithLp.toLp 2 (A.symm (WithLp.ofLp (v i))))).trans hprod
  calc
    _ = |A.toContinuousLinearMap.det| *
        tupleWedgeVolume (fun i => WithLp.toLp 2 (A.symm (WithLp.ofLp (v i)))) *
        volume.real (coordinateEuclideanBall N 1) := by rw [he]
    _ ≤ |A.toContinuousLinearMap.det| * ((2*(N:ℝ)^2)^N * ∏i, p (v i)) *
        volume.real (coordinateEuclideanBall N 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (abs_nonneg _)) (measureReal_nonneg)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hdet
        (show 0≤(2*(N:ℝ)^2)^N * ∏i, p (v i) from
          mul_nonneg (pow_nonneg (by positivity) _) (Finset.prod_nonneg (fun i _ => apply_nonneg p (v i))))
      nlinarith only [hh]

/-- Dimension descent retains the indispensable upper-bound power N-k.
The completion is constructed even for dependent tuples. -/
theorem wedge_bound_descend {N k : ℕ} (hk : k≤N)
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N)))
    (C W V : ℝ) (hC : 0≤C) (hW : 0≤W)
    (hupper : ∀v, ‖v‖=1 → p v≤C)
    (hfull : ∀v : Fin N → EuclideanSpace ℝ (Fin N),
      tupleWedgeVolume v * V ≤ W * ∏i, p (v i))
    (v : Fin k → EuclideanSpace ℝ (Fin N)) :
    tupleWedgeVolume v * V ≤ W * C^(N-k) * ∏i, p (v i) := by
  have aux : ∀d k : ℕ, N-k=d → k≤N →
      ∀v : Fin k → EuclideanSpace ℝ (Fin N),
        tupleWedgeVolume v * V ≤ W * C^(N-k) * ∏i, p (v i) := by
    intro d
    induction d with
    | zero =>
      intro k he hk v
      have heq : k=N := by omega
      subst k
      simpa using hfull v
    | succ d ih =>
      intro k he hk v
      obtain ⟨u,hu,hv⟩ := exists_unit_normal_tuple (by omega : k<N) v
      have hh := ih (k+1) (by omega) (by omega) (Fin.cons u v)
      rw [hv,Fin.prod_univ_succ] at hh
      simp only [Fin.cons_zero,Fin.cons_succ] at hh
      have hmult := mul_le_mul_of_nonneg_left (hupper u hu)
        (show 0≤W*C^(N-(k+1))*(∏i, p (v i)) from
          mul_nonneg (mul_nonneg hW (pow_nonneg hC _))
            (Finset.prod_nonneg (fun i _ => apply_nonneg p (v i))))
      have heq : N-k=(N-(k+1))+1 := by omega
      rw [heq,pow_succ]
      nlinarith only [hh,hmult]
  exact aux (N-k) k rfl hk v

/-- Actual all-k visibility-to-wedge estimate, with the same dimension-only
factor and the exact complementary power of the directional upper bound. -/
theorem visibility_wedge_bound {N k : ℕ} (hN : 0<N) (hk : k≤N)
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N))) (hp : Continuous p)
    (C : ℝ) (hC : 0≤C) (hupper : ∀v, p v≤C*‖v‖)
    (hlower : ∀v, ‖v‖≤p v) (v : Fin k → EuclideanSpace ℝ (Fin N)) :
    tupleWedgeVolume v * volume.real (coordinateEuclideanBall N 1) ≤
      (volume.real (coordinateVisibilityBody p) * (2*(N:ℝ)^2)^N) *
        C^(N-k) * ∏i, p (v i) := by
  apply wedge_bound_descend hk p C _ _ hC (by positivity)
    (fun v hv => by simpa [hv] using hupper v)
  exact visibility_full_wedge_bound hN p hp C hC hupper hlower

end KakeyaTwoScale
#print axioms KakeyaTwoScale.tupleWedgeVolume_le_prod_norm
#print axioms KakeyaTwoScale.tupleWedgeVolume_full_eq_det

#print axioms KakeyaTwoScale.tupleWedgeVolume_full_map
#print axioms KakeyaTwoScale.exists_unit_normal_tuple
#print axioms KakeyaTwoScale.visibility_full_wedge_bound
#print axioms KakeyaTwoScale.wedge_bound_descend
#print axioms KakeyaTwoScale.visibility_wedge_bound
