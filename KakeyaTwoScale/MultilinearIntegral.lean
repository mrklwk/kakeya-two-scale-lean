module
public import KakeyaTwoScale.WeightedCubeMultilinear

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

/-- The explicit infinite-line neighborhood is the sublevel set of the
continuous orthogonal residual, including radius zero and arbitrary axes. -/
theorem infiniteLineTube_iff_projection {N : ℕ} (b x : Fin N → ℝ)
    (u : EuclideanSpace ℝ (Fin N)) (r : ℝ) :
    x∈infiniteLineTube b (WithLp.ofLp u) r ↔
      ‖normalProjection (ℝ ∙ u) (WithLp.toLp 2 (x-b))‖≤r := by
  let H := ℝ ∙ u
  constructor
  · rintro ⟨t,ht⟩
    have he : normalProjection H (WithLp.toLp 2 (x-(b+t • WithLp.ofLp u)))=
        normalProjection H (WithLp.toLp 2 (x-b)) := by
      have hs : (WithLp.toLp 2 (x-(b+t • WithLp.ofLp u)) : EuclideanSpace ℝ (Fin N))=
          WithLp.toLp 2 (x-b)-t • u := by ext i; simp; ring
      rw [hs,map_sub,normalProjection_zero H (H.smul_mem t (Submodule.mem_span_singleton_self u)),sub_zero]
    have hh := Hᗮ.norm_starProjection_apply_le
      (WithLp.toLp 2 (x-(b+t • WithLp.ofLp u)))
    change ‖normalProjection H _‖≤_ at hh
    rw [he] at hh
    exact hh.trans ht
  · intro hx
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp
      (H.starProjection_apply_mem (WithLp.toLp 2 (x-b)))
    refine ⟨t,?_⟩
    have he : (WithLp.toLp 2 (x-(b+t • WithLp.ofLp u)) : EuclideanSpace ℝ (Fin N))=
        normalProjection H (WithLp.toLp 2 (x-b)) := by
      rw [normalProjection,Submodule.starProjection_orthogonal_val,← ht]
      ext i
      simp
      ring
    rwa [he]

theorem infiniteLineTube_closed {N : ℕ} (b u : Fin N → ℝ) (r : ℝ) :
    IsClosed (infiniteLineTube b u r) := by
  have he : infiniteLineTube b u r =
      {x | ‖normalProjection (ℝ ∙ (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin N))) (WithLp.toLp 2 (x-b))‖≤r} := by
    ext x
    exact infiniteLineTube_iff_projection b x (WithLp.toLp 2 u) r
  rw [he]
  exact isClosed_le
    ((normalProjection _).continuous.comp ((PiLp.continuous_toLp 2 _).comp
      (continuous_id.sub continuous_const))).norm continuous_const

def weightedTubeFunction {n k : ℕ} (L : Fin k → ℕ)
    (b : (j : Fin k) → Fin (L j) → Fin (n+1) → ℝ)
    (u : (j : Fin k) → Fin (L j) → EuclideanSpace ℝ (Fin (n+1)))
    (a : (j : Fin k) → Fin (L j) → ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  ∑f : (j : Fin k) → Fin (L j), tupleWedgeVolume (fun j => u j (f j))*
    ∏j, (infiniteLineTube (b j (f j)) (WithLp.ofLp (u j (f j))) 1).indicator (fun _ => a j (f j)) x

theorem weightedTubeFunction_measurable {n k : ℕ} (L : Fin k → ℕ) (b u a) :
    Measurable (weightedTubeFunction (n:=n) L b u a) := by
  apply Finset.measurable_sum
  intro f _
  apply Measurable.const_mul
  apply Finset.measurable_prod
  intro j _
  exact measurable_const.indicator (infiniteLineTube_closed _ _ _).measurableSet

theorem weightedTubeFunction_nonneg {n k : ℕ} (L : Fin k → ℕ) (b u a)
    (ha : ∀j t, 0≤a j t) (x : Fin (n+1) → ℝ) : 0≤weightedTubeFunction L b u a x := by
  apply Finset.sum_nonneg
  intro f _
  apply mul_nonneg (tupleWedgeVolume_nonneg _)
  apply Finset.prod_nonneg
  intro j _
  exact Set.indicator_nonneg (fun _ _ => ha j (f j)) x

/-- A pointwise tuple contribution is bounded by the literal incidence sum
of every closed unit cube containing the point. -/
theorem weightedTubeFunction_le_cube {n k : ℕ} (L : Fin k → ℕ) (b u a)
    (ha : ∀j t, 0≤a j t) (z : Fin (n+1) → ℤ) (x : Fin (n+1) → ℝ)
    (hx : x∈visibilityCube (fun i => (z i:ℝ))) :
    weightedTubeFunction L b u a x≤cubeMultilinearMass L b u a z := by
  apply Finset.sum_le_sum
  intro f _
  apply mul_le_mul_of_nonneg_left _ (tupleWedgeVolume_nonneg _)
  apply Finset.prod_le_prod₀
  · intro j _
    exact Set.indicator_nonneg (fun _ _ => ha j (f j)) x
  · intro j _
    by_cases ht : x∈infiniteLineTube (b j (f j)) (WithLp.ofLp (u j (f j))) 1
    · rw [Set.indicator_of_mem ht]
      have hi : (visibilityCube (fun i => (z i:ℝ)) ∩ infiniteLineTube (b j (f j))
          (WithLp.ofLp (u j (f j))) 1).Nonempty := ⟨x,hx,ht⟩
      simp only [cubeTubeWeight,ite_eq_left hi]
      exact le_rfl
    · rw [Set.indicator_of_notMem ht]
      exact cubeTubeWeight_nonneg L b u a ha z j (f j)

/-- Integer-centered closed unit cubes cover the entire coordinate space. -/
theorem exists_lattice_visibilityCube {N : ℕ} (x : Fin N → ℝ) :
    ∃z : Fin N → ℤ, x∈visibilityCube (fun i => (z i:ℝ)) := by
  refine ⟨fun i => ⌊x i+(1/2:ℝ)⌋,?_⟩
  apply (dist_pi_le_iff (by norm_num : (0:ℝ)≤1/2)).mpr
  intro i
  rw [Real.dist_eq,abs_le]
  have hl := Int.floor_le (x i+(1/2:ℝ))
  have hu := Int.lt_floor_add_one (x i+(1/2:ℝ))
  constructor <;> linarith

/-- Integrate a literal cube-wise domination over the whole space. Countable
coverage is proved, and overlap can only enlarge this upper bound. -/
theorem lintegral_le_lattice_cube_sum {N : ℕ}
    (f : (Fin N → ℝ) → ℝ≥0∞) (g : (Fin N → ℤ) → ℝ≥0∞)
    (h : ∀z x, x∈visibilityCube (fun i => (z i:ℝ)) → f x≤g z) :
    (∫⁻x, f x)≤∑'z, g z := by
  have hm (z : Fin N → ℤ) : Measurable
      ((visibilityCube (fun i => (z i:ℝ))).indicator (fun _ => g z)) :=
    measurable_const.indicator measurableSet_closedBall
  calc
    _ ≤ ∫⁻x, ∑'z : Fin N → ℤ,
        (visibilityCube (fun i => (z i:ℝ))).indicator (fun _ => g z) x := by
      apply lintegral_mono
      intro x
      obtain ⟨z,hz⟩ := exists_lattice_visibilityCube x
      have hh := h z x hz
      rw [← Set.indicator_of_mem hz (fun _ => g z)] at hh
      exact hh.trans (ENNReal.le_tsum (f := fun w : Fin N → ℤ => (visibilityCube (fun i => (w i:ℝ))).indicator (fun _ => g w) x) z)
    _ = ∑'z : Fin N → ℤ, ∫⁻x,
        (visibilityCube (fun i => (z i:ℝ))).indicator (fun _ => g z) x :=
      lintegral_tsum (fun z => (hm z).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro z
      rw [lintegral_indicator (show MeasurableSet (visibilityCube (fun i => (z i:ℝ))) from measurableSet_closedBall),lintegral_const,Measure.restrict_apply_univ]
      have hv : volume (visibilityCube (fun i => (z i:ℝ)))=1 := by
        rw [visibilityCube,Real.volume_pi_closedBall _ (by norm_num : (0:ℝ)≤1/2)]
        norm_num
      rw [hv,mul_one]

/-- The actual determinant-weighted multilinear Kakeya estimate for radius-one
neighborhoods of doubly infinite lines. The wedge has power one inside the
sum; arbitrary nonnegative real weights and repeated tubes are allowed.
Constants precede all families, with no separation hypothesis. -/
theorem weighted_multilinear_kakeya_unit (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1) :
    ∃C : ℝ, 0<C ∧ ∀(L : Fin k → ℕ)
      (b : (j : Fin k) → Fin (L j) → Fin (n+1) → ℝ)
      (u : (j : Fin k) → Fin (L j) → EuclideanSpace ℝ (Fin (n+1)))
      (a : (j : Fin k) → Fin (L j) → ℝ), (∀j t, ‖u j t‖=1) → (∀j t, 0≤a j t) →
      (∫⁻x, ENNReal.ofReal ((weightedTubeFunction L b u a x)^(1/((k-1:ℕ):ℝ))))≤
        ENNReal.ofReal (C*(∏j, ∑t, a j t)^(1/((k-1:ℕ):ℝ))) := by
  classical
  obtain ⟨C,hC,hfinite⟩ := weighted_cube_multilinear n k hk hkn
  refine ⟨C+1,by linarith,?_⟩
  intro L b u a hu ha
  let g := fun z : Fin (n+1) → ℤ => (cubeMultilinearMass L b u a z)^(1/((k-1:ℕ):ℝ))
  have hg (z) : 0≤g z := Real.rpow_nonneg (cubeMultilinearMass_nonneg L b u a ha z) _
  have hsum : (∑'z, ENNReal.ofReal (g z))≤
      ENNReal.ofReal (C*(∏j, ∑t, a j t)^(1/((k-1:ℕ):ℝ))) := by
    apply ENNReal.summable.tsum_le_of_sum_le
    intro s
    let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
    have hz : Function.Injective (fun q => (e q).val) :=
      Subtype.val_injective.comp e.injective
    have hh := hfinite (Fintype.card s) (fun q => (e q).val) hz L b u a hu ha
    change (∑q, g (e q).val)≤_ at hh
    have he : (∑q, g (e q).val)=(∑z∈s, g z) := by
      exact (Equiv.sum_comp e (fun z : s => g z.val)).trans (Finset.sum_coe_sort s g)
    rw [he] at hh
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hg z)]
    exact ENNReal.ofReal_le_ofReal hh
  have hpoint := lintegral_le_lattice_cube_sum
    (fun x => ENNReal.ofReal ((weightedTubeFunction L b u a x)^(1/((k-1:ℕ):ℝ))))
    (fun z => ENNReal.ofReal (g z)) (fun z x hx => ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (weightedTubeFunction_nonneg L b u a ha x)
        (weightedTubeFunction_le_cube L b u a ha z x hx) (by positivity)))
  apply (hpoint.trans hsum).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by linarith : C≤C+1)
    (Real.rpow_nonneg (Finset.prod_nonneg (fun j _ => Finset.sum_nonneg (fun t _ => ha j t))) _)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.infiniteLineTube_iff_projection
#print axioms KakeyaTwoScale.infiniteLineTube_closed
#print axioms KakeyaTwoScale.weightedTubeFunction_measurable
#print axioms KakeyaTwoScale.weightedTubeFunction_le_cube
#print axioms KakeyaTwoScale.exists_lattice_visibilityCube

#print axioms KakeyaTwoScale.lintegral_le_lattice_cube_sum
#print axioms KakeyaTwoScale.weighted_multilinear_kakeya_unit
