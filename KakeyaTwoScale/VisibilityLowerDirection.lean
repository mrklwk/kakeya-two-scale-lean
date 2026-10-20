module
public import KakeyaTwoScale.VisibilityWedge

@[expose] public section

open Set MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace KakeyaTwoScale

private theorem seminorm_finite_sum_le {N : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N)))
    {ι : Type*} (s : Finset ι) (v : ι → EuclideanSpace ℝ (Fin N)) :
    p (∑i∈s, v i)≤∑i∈s, p (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)

/-- An actual orthogonal box lies in the truncated seminorm body when its
coordinate norm and seminorm budgets sum to at most one. -/
theorem orthogonal_box_subset_visibility {N : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N)))
    (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (a : Fin N → ℝ) (_ha : ∀i, 0≤a i)
    (hn : ∑i, a i≤1)
    (hp : ∑i, a i*p (R (EuclideanSpace.single i 1))≤1) :
    orthogonalCoordinates R '' (univ.pi (fun i => Icc (-a i) (a i))) ⊆
      coordinateVisibilityBody p := by
  rintro _ ⟨x,hx,rfl⟩
  have hab (i) : |x i|≤a i := abs_le.mpr (hx i (mem_univ i))
  have he : R (WithLp.toLp 2 x) = ∑i, (x i) • R (EuclideanSpace.single i 1) := by
    simp_rw [← map_smul]
    rw [← map_sum]
    congr 1
    ext j
    simp [Pi.single_apply,mul_ite]
  change ‖R (WithLp.toLp 2 x)‖≤1 ∧ p (R (WithLp.toLp 2 x))≤1
  rw [he]
  constructor
  · calc
      _ ≤ ∑i, ‖(x i) • R (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
      _ = ∑i, |x i| := by simp [norm_smul,Real.norm_eq_abs]
      _ ≤ ∑i, a i := Finset.sum_le_sum (fun i _ => hab i)
      _ ≤ 1 := hn
  · calc
      _ ≤ ∑i, p ((x i) • R (EuclideanSpace.single i 1)) := seminorm_finite_sum_le p _ _
      _ = ∑i, |x i| *p (R (EuclideanSpace.single i 1)) := by simp [map_smul_eq_mul,Real.norm_eq_abs]
      _ ≤ ∑i, a i*p (R (EuclideanSpace.single i 1)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hab i) (apply_nonneg p _))
      _ ≤ 1 := hp

/-- The lower volume is the volume of a constructed orthogonal box. -/
theorem orthogonal_box_visibility_volume_lower {N : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin N))) (hcont : Continuous p)
    (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (a : Fin N → ℝ) (ha : ∀i, 0≤a i)
    (hn : ∑i, a i≤1)
    (hp : ∑i, a i*p (R (EuclideanSpace.single i 1))≤1) :
    (∏i, 2*a i)≤volume.real (coordinateVisibilityBody p) := by
  have hh : volume.real (orthogonalCoordinates R '' (univ.pi (fun i => Icc (-a i) (a i)))) ≤
      volume.real (coordinateVisibilityBody p) :=
    measureReal_mono (orthogonal_box_subset_visibility p R a ha hn hp)
      (coordinateVisibilityBody_compact p hcont).measure_lt_top.ne
  have he : volume (orthogonalCoordinates R '' (univ.pi (fun i => Icc (-a i) (a i)))) =
      ∏i, ENNReal.ofReal (2*a i) := by
    change volume ((orthogonalCoordinates R).toContinuousLinearMap.toLinearMap '' _) = _
    rw [Measure.addHaar_image_linearMap volume (orthogonalCoordinates R).toContinuousLinearMap.toLinearMap,
      show |(orthogonalCoordinates R).toContinuousLinearMap.toLinearMap.det|=1 from
        orthogonalCoordinates_abs_det R]
    simp only [ENNReal.ofReal_one,one_mul,volume_pi,Measure.pi_pi,Real.volume_Icc]
    congr 1
    funext i
    congr 1
    ring
  have hae (i) : (ENNReal.ofReal (2*a i)).toReal=2*a i :=
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (ha i))
  simpa only [Measure.real,he,ENNReal.toReal_prod,hae] using hh

/-- A low-area unit direction forces a long box in the actual visibility
body. The transverse exponent is n in ambient dimension n+1. -/
theorem visibility_volume_lower_of_low_direction {n : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin (n+1)))) (hcont : Continuous p)
    (C : ℝ) (_hC : 0≤C) (hupper : ∀v, p v≤C*‖v‖)
    (u : EuclideanSpace ℝ (Fin (n+1))) (hu : ‖u‖=1) (hpu : p u≤1) :
    (1/((n+1:ℕ):ℝ)) * (1/(((n+1:ℕ):ℝ)*max 1 C))^n ≤
      volume.real (coordinateVisibilityBody p) := by
  obtain ⟨R,hR⟩ := exists_axis_isometry (0 : Fin (n+1)) u hu
  let N : ℝ := (n+1:ℕ)
  let A : ℝ := max 1 C
  let r : ℝ := 1/(2*N)
  have hN : 0<N := by dsimp [N]; positivity
  have hA1 : 1≤A := le_max_left _ _
  have hCA : C≤A := le_max_right _ _
  have hA : 0<A := lt_of_lt_of_le zero_lt_one hA1
  have hr : 0<r := by dsimp [r]; positivity
  have hrad : r/A≤r := (div_le_iff₀ hA).mpr (by nlinarith)
  have hprod : r/A*C≤r := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hA).mpr (mul_le_mul_of_nonneg_left hCA hr.le)
  let a : Fin (n+1) → ℝ := Fin.cons r (fun _ => r/A)
  have ha (i) : 0≤a i := by
    refine Fin.cases hr.le (fun _ => div_nonneg hr.le hA.le) i
  have har (i) : a i≤r := by
    refine Fin.cases le_rfl (fun _ => hrad) i
  have hp (i) : a i*p (R (EuclideanSpace.single i 1))≤r := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change r*p (R (EuclideanSpace.single 0 1))≤r
      rw [hR]
      simpa using mul_le_mul_of_nonneg_left hpu hr.le
    · change r/A*p (R (EuclideanSpace.single j.succ 1))≤r
      have hh := hupper (R (EuclideanSpace.single j.succ 1))
      simp only [R.norm_map,PiLp.norm_single,norm_one,mul_one] at hh
      exact (mul_le_mul_of_nonneg_left hh (div_nonneg hr.le hA.le)).trans hprod
  have hsum : (∑_i : Fin (n+1), r)≤1 := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    change N*r≤1
    have he : N*r=(1:ℝ)/2 := by dsimp [r]; field_simp
    rw [he]
    norm_num
  have hh := orthogonal_box_visibility_volume_lower p hcont R a ha
    ((Finset.sum_le_sum (fun i _ => har i)).trans hsum)
    ((Finset.sum_le_sum (fun i _ => hp i)).trans hsum)
  have hr2 : 2*r=1/N := by dsimp [r]; ring
  have hra : 2*(r/A)=1/(N*A) := by dsimp [r]; ring
  simpa only [Fin.prod_univ_succ,a,Fin.cons_zero,Fin.cons_succ,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,hr2,hra,N,A] using hh

/-- High visibility supplies norm domination, rather than assuming it as an
interface. The threshold retains the exact ambient-minus-one exponent. -/
theorem norm_le_seminorm_of_small_visibility_body {n : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin (n+1)))) (hcont : Continuous p)
    (C : ℝ) (hC : 0≤C) (hupper : ∀v, p v≤C*‖v‖)
    (hsmall : volume.real (coordinateVisibilityBody p) <
      (1/((n+1:ℕ):ℝ)) * (1/(((n+1:ℕ):ℝ)*max 1 C))^n) :
    ∀v, ‖v‖≤p v := by
  intro v
  by_cases hv : v=0
  · simp [hv]
  have hn : 0<‖v‖ := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖=1 := by
    simp [u,norm_smul,hn.ne']
  have hp : 1<p u := by
    by_contra h
    exact (not_le_of_gt hsmall) (visibility_volume_lower_of_low_direction p hcont C hC hupper
      u hu (le_of_not_gt h))
  have he : p u=‖v‖⁻¹*p v := by
    simp only [u,map_smul_eq_mul,Real.norm_eq_abs,abs_inv,abs_of_pos hn]
  rw [he] at hp
  have hh := (lt_inv_mul_iff₀ hn).mp hp
  simpa using hh.le

end KakeyaTwoScale
#print axioms KakeyaTwoScale.orthogonal_box_subset_visibility
#print axioms KakeyaTwoScale.orthogonal_box_visibility_volume_lower

#print axioms KakeyaTwoScale.visibility_volume_lower_of_low_direction

#print axioms KakeyaTwoScale.norm_le_seminorm_of_small_visibility_body
