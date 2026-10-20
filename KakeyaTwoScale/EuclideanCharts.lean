module
public import KakeyaTwoScale.DirectionNormalization
public import KakeyaTwoScale.BrushGeometry

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical NormedSpace
open scoped BigOperators

def chartSlope {n : ℕ} (i : Fin (n+1)) (u : EuclideanSpace ℝ (Fin (n+1))) : Fin n → ℝ :=
  fun j => u (i.succAbove j)/u i

/-- A deliberately nonoptimal uniform comparison from coordinate bounds. -/
theorem euclidean_norm_of_coordinate_bound {n : ℕ}
    (x : EuclideanSpace ℝ (Fin (n+1))) (D : ℝ) (hD : 0 ≤ D)
    (hx : ∀ j, |x j| ≤ D) : ‖x‖ ≤ (n+2:ℝ)*D := by
  have hh := euclidean_dist_le_sqrt_mul_sup (WithLp.ofLp x) (0:Fin (n+1) → ℝ)
  simp only [WithLp.toLp_ofLp,WithLp.toLp_zero,dist_zero_right] at hh
  have hs : ‖WithLp.ofLp x‖ ≤ D := (pi_norm_le_iff_of_nonneg hD).mpr (by simpa [Real.norm_eq_abs] using hx)
  have hroot : Real.sqrt (n+1:ℝ) ≤ n+2 := by
    have hh := Real.sq_sqrt (show (0:ℝ) ≤ n+1 by positivity)
    nlinarith [Real.sqrt_nonneg (n+1:ℝ),Nat.cast_nonneg (α:=ℝ) n]
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _))
  push_cast at hh'
  exact hh'.trans (mul_le_mul_of_nonneg_right hroot hD)

/-- Unit directions with positive chosen coordinate are controlled by their
actual graph slopes. No bounded-slope hypothesis is needed. -/
theorem angle_le_chartSlope {n : ℕ} (i : Fin (n+1))
    (u v : EuclideanSpace ℝ (Fin (n+1))) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (hui : 0 < u i) (hvi : 0 < v i) :
    InnerProductGeometry.angle u v ≤ Real.pi*(n+2:ℝ)*dist (chartSlope i u) (chartSlope i v) := by
  let x := (u i)⁻¹ • u
  let y := (v i)⁻¹ • v
  have hx : 1 ≤ ‖x‖ := by
    have hh := PiLp.norm_apply_le x i
    simpa [x,Real.norm_eq_abs,hui.ne',inv_mul_cancel₀] using hh
  have hy : 0 < ‖y‖ := by
    dsimp [y]; rw [norm_smul,hv,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hvi),mul_one]
    exact inv_pos.mpr hvi
  have hnx : normalize x=u := by
    rw [NormedSpace.normalize_smul_of_pos (inv_pos.mpr hui),NormedSpace.normalize_eq_self_of_norm_eq_one hu]
  have hny : normalize y=v := by
    rw [NormedSpace.normalize_smul_of_pos (inv_pos.mpr hvi),NormedSpace.normalize_eq_self_of_norm_eq_one hv]
  have hcoord : ∀ j, |(x-y) j| ≤ dist (chartSlope i u) (chartSlope i v) := by
    refine (Fin.forall_iff_succAbove i (P:=fun j => |(x-y) j| ≤ dist (chartSlope i u) (chartSlope i v))).mpr ?_
    constructor
    · simp [x,y,hui.ne',hvi.ne',inv_mul_cancel₀]
    · intro j
      have hh := dist_le_pi_dist (chartSlope i u) (chartSlope i v) j
      simpa only [Real.dist_eq,chartSlope,x,y,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,div_eq_inv_mul] using hh
  have hnorm := euclidean_norm_of_coordinate_bound (x-y) _ dist_nonneg hcoord
  have hdist := normalize_dist_le x y hx hy
  rw [hnx,hny,dist_eq_norm x y] at hdist
  have ha := (unit_direction_angle_bounds u v hu hv).2
  have hpi := Real.pi_pos
  nlinarith

/-- Actual graph slope separation after a positive height rescaling. -/
theorem rescaled_chartSlope_separation {n : ℕ} (i : Fin (n+1))
    (u v : EuclideanSpace ℝ (Fin (n+1))) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (hui : 0 < u i) (hvi : 0 < v i) {L r : ℝ} (hL : 0 < L)
    (hsep : r ≤ InnerProductGeometry.angle u v) :
    L*r/(Real.pi*(n+2:ℝ)) ≤ dist (L • chartSlope i u) (L • chartSlope i v) := by
  have hh := hsep.trans (angle_le_chartSlope i u v hu hv hui hvi)
  have hd : 0 < Real.pi*(n+2:ℝ) := by positivity
  rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos hL]
  apply (div_le_iff₀ hd).mpr
  have hm := mul_le_mul_of_nonneg_left hh hL.le
  nlinarith only [hm]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.euclidean_norm_of_coordinate_bound
#print axioms KakeyaTwoScale.angle_le_chartSlope
#print axioms KakeyaTwoScale.rescaled_chartSlope_separation
