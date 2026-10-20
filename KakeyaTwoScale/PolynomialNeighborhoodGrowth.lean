module
public import KakeyaTwoScale.PolynomialCompactCover
public import KakeyaTwoScale.DyadicCover

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Nearby zero-set witnesses need an enlarged ball. This avoids the false
same-radius containment sometimes suppressed in informal neighborhood proofs. -/
theorem thickening_inter_ball_localize {X : Type*} [PseudoMetricSpace X]
    (Z : Set X) (a : X) (R rho : ℝ) :
    thickening rho Z ∩ ball a R ⊆ thickening rho (Z∩closedBall a (R+rho)) := by
  rintro x ⟨hx,hxR⟩
  obtain ⟨y,hy,hxy⟩ := mem_thickening_iff.mp hx
  refine mem_thickening_iff.mpr ⟨y,⟨hy,?_⟩,hxy⟩
  have ht := dist_triangle y x a
  rw [dist_comm y x] at ht
  change dist x a<R at hxR
  change dist y a≤R+rho
  linarith

/-- Uniform codimension-sensitive neighborhood growth for actual globally
regular polynomial zero sets. The constant precedes equation count, every
coefficient, center and both scales. All grid and component estimates are
constructed from the original equations; no growth or count hypothesis remains. -/
theorem uniform_regular_polynomial_neighborhood_growth (d D : ℕ) [NeZero d] :
    ∃ C : ℝ, 0<C ∧ ∀ (s : ℕ), s≤d →
      ∀ P : Fin s→MvPolynomial (Fin d) ℝ, (∀ j, (P j).totalDegree≤D) →
      (∀ x, rectangularPolynomialMap P x=0 →
        (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤) →
      ∀ (a : EuclideanSpace ℝ (Fin d)) (rho R : ℝ), 0<rho → rho≤R →
      volume (thickening rho {x | rectangularPolynomialMap P x=0} ∩ ball a R)≤
        ENNReal.ofReal (C*rho^s*R^(d-s)) := by
  let G : ℝ := 2^d*(4*(max D 1:ℕ)+5)^d*2^d
  let H : ℝ := 20*(d+2)
  let C : ℝ := G*H^d*2^d*(ballConstant d+1)
  have hB : 0≤ballConstant d := ENNReal.toReal_nonneg
  have hG : 0<G := by dsimp [G]; positivity
  have hH : 1≤H := by dsimp [H]; nlinarith [Nat.cast_nonneg (α := ℝ) d]
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro s hs P hP hreg a rho R hrho hrhoR
  have hR : 0<R := hrho.trans_le hrhoR
  let h : ℝ := rho/(d+2)
  have hdpos : 0<(d:ℝ)+2 := by positivity
  have hh : 0<h := div_pos hrho hdpos
  have hhR : h≤R+rho := by
    dsimp [h]
    apply (div_le_iff₀ hdpos).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  let Z := {x | rectangularPolynomialMap P x=0}
  obtain ⟨centers,hcover,hcard⟩ := regular_polynomial_compact_cover P hP hreg a (R+rho)
    (by positivity) h hh
  have heh : ((d:ℝ)+2)*h=rho := by dsimp [h]; field_simp
  rw [heh] at hcover
  let M := (gridLabelBank (⌈(R+rho)/h⌉₊+2)).card
  have hcard' : (centers.card:ℝ)≤G*(M:ℝ)^(d-s) := by
    have hc : (centers.card:ℝ)≤
        (2^d*(M:ℝ)^(d-s))*((4*(max D 1:ℕ)+5)^d*2^d) := by exact_mod_cast hcard
    calc
      _ ≤ _ := hc
      _ = _ := by dsimp [G]; ring
  have hM : (M:ℝ)≤H*(R/rho) := by
    have hb := gridLabelBank_card_bound h (R+rho) hh hhR
    calc
      (M:ℝ) ≤ 10*((R+rho)/h) := hb
      _ ≤ 10*((2*R)/h) := by gcongr; linarith
      _ = H*(R/rho) := by dsimp [h,H]; field_simp; ring
  have hp : (M:ℝ)^(d-s)≤H^d*(R/rho)^(d-s) := by
    have hm := pow_le_pow_left₀ (show (0:ℝ)≤M by positivity) hM (d-s)
    rw [mul_pow] at hm
    exact hm.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hH (Nat.sub_le d s)) (by positivity))
  have hcount : (centers.card:ℝ)≤G*H^d*(R/rho)^(d-s) := by
    exact hcard'.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hG.le)
  have hv := neighborhood_volume_le_cover d (Z∩closedBall a (R+rho)) centers rho hcover
  have hbconv : (centers.card:ℝ≥0∞)*ENNReal.ofReal (2*rho)^d*
      ENNReal.ofReal (Real.sqrt Real.pi^d/Real.Gamma ((d:ℝ)/2+1))=
      ENNReal.ofReal ((centers.card:ℝ)*(2*rho)^d*ballConstant d) := by
    simp only [ENNReal.ofReal_mul (by positivity : (0:ℝ)≤(centers.card:ℝ)*(2*rho)^d),
      ENNReal.ofReal_mul (by positivity : (0:ℝ)≤(centers.card:ℝ)),
      ENNReal.ofReal_pow (by positivity : (0:ℝ)≤2*rho),ENNReal.ofReal_natCast,
      ballConstant]
    rw [ENNReal.ofReal_toReal (by finiteness)]
  rw [hbconv] at hv
  have hcancel : (R/rho)^(d-s)*rho^d=rho^s*R^(d-s) := by
    have he : rho^d=rho^s*rho^(d-s) := by rw [← pow_add,Nat.add_sub_of_le hs]
    rw [div_pow,he]
    field_simp
  calc
    _ ≤ volume (thickening rho (Z∩closedBall a (R+rho))) :=
      measure_mono (thickening_inter_ball_localize Z a R rho)
    _ ≤ ENNReal.ofReal ((centers.card:ℝ)*(2*rho)^d*ballConstant d) := hv
    _ ≤ ENNReal.ofReal ((G*H^d*(R/rho)^(d-s))*(2*rho)^d*(ballConstant d+1)) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul (mul_le_mul_of_nonneg_right hcount (by positivity))
        (by linarith) hB (by positivity)
    _ = ENNReal.ofReal (C*rho^s*R^(d-s)) := by
      congr 1
      rw [mul_pow (2:ℝ) rho d]
      calc
        _ = (G*H^d*2^d*(ballConstant d+1))*((R/rho)^(d-s)*rho^d) := by ring
        _ = _ := by rw [hcancel]; dsimp [C]; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.thickening_inter_ball_localize
#print axioms KakeyaTwoScale.uniform_regular_polynomial_neighborhood_growth
