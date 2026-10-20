module
public import KakeyaTwoScale.PrescribedCylinderFat
public import KakeyaTwoScale.PolynomialNeighborhoodGrowth

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Actual inner balls and polynomial growth give a volume-decay estimate.
The geometric thickness hypothesis will be discharged by actual cylinder unions. -/
theorem uniform_thick_polynomial_intersection (d D : ℕ) [NeZero d] :
    ∃ K : ℝ, 0<K ∧ ∀ (s : ℕ), s≤d →
      ∀ P : Fin s→MvPolynomial (Fin d) ℝ, (∀ j, (P j).totalDegree≤D) →
      (∀ x, rectangularPolynomialMap P x=0 →
        (fderiv ℝ (rectangularPolynomialMap P) x).range=⊤) →
      ∀ (W : Set (EuclideanSpace ℝ (Fin d))) (rho r : ℝ),
      0<rho → 0<r → rho≤2*r → volume W≠⊤ →
      (∀ x∈W, ∃ y, ball y (r/8)⊆W∩ball x r) →
      volume (thickening rho {x | rectangularPolynomialMap P x=0}∩W)≤
        ENNReal.ofReal (K*(rho/r)^s)*volume W := by
  obtain ⟨C,hC,hgrowth⟩ := uniform_regular_polynomial_neighborhood_growth d D
  let U := (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
  have hU : 0<U := ENNReal.toReal_pos
    (measure_ball_pos volume 0 (by norm_num : (0:ℝ)<1)).ne' measure_ball_lt_top.ne
  let K := C*2^d*8^d/U
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro s hs P hP hreg W rho r hrho hr hrhor hW hinner
  obtain ⟨F,_hFW,hcover,hpack⟩ := thickness_finite_cover W r hr hW hinner
  let Z := {x | rectangularPolynomialMap P x=0}
  have hupper : volume (thickening rho Z∩W)≤
      (F.card : ℝ≥0∞)*ENNReal.ofReal (C*rho^s*(2*r)^(d-s)) := by
    calc
      _ ≤ volume (⋃ a∈F, thickening rho Z∩ball a (2*r)) := measure_mono (by
        rintro x ⟨hx,hW⟩
        obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp (hcover hW)
        exact mem_iUnion₂.mpr ⟨a,ha,hx,hxa⟩)
      _ ≤ ∑ a∈F, volume (thickening rho Z∩ball a (2*r)) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _a∈F, ENNReal.ofReal (C*rho^s*(2*r)^(d-s)) :=
        Finset.sum_le_sum (fun a _ => hgrowth s hs P hP hreg a rho (2*r) hrho hrhor)
      _ = _ := by simp
  have hsmall : (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (r/8))).toReal=
      (r/8)^d*U := by
    rw [volume.addHaar_ball_of_pos 0 (by positivity : 0<r/8)]
    simp only [ENNReal.toReal_mul,finrank_euclideanSpace_fin]
    rw [ENNReal.toReal_ofReal (by positivity : 0≤(r/8)^d)]
  have hpackR : (F.card : ℝ)*(r/8)^d*U≤(volume W).toReal := by
    have hh := ENNReal.toReal_mono hW hpack
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,hsmall,mul_assoc] using hh
  have hupperR : (volume (thickening rho Z∩W)).toReal≤
      (F.card : ℝ)*(C*rho^s*(2*r)^(d-s)) := by
    have hh := ENNReal.toReal_mono (by finiteness) hupper
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal (by positivity : 0≤C*rho^s*(2*r)^(d-s))] using hh
  have hcancel : (rho/r)^s*r^d=rho^s*r^(d-s) := by
    rw [show r^d=r^s*r^(d-s) by rw [← pow_add,Nat.add_sub_of_le hs],div_pow]
    field_simp
  have hfactor : C*rho^s*(2*r)^(d-s)≤K*(rho/r)^s*((r/8)^d*U) := by
    have htwo : (2:ℝ)^(d-s)≤2^d := pow_le_pow_right₀ (by norm_num) (Nat.sub_le d s)
    calc
      _ = C*2^(d-s)*(rho/r)^s*r^d := by rw [mul_pow]; rw [mul_assoc _ _ (r^d),hcancel]; ring
      _ ≤ C*2^d*(rho/r)^s*r^d := by gcongr
      _ = _ := by dsimp [K]; rw [div_pow r 8 d]; field_simp
  have hfinalR : (volume (thickening rho Z∩W)).toReal≤K*(rho/r)^s*(volume W).toReal := by
    calc
      _ ≤ (F.card : ℝ)*(C*rho^s*(2*r)^(d-s)) := hupperR
      _ ≤ (F.card : ℝ)*(K*(rho/r)^s*((r/8)^d*U)) := mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = K*(rho/r)^s*((F.card : ℝ)*(r/8)^d*U) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpackR (by dsimp [K]; positivity)
  have hfinite : volume (thickening rho Z∩W)≠⊤ :=
    ne_top_of_le_ne_top hW (measure_mono inter_subset_right)
  have hh := ENNReal.ofReal_le_ofReal hfinalR
  rw [ENNReal.ofReal_toReal hfinite,ENNReal.ofReal_mul (by dsimp [K]; positivity),
    ENNReal.ofReal_toReal hW] at hh
  exact hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_thick_polynomial_intersection
