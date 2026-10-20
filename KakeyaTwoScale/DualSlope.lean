module
public import KakeyaTwoScale.KatzTaoProjection

@[expose] public section

namespace KakeyaTwoScale

/-- Explicit rational dual slope. Its pole is tracked separately. -/
def dualNumerator (a p s r : ℚ) : ℚ := -(r-s)+a*s*(r-p)
def dualDenominator (a p s r : ℚ) : ℚ := r-s+a*(r-p)
def dualSlope (a p s r : ℚ) : ℚ := dualNumerator a p s r / dualDenominator a p s r

def verticalNu (a p : ℚ) (v : ArithmeticPoint × ArithmeticPoint) : ℚ :=
  a*arithmeticProjection p v.1 + arithmeticProjection (-1) v.2

/-- Rational dual-projection identity, with both excluded denominators
explicit. The only geometric input is the actual vertical-pair equation. -/
theorem dual_projection_identity (a p s r : ℚ) (hrs : r ≠ s)
    (hd : dualDenominator a p s r ≠ 0) (v : ArithmeticPoint × ArithmeticPoint)
    (hv : arithmeticProjection s v.1 = arithmeticProjection s v.2) :
    verticalNu a p v =
      (a-a*(r-p)/(r-s))*arithmeticProjection r v.1 +
      (1+a*(r-p)/(r-s))*arithmeticProjection (dualSlope a p s r) v.2 := by
  have hden : r-s ≠ 0 := sub_ne_zero.mpr hrs
  have he : dualDenominator a p s r = r-s+a*(r-p) := rfl
  dsimp [verticalNu, arithmeticProjection] at *
  unfold dualSlope
  field_simp
  dsimp [dualNumerator, dualDenominator] at *
  linear_combination a*(r-p)*(r-s+a*(r-p))*hv

/-- The distinguished difference slope is avoided by the dual map under the
proper, distinct slope hypotheses used by the source. -/
theorem dualSlope_proper (a p s r : ℚ) (ha : a ≠ 0) (hs : s ≠ -1)
    (hrp : r ≠ p) (hd : dualDenominator a p s r ≠ 0) :
    dualSlope a p s r ≠ -1 := by
  intro h
  have he := (div_eq_iff hd).mp h
  change dualNumerator a p s r = -1*dualDenominator a p s r at he
  have hz : a*(s+1)*(r-p) = 0 := by
    dsimp [dualNumerator, dualDenominator] at he
    linear_combination he
  have hs1 : s+1 ≠ 0 := by intro h; apply hs; linarith
  exact (mul_ne_zero (mul_ne_zero ha hs1) (sub_ne_zero.mpr hrp)) hz

theorem dualSlope_ne_vertical (a p s r : ℚ) (hs : s ≠ -1) (hrs : r ≠ s)
    (hd : dualDenominator a p s r ≠ 0) : dualSlope a p s r ≠ s := by
  intro h
  have he := (div_eq_iff hd).mp h
  change dualNumerator a p s r = s*dualDenominator a p s r at he
  have hz : (s+1)*(r-s) = 0 := by
    dsimp [dualNumerator, dualDenominator] at he
    linear_combination -he
  have hs1 : s+1 ≠ 0 := by intro h; apply hs; linarith
  exact (mul_ne_zero hs1 (sub_ne_zero.mpr hrs)) hz

/-- A dual pair of projections really determines nu on the vertical family. -/
theorem dual_projections_determine_nu (a p s r : ℚ) (hrs : r ≠ s)
    (hd : dualDenominator a p s r ≠ 0) (v w : ArithmeticPoint × ArithmeticPoint)
    (hv : arithmeticProjection s v.1 = arithmeticProjection s v.2)
    (hw : arithmeticProjection s w.1 = arithmeticProjection s w.2)
    (h1 : arithmeticProjection r v.1 = arithmeticProjection r w.1)
    (h2 : arithmeticProjection (dualSlope a p s r) v.2 = arithmeticProjection (dualSlope a p s r) w.2) :
    verticalNu a p v = verticalNu a p w := by
  rw [dual_projection_identity a p s r hrs hd v hv,
    dual_projection_identity a p s r hrs hd w hw, h1,h2]

/-- Source nu is the general vertical functional with a=1-lambda. -/
theorem cornerNu_eq_verticalNu (p r3 r4 : ℚ) :
    cornerNu p r3 r4 = verticalNu (1-cornerCoefficient p r3 r4) p := rfl

/-- Distinct source slopes give the nonzero coefficient required by the
finite dual-exception construction. -/
theorem cornerNu_coefficient_ne_zero (p r3 r4 : ℚ) (h4p : r4 ≠ p) (h43 : r4 ≠ r3) :
    1-cornerCoefficient p r3 r4 ≠ 0 := by
  intro hz
  have he : (r3-p)/(r4-p) = 1 := by
    dsimp [cornerCoefficient] at hz
    linarith
  have hn := (div_eq_iff (sub_ne_zero.mpr h4p)).mp he
  apply h43
  linarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.dual_projection_identity
#print axioms KakeyaTwoScale.dualSlope_proper
#print axioms KakeyaTwoScale.dualSlope_ne_vertical
#print axioms KakeyaTwoScale.dual_projections_determine_nu
#print axioms KakeyaTwoScale.cornerNu_eq_verticalNu

#print axioms KakeyaTwoScale.cornerNu_coefficient_ne_zero
