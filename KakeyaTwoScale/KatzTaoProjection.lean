module
public import KakeyaTwoScale.CornerCounting

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

abbrev ArithmeticPoint := ℚ × ℚ
abbrev ArithmeticCorner := Σ _ : ArithmeticPoint, ArithmeticPoint × ArithmeticPoint

def arithmeticProjection (r : ℚ) (z : ArithmeticPoint) : ℚ := z.1+r*z.2

theorem two_projections_injective {r s : ℚ} (hrs : r ≠ s) :
    Function.Injective (fun z : ArithmeticPoint => (arithmeticProjection r z, arithmeticProjection s z)) := by
  intro z w he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  dsimp [arithmeticProjection] at h1 h2
  have hh : (r-s)*(z.2-w.2) = 0 := by nlinarith
  have hb : z.2 = w.2 := sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hrs))
  apply Prod.ext _ hb
  rw [hb] at h1
  linarith

def arithmeticCorners (G : Finset ArithmeticPoint) (r s : ℚ) : Finset ArithmeticCorner :=
  projectionCorners G (arithmeticProjection r) (arithmeticProjection s)

def cornerMu (t : ℚ) (c : ArithmeticCorner) : ℚ :=
  arithmeticProjection t c.2.1 + arithmeticProjection (-1) c.2.2

theorem mem_arithmeticCorners (G : Finset ArithmeticPoint) (r s : ℚ) (c : ArithmeticCorner) :
    c ∈ arithmeticCorners G r s ↔
      c.1 ∈ G ∧ c.2.1 ∈ G ∧ arithmeticProjection r c.2.1 = arithmeticProjection r c.1 ∧
      c.2.2 ∈ G ∧ arithmeticProjection s c.2.2 = arithmeticProjection s c.1 := by
  simp [arithmeticCorners, projectionCorners, and_assoc]

/-- Source equations (11) and the ensuing corner parameterization, with
exact injectivity hypotheses and no generic-uniformity assumption. -/
theorem corner_first_mu_injective (G : Finset ArithmeticPoint) (r s t : ℚ) (hrs : r ≠ s)
    (hdiff : Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint)) :
    Set.InjOn (fun c : ArithmeticCorner => (c.2.1, cornerMu t c)) (↑(arithmeticCorners G r s) : Set ArithmeticCorner) := by
  intro c hc d hd he
  have hc' := (mem_arithmeticCorners G r s c).mp hc
  have hd' := (mem_arithmeticCorners G r s d).mp hd
  have hleft := congrArg Prod.fst he
  have hmu := congrArg Prod.snd he
  dsimp only at hleft hmu
  have hright : c.2.2 = d.2.2 := by
    apply hdiff hc'.2.2.2.1 hd'.2.2.2.1
    unfold cornerMu at hmu
    rw [hleft] at hmu
    exact add_left_cancel hmu
  have hmid : c.1 = d.1 := by
    apply two_projections_injective hrs
    apply Prod.ext
    · exact hc'.2.2.1.symm.trans ((congrArg (arithmeticProjection r) hleft).trans hd'.2.2.1)
    · exact hc'.2.2.2.2.symm.trans ((congrArg (arithmeticProjection s) hright).trans hd'.2.2.2.2)
  cases c with
  | mk cm cw =>
    cases d with
    | mk dm dw =>
      dsimp at hmid hleft hright
      subst dm
      have hw : cw = dw := Prod.ext hleft hright
      subst dw
      rfl

/-- Every actual mu fiber has exactly as many corners as first-wing points;
this is the cardinality equality needed before applying an SD estimate. -/
theorem corner_mu_fiber_card (G : Finset ArithmeticPoint) (r s t z : ℚ) (hrs : r ≠ s)
    (hdiff : Set.InjOn (arithmeticProjection (-1)) (↑G : Set ArithmeticPoint)) :
    (((arithmeticCorners G r s).filter (fun c => cornerMu t c = z)).image (fun c => c.2.1)).card =
      ((arithmeticCorners G r s).filter (fun c => cornerMu t c = z)).card := by
  apply Finset.card_image_iff.mpr
  intro c hc d hd he
  obtain ⟨hc, hcm⟩ := Finset.mem_filter.mp hc
  obtain ⟨hd, hdm⟩ := Finset.mem_filter.mp hd
  apply corner_first_mu_injective G r s t hrs hdiff hc hd
  exact Prod.ext he (hcm.trans hdm.symm)

/-- Source corner/vertical linear dependence (13), with its exceptional
slope r4=r1 excluded explicitly. -/
def cornerCoefficient (r1 r3 r4 : ℚ) : ℚ := (r3-r1)/(r4-r1)
def cornerNu (r1 r3 r4 : ℚ) (v : ArithmeticPoint × ArithmeticPoint) : ℚ :=
  (1-cornerCoefficient r1 r3 r4)*arithmeticProjection r1 v.1 + arithmeticProjection (-1) v.2

theorem corner_mu_nu_identity (G : Finset ArithmeticPoint) (r1 r2 r3 r4 : ℚ)
    (hr : r4 ≠ r1) {c : ArithmeticCorner} (hc : c ∈ arithmeticCorners G r1 r2) :
    cornerMu r3 c = cornerCoefficient r1 r3 r4 * arithmeticProjection r4 c.2.1 +
      cornerNu r1 r3 r4 (c.1, c.2.2) := by
  have he := (mem_arithmeticCorners G r1 r2 c).mp hc |>.2.2.1
  unfold cornerMu cornerNu
  rw [← he]
  dsimp [cornerCoefficient, arithmeticProjection]
  field_simp
  ring

/-- Holding the first projection fixed, mu-fibers and nu-fibers coincide
exactly on the actual corner set. -/
theorem corner_mu_nu_fiber_iff (G : Finset ArithmeticPoint) (r1 r2 r3 r4 : ℚ)
    (hr : r4 ≠ r1) {c d : ArithmeticCorner}
    (hc : c ∈ arithmeticCorners G r1 r2) (hd : d ∈ arithmeticCorners G r1 r2)
    (hproj : arithmeticProjection r4 c.2.1 = arithmeticProjection r4 d.2.1) :
    cornerMu r3 c = cornerMu r3 d ↔
      cornerNu r1 r3 r4 (c.1,c.2.2) = cornerNu r1 r3 r4 (d.1,d.2.2) := by
  rw [corner_mu_nu_identity G r1 r2 r3 r4 hr hc,
    corner_mu_nu_identity G r1 r2 r3 r4 hr hd, hproj]
  exact add_left_cancel_iff

end KakeyaTwoScale
#print axioms KakeyaTwoScale.two_projections_injective
#print axioms KakeyaTwoScale.corner_first_mu_injective
#print axioms KakeyaTwoScale.corner_mu_fiber_card

#print axioms KakeyaTwoScale.corner_mu_nu_identity
#print axioms KakeyaTwoScale.corner_mu_nu_fiber_iff
