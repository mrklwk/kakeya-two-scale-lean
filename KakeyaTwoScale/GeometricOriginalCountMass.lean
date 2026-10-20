module
public import KakeyaTwoScale.OriginalSlopeBallPacking
public import KakeyaTwoScale.UniformOrderedCaptureDepth

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- The multiscale counting mass for a finite set of distinct originals in one
positive coordinate chart. Eligible-ball inclusion and recursive target volume
are proved from the displayed literal cylinders and regular flag. No counting
or recurrence hypothesis is an input. -/
theorem geometric_original_count_mass (n e D R : ℕ) (C : ℝ) (hC : 0≤C) :
    ∃ K : ℝ, 0<K ∧ ∀ (r : ℕ), r≤R → ∀ (hr : 0<r), r≤n+1 →
    ∀ (h : Fin (n+1)) (O : Type*) (F : Finset O)
      (P : Fin r→Fin e→MvPolynomial (Fin (n+1)) ℝ),
    (∀ i j, (P i j).totalDegree≤D) →
    ∀ (Q : ∀ i : Fin r, Fin (i.val+1)→MvPolynomial (Fin (n+1)) ℝ),
    (∀ i, (∀ j, (Q i j).totalDegree≤D) ∧
      (∀ x, rectangularPolynomialMap (Q i) x=0 →
        (fderiv ℝ (rectangularPolynomialMap (Q i)) x).range=⊤) ∧
      captureZeroSet (P i)={x | rectangularPolynomialMap (Q i) x=0}) →
    ∀ (b : O→Fin r→EuclideanSpace ℝ (Fin (n+1)))
      (c u w : O→EuclideanSpace ℝ (Fin (n+1))) (center : EuclideanSpace ℝ (Fin (n+1)))
      (L : Fin r→ℝ) (ell delta rho : ℝ),
    0<ell → 0<delta → delta≤rho → Antitone L →
    (∀ i, 0<L i ∧ L i≤1 ∧ ell≤L i ∧ 8*rho≤L i) →
    (∀ o∈F, ‖u o‖=1 ∧ 1/(n+2:ℝ)≤u o h ∧
      w o∈flatCylinder (c o) (u o) ell delta ∧ dist (w o) center<C*ell ∧
      (∀ i, flatCylinder (c o) (u o) ell delta⊆flatCylinder (b o i) (u o) (L i) delta) ∧
      (∀ i, flatCylinder (b o i) (u o) (L i) delta⊆thickening rho (captureZeroSet (P i)))) →
    (∀ o∈F, ∀ p∈F, o≠p → delta/2≤dist (u o) (u p)) →
    ((F.card:ℝ≥0∞)*ENNReal.ofReal ((2*(delta/(16*(n+2:ℝ)*(C+3))))^n))*
      ENNReal.ofReal ((L ⟨0,hr⟩/(16*(n+2:ℝ)))^(n+1)) ≤
    ENNReal.ofReal (K*((rho+delta)^r*L ⟨0,hr⟩^n/
      (((List.finRange r).drop 1).map L).prod)) := by
  classical
  obtain ⟨K,hK,hvol⟩ := uniform_ordered_capture_depth n e D R C hC
  obtain ⟨B,hB,hball⟩ := localized_eligible_direction_ball n C hC
  let bank := Finset.Icc (-(B:ℤ)) (B:ℤ)
  refine ⟨((bank.card:ℝ)+1)*K,by positivity,?_⟩
  intro r hrR hr hrd h O F P hP Q hQ b c u w center L ell delta rho hell hdelta hdr hmono hscale hgeom hsep
  let first : Fin r := ⟨0,hr⟩
  let slab := L first/(16*(n+2:ℝ))
  let E : ℤ→Set (Fin n→ℝ) := fun q => {v | ∃ a, universalEligibleLine D C h first
    (captureParameters P center L (rho+delta) ((q:ℝ)*slab) slab) v a}
  have hrho : 0<rho := hdelta.trans_le hdr
  have hL (i) := (hscale i).1
  have hslab : 0<slab := div_pos (hL first) (by positivity)
  have hcover (o) (ho : o∈F) :
      ball (chartSlope h (u o)) (delta/(16*(n+2:ℝ)*(C+3)))⊆⋃ q∈bank, E q := by
    obtain ⟨hu,hh,hw,hwb,hcontain,hcapture⟩ := hgeom o ho
    obtain ⟨q,hq,hsub⟩ := hball r e D h first P hP (b o) (c o) (u o) center (w o) L ell delta rho
      hu hh hell hdelta hrho hL (fun i => (hscale i).2.1)
      (fun i => by have hi := (hscale i).2.2.2; linarith)
      (fun i => (hscale i).2.2.1) (fun i => (hscale i).2.2.2) hcontain hw hwb hcapture
    intro v hv
    refine mem_iUnion₂.mpr ⟨q,hq,?_⟩
    refine ⟨chartIntercept h (c o-center) (u o) 0,?_⟩
    have he : (q:ℝ)*slab=(q:ℝ)*L first/(16*(n+2:ℝ)) := by dsimp [slab]; ring
    simpa only [Set.mem_ofPred_eq,E,he,slab] using hsub hv
  have hp := original_slope_ball_volume_le F h u delta (C+3) hdelta (by linarith)
    (fun o ho => (hgeom o ho).1)
    (fun o ho => (one_div_pos.mpr (by positivity : 0<(n+2:ℝ))).trans_le (hgeom o ho).2.1)
    hsep (⋃ q∈bank, E q) hcover
  have hs : volume (⋃ q∈bank, E q)≤∑ q∈bank, volume (E q) := measure_biUnion_finset_le bank E
  have hv (q : ℤ) : volume (E q)*ENNReal.ofReal (slab^(n+1))≤
      ENNReal.ofReal (K*((rho+delta)^r*L first^n/(((List.finRange r).drop 1).map L).prod)) := by
    apply hvol r hrR hr h P hP center L (rho+delta) ((q:ℝ)*slab) slab Q hrd
      (add_pos hrho hdelta) hslab _ hmono hQ
    intro i
    refine ⟨hL i,?_⟩
    have hi := (hscale i).2.2.2
    linarith
  have hh := mul_le_mul (hp.trans hs) (le_refl (ENNReal.ofReal (slab^(n+1)))) zero_le zero_le
  rw [Finset.sum_mul] at hh
  have hsum := Finset.sum_le_sum (fun q (_ : q∈bank) => hv q)
  have hbound := hh.trans hsum
  simp only [Finset.sum_const,nsmul_eq_mul] at hbound
  have hf : 0≤(rho+delta)^r*L first^n/(((List.finRange r).drop 1).map L).prod := by
    have hden : 0<(((List.finRange r).drop 1).map L).prod := by
      apply List.prod_pos
      intro x hx
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      exact hL i
    have := hL first
    positivity
  refine hbound.trans ?_
  rw [← ENNReal.ofReal_natCast bank.card,← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hkf : 0≤K*((rho+delta)^r*L first^n/(((List.finRange r).drop 1).map L).prod) := mul_nonneg hK.le hf
  dsimp only [first]
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.geometric_original_count_mass
