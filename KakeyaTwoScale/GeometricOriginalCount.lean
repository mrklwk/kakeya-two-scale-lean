module
public import KakeyaTwoScale.NestedCountCancellation

@[expose] public section

open Set Metric MeasureTheory
noncomputable section
namespace KakeyaTwoScale

/-- Exact product-of-length count from actual cylinder geometry and original separation. -/
theorem geometric_original_count (n e D R : ℕ) (C : ℝ) (hC : 0≤C) :
    ∃ K : ℝ, 0<K ∧ ∀ (r : ℕ), r≤R → ∀ (_hr : 0<r), r≤n+1 →
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
    (F.card:ℝ)≤K*(rho+delta)^r/(delta^n*((List.finRange r).map L).prod) := by
  obtain ⟨K,hK,hcount⟩ := geometric_original_count_mass n e D R C hC
  let a : ℝ := 16*(n+2:ℝ)
  refine ⟨K*(a*(C+3)/2)^n*a^(n+1),by dsimp [a]; positivity,?_⟩
  intro r hrR hr hrd h O F P hP Q hQ b c u w center L ell delta rho hell hdelta hdr hmono hscale hgeom hsep
  have hm := hcount r hrR hr hrd h O F P hP Q hQ b c u w center L ell delta rho
    hell hdelta hdr hmono hscale hgeom hsep
  have hrho : 0<rho := hdelta.trans_le hdr
  have hL (i) := (hscale i).1
  have hT : 0<(((List.finRange r).drop 1).map L).prod := by
    apply List.prod_pos
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact hL i
  have hc := nested_count_cancel n r F.card K (rho+delta) delta (L ⟨0,hr⟩)
    (((List.finRange r).drop 1).map L).prod a (C+3) hK (add_pos hrho hdelta) hdelta
    (hL _) hT (by dsimp [a]; positivity) (by linarith) hm
  have hp : ((List.finRange r).map L).prod=L ⟨0,hr⟩*(((List.finRange r).drop 1).map L).prod := by
    cases r with
    | zero => omega
    | succ r =>
      have hz : (⟨0,hr⟩ : Fin (r+1))=0 := by ext; simp
      simp only [hz,List.finRange_succ,List.map_cons,List.prod_cons,List.drop_succ_cons,List.drop_zero]
  rwa [← hp] at hc

end KakeyaTwoScale
#print axioms KakeyaTwoScale.geometric_original_count
