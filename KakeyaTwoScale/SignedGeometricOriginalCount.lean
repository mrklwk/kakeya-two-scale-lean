module
public import KakeyaTwoScale.GeometricOriginalCount
public import KakeyaTwoScale.CylinderOrientation

@[expose] public section

open Set Metric MeasureTheory
noncomputable section
namespace KakeyaTwoScale

/-- Sum a finite signed-coordinate partition of original identifiers. -/
theorem geometric_original_count_all_charts (n e D R : ℕ) (C : ℝ) (hC : 0≤C) :
    ∃ K : ℝ, 0<K ∧ ∀ (r : ℕ), r≤R → ∀ (_hr : 0<r), r≤n+1 →
    ∀ (O : Type*) (F : Finset O)
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
    (∀ o∈F, ‖u o‖=1 ∧
      w o∈flatCylinder (c o) (u o) ell delta ∧ dist (w o) center<C*ell ∧
      (∀ i, flatCylinder (c o) (u o) ell delta⊆flatCylinder (b o i) (u o) (L i) delta) ∧
      (∀ i, flatCylinder (b o i) (u o) (L i) delta⊆thickening rho (captureZeroSet (P i)))) →
    (∀ o∈F, ∀ p∈F, o≠p → delta/2≤dist (u o) (u p)) →
    (F.card:ℝ)≤K*(rho+delta)^r/(delta^n*((List.finRange r).map L).prod) := by
  classical
  obtain ⟨K,hK,hcount⟩ := geometric_original_count n e D R C hC
  let Code := Fin (n+1) × Bool
  refine ⟨(Fintype.card Code:ℝ)*K,by dsimp [Code]; positivity,?_⟩
  intro r hrR hr hrd O F P hP Q hQ b c u w center L ell delta rho hell hdelta hdr hmono hscale hgeom hsep
  have hchoose (o) (ho : o∈F) : ∃ code : Code,
      1/(n+2:ℝ)≤orientedDirection code.2 (u o) code.1 := by
    obtain ⟨i,hi⟩ := unit_large_coordinate (u o) (hgeom o ho).1
    by_cases hh : u o i<0
    · exact ⟨(i,true),by simpa [orientedDirection,abs_of_neg hh] using hi⟩
    · exact ⟨(i,false),by simpa [orientedDirection,abs_of_nonneg (le_of_not_gt hh)] using hi⟩
  let code (o : O) : Code := if ho : o∈F then (hchoose o ho).choose else (0,false)
  have hcode (o) (ho : o∈F) : 1/(n+2:ℝ)≤orientedDirection (code o).2 (u o) (code o).1 := by
    dsimp [code]
    rw [dite_eq_left ho]
    exact (hchoose o ho).choose_spec
  let bin (z : Code) := F.filter (fun o => code o=z)
  have hbin (z : Code) : ((bin z).card:ℝ)≤K*(rho+delta)^r/(delta^n*((List.finRange r).map L).prod) := by
    apply hcount r hrR hr hrd z.1 O (bin z) P hP Q hQ
      (fun o i => orientedCylinderBase z.2 (b o i) (u o) (L i))
      (fun o => orientedCylinderBase z.2 (c o) (u o) ell)
      (fun o => orientedDirection z.2 (u o)) w center L ell delta rho
      hell hdelta hdr hmono hscale
    · intro o ho
      obtain ⟨ho,hz⟩ := Finset.mem_filter.mp ho
      obtain ⟨hu,hw,hwb,hcontain,hcapture⟩ := hgeom o ho
      refine ⟨?_,?_,?_,hwb,?_,?_⟩
      · cases z.2 <;> simpa [orientedDirection] using hu
      · simpa only [hz] using hcode o ho
      · rwa [oriented_flatCylinder]
      · intro i
        simpa only [oriented_flatCylinder] using hcontain i
      · intro i
        simpa only [oriented_flatCylinder] using hcapture i
    · intro o ho p hp hop
      have hh := hsep o (Finset.mem_filter.mp ho).1 p (Finset.mem_filter.mp hp).1 hop
      cases z.2 <;> simpa [orientedDirection] using hh
  have hcard : (F.card:ℝ)=∑ z : Code, ((bin z).card:ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise (s := F) (t := Finset.univ)
      (f := code) (fun _ _ => Finset.mem_univ _))
  rw [hcard]
  have hs := Finset.sum_le_sum (fun z (_ : z∈(Finset.univ : Finset Code)) => hbin z)
  refine hs.trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.geometric_original_count_all_charts
