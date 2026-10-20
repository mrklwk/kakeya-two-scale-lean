module
public import KakeyaTwoScale.OrderedCaptureVolume

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Fixed-depth version, including empty flags only as an unused case. -/
theorem uniform_ordered_capture_depth_aux (n r e D : ℕ) (C : ℝ) (hC : 0≤C)
    (h : Fin (n+1)) :
    ∃ K : ℝ, 0<K ∧ ∀ hr : 0<r,
      ∀ (P : Fin r→Fin e→MvPolynomial (Fin (n+1)) ℝ),
      (∀ i j, (P i j).totalDegree≤D) →
      ∀ (center : EuclideanSpace ℝ (Fin (n+1))) (L : Fin r→ℝ) (rho s ell : ℝ)
        (Q : ∀ i : Fin r, Fin (i.val+1)→MvPolynomial (Fin (n+1)) ℝ),
      r≤n+1 → 0<rho → 0<ell → (∀ i, 0<L i ∧ rho≤L i/4) → Antitone L →
      (∀ i, (∀ j, (Q i j).totalDegree≤D) ∧
        (∀ x, rectangularPolynomialMap (Q i) x=0 →
          (fderiv ℝ (rectangularPolynomialMap (Q i)) x).range=⊤) ∧
        captureZeroSet (P i)={x | rectangularPolynomialMap (Q i) x=0}) →
      volume {v | ∃ a, universalEligibleLine D C h ⟨0,hr⟩
        (captureParameters P center L rho s ell) v a} * ENNReal.ofReal (ell^(n+1)) ≤
        ENNReal.ofReal (K*(rho^r*L ⟨0,hr⟩^n/
          (((List.finRange r).drop 1).map L).prod)) := by
  cases r with
  | zero => exact ⟨1,by norm_num,fun hr => (Nat.not_lt_zero _ hr).elim⟩
  | succ r =>
    obtain ⟨K,hK,M,hvol⟩ := uniform_ordered_capture_volume n r e D C hC h
    refine ⟨K*((M:ℝ)+1),by positivity,?_⟩
    intro hr P hP center L rho s ell Q hd hrho hell hscale hmono hQ
    have hv := hvol P hP center L rho s ell Q hd hrho hell hscale hmono hQ
    have hden : 0<((List.finRange r).map (fun i => L i.succ)).prod := by
      apply List.prod_pos
      intro x hx
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      exact (hscale _).1
    have hL := (hscale 0).1
    let F := rho^(r+1)*L 0^n/((List.finRange r).map (fun i => L i.succ)).prod
    have hF : 0≤F := by dsimp [F]; positivity
    have hm : (M:ℝ≥0∞)≤ENNReal.ofReal ((M:ℝ)+1) := by
      rw [← ENNReal.ofReal_natCast M]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hv' := hv.trans (mul_le_mul le_rfl hm zero_le zero_le)
    have he : ENNReal.ofReal (K*F)*ENNReal.ofReal ((M:ℝ)+1)=
        ENNReal.ofReal ((K*((M:ℝ)+1))*F) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hK.le hF)]
      congr 1
      ring
    change _≤ENNReal.ofReal (K*F)*ENNReal.ofReal ((M:ℝ)+1) at hv'
    rw [he] at hv'
    have hz : (⟨0,hr⟩ : Fin (r+1))=0 := by ext; simp
    simpa only [hz,List.finRange_succ,List.drop_succ_cons,List.drop_zero,List.map_map,
      Function.comp_def,F] using hv'

/-- The constant precedes stopping depth, chart, original equations and all
real scale data. The maximum depth is fixed before any delta-dependent input. -/
theorem uniform_ordered_capture_depth (n e D R : ℕ) (C : ℝ) (hC : 0≤C) :
    ∃ K : ℝ, 0<K ∧ ∀ (r : ℕ), r≤R → ∀ (hr : 0<r) (h : Fin (n+1)),
      ∀ (P : Fin r→Fin e→MvPolynomial (Fin (n+1)) ℝ),
      (∀ i j, (P i j).totalDegree≤D) →
      ∀ (center : EuclideanSpace ℝ (Fin (n+1))) (L : Fin r→ℝ) (rho s ell : ℝ)
        (Q : ∀ i : Fin r, Fin (i.val+1)→MvPolynomial (Fin (n+1)) ℝ),
      r≤n+1 → 0<rho → 0<ell → (∀ i, 0<L i ∧ rho≤L i/4) → Antitone L →
      (∀ i, (∀ j, (Q i j).totalDegree≤D) ∧
        (∀ x, rectangularPolynomialMap (Q i) x=0 →
          (fderiv ℝ (rectangularPolynomialMap (Q i)) x).range=⊤) ∧
        captureZeroSet (P i)={x | rectangularPolynomialMap (Q i) x=0}) →
      volume {v | ∃ a, universalEligibleLine D C h ⟨0,hr⟩
        (captureParameters P center L rho s ell) v a} * ENNReal.ofReal (ell^(n+1)) ≤
        ENNReal.ofReal (K*(rho^r*L ⟨0,hr⟩^n/
          (((List.finRange r).drop 1).map L).prod)) := by
  classical
  let B := Fin (R+1) × Fin (n+1)
  have hh (j : B) := uniform_ordered_capture_depth_aux n j.1.val e D C hC j.2
  choose K hK hvol using hh
  let total : ℝ := 1+∑ j : B, K j
  have ht : 0<total := by
    have hh := Finset.sum_nonneg (fun j (_ : j∈(Finset.univ : Finset B)) => (hK j).le)
    dsimp [total]
    linarith
  refine ⟨total,ht,?_⟩
  intro r hr hrpos h P hP center L rho s ell Q hd hrho hell hscale hmono hQ
  let j : B := (⟨r,by omega⟩,h)
  have hv := hvol j hrpos P hP center L rho s ell Q hd hrho hell hscale hmono hQ
  have hsum := Finset.single_le_sum (fun i (_ : i∈(Finset.univ : Finset B)) => (hK i).le)
    (Finset.mem_univ j)
  have hcoef : K j≤total := by dsimp [total]; linarith
  have hden : 0<(((List.finRange r).drop 1).map L).prod := by
    apply List.prod_pos
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact (hscale i).1
  have hL := (hscale ⟨0,hrpos⟩).1
  exact hv.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoef (by positivity)))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_ordered_capture_depth_aux
#print axioms KakeyaTwoScale.uniform_ordered_capture_depth
