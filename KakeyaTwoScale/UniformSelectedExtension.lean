module
public import KakeyaTwoScale.AffineSignGraphFibers
public import KakeyaTwoScale.OpenDomainExtrapolation

@[expose] public section

open Set MeasureTheory MvPolynomial
open OAI.Release061 OAI.Release061.SignElimination
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- A jointly semialgebraic segment relation controls its ENTIRE extrapolated
point universe. Selection and regular-fiber multiplicity are proved, and the
constant precedes all real parameters and extrapolation factors. -/
theorem uniform_semialgebraic_extension_volume {π : Type*} (n : ℕ)
    (A : Set (((π→ℝ) × (Fin n→ℝ)) × (Fin n→ℝ)))
    (hA : PolynomialSignSet (fun z => Sum.elim (Sum.elim z.1.1 z.1.2) z.2) A) :
    ∃ C : ℝ, 0<C ∧ ∃ M : ℕ, ∀ (p : π→ℝ) (T : ℝ) (E : Set (Fin n→ℝ)),
      (∀ x v, ((p,x),v)∈A → ∀ t∈Icc (0:ℝ) 1, x+(t-T) • v∈E) →
      volume {x | ∃ v, ((p,x),v)∈A}≤
        (ENNReal.ofReal (C*(max 1 |T|)^n)*M)*volume E := by
  obtain ⟨C,hC,hvol⟩ := open_regular_extension_volume n
  obtain ⟨s,D,G,Q,accept,hG,hQ,hgraph,hreg⟩ := uniform_semialgebraic_selection A hA
  refine ⟨C,hC,2^s*(4*D+1)^n+1,?_⟩
  intro p T E hE
  obtain ⟨U,hU,hUnull,hGU⟩ := hreg p
  let B : Set (Fin n→ℝ) := {x | ∃ v, ((p,x),v)∈A}
  have hAp := hA.polynomial_preimage
    (fun z : (Fin n→ℝ) × (Fin n→ℝ) => ((p,z.1),z.2))
    (Sum.elim (Sum.elim (fun i => MvPolynomial.C (p i)) (fun i => X (Sum.inl i)))
      (fun i => X (Sum.inr i)))
    (d := fun z : (Fin n→ℝ) × (Fin n→ℝ) => Sum.elim z.1 z.2)
    (by intro z i; rcases i with (i|i)|i <;> simp)
  have hB : PolynomialSignSet id B := polynomialSignSet_projection_finite (c := id) hAp
  let V := interior B∩U
  have hV : IsOpen V := isOpen_interior.inter hU
  have hVB : V⊆B := fun x hx => interior_subset hx.1
  have hnull : volume (B\V)=0 := by
    apply measure_mono_null _ (measure_union_null (semialgebraic_diff_interior_null B hB) hUnull)
    intro x hx
    by_cases hi : x∈interior B
    · exact Or.inr (fun hu => hx.2 ⟨hi,hu⟩)
    · exact Or.inl ⟨hx.1,hi⟩
  have heq : volume V=volume B := measure_eq_measure_of_null_sdiff hVB hnull
  let F : (Fin n→ℝ)→(Fin n→ℝ) := fun x => x-T • G p x
  have hGV : ContDiffOn ℝ 1 (G p) V := hGU.mono inter_subset_right
  have hFV : ContDiffOn ℝ 1 F V := contDiffOn_id.sub (hGV.const_smul T)
  have hidentity (x) (_hx : x∈V) : F x+T • G p x=x := by dsimp [F]; module
  have hfun (t : ℝ) : (fun x => F x+t • G p x)=(fun x => x+(t-T) • G p x) := by
    funext x; dsimp [F]; module
  have hfiber (t : ℝ) (z : Fin n→ℝ) :
      Set.encard {x : Fin n→ℝ | x∈V ∧ F x+t • G p x=z ∧
        (fderiv ℝ (fun x => F x+t • G p x) x).det≠0}≤(2^s*(4*D+1)^n+1 : ℕ) := by
    have hh := sign_graph_open_affine_fiber_encard_le (G p) V hV hGV
      (Q p) (hQ p) accept (fun x v => eq_comm.trans (hgraph p x v)) (t-T) z
    convert hh using 1
    congr 1
    ext x
    rw [hfun t]
    simp only [mem_ofPred_eq]
    rw [congrFun (hfun t) x]
  have hh := hvol F (G p) V hV hFV hGV 0 1 T (by norm_num) hidentity
    (2^s*(4*D+1)^n+1) (fun t _ z => hfiber t z)
  have hsweep : differentiableLineSweep F (G p) V 0 1 ⊆ E ×ˢ Icc (0:ℝ) 1 := by
    rintro _ ⟨⟨x,t⟩,⟨hx,ht⟩,rfl⟩
    refine ⟨?_,by simpa using ht⟩
    change F x+t • G p x∈E
    rw [congrFun (hfun t) x]
    exact hE x (G p x) (hG p x (hVB hx)) t (by simpa using ht)
  have hmeasure : (volume.prod volume) (differentiableLineSweep F (G p) V 0 1)≤volume E := by
    have hm := measure_mono (μ := volume.prod volume) hsweep
    simpa only [Measure.prod_prod,Real.volume_Icc,sub_zero,ENNReal.ofReal_one,mul_one] using hm
  simp only [sub_zero,div_one,ENNReal.ofReal_one,mul_one,heq] at hh
  exact hh.trans (mul_le_mul le_rfl hmeasure zero_le zero_le)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.uniform_semialgebraic_extension_volume
