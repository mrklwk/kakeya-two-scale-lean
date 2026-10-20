module
public import KakeyaTwoScale.UniversalCaptureAtoms
public import KakeyaTwoScale.SelectedSemialgebraicSweep

@[expose] public section

open Set MvPolynomial
open OAI.Release061 OAI.Release061.SignElimination
noncomputable section
namespace KakeyaTwoScale

def universalCaptureNear {n r e : ℕ} (D : ℕ) (C : ℝ) (h : Fin (n+1))
    (p : CaptureParameter n r e → ℝ) (v a : Fin n → ℝ) (i : Fin r) (t : ℝ) : Prop :=
  ∃ y, universalCapturePoint D C h p v a i t y

def universalCaptureInterval {n r e : ℕ} (D : ℕ) (C : ℝ) (h : Fin (n+1))
    (p : CaptureParameter n r e → ℝ) (v a : Fin n → ℝ) (i : Fin r) (s L : ℝ) : Prop :=
  ∀ t ∈ Icc s (s+L), universalCaptureNear D C h p v a i t

def universalCaptureLevel {n r e : ℕ} (D : ℕ) (C : ℝ) (h : Fin (n+1))
    (p : CaptureParameter n r e → ℝ) (v a : Fin n → ℝ) (i : Fin r) : Prop :=
  ∃ s : ℝ, -(C+3)*p (.length i) ≤ s ∧
    s+p (.length i)/(4*(n+2:ℝ)) ≤ (C+3)*p (.length i) ∧
    universalCaptureInterval D C h p v a i s (p (.length i)/(4*(n+2:ℝ)))

/-- The actual fixed-format multilevel line relation: existential starts,
universal times, nearby zero-set witnesses, bounded slope/intercept boxes and
one fixed common outer slab. No finite population of original lines occurs. -/
def universalEligibleLine {n r e : ℕ} (D : ℕ) (C : ℝ) (h : Fin (n+1)) (outer : Fin r)
    (p : CaptureParameter n r e → ℝ) (v a : Fin n → ℝ) : Prop :=
  0 < p .radius ∧ 0 < p .slabLength ∧ (∀ i, 0 < p (.length i)) ∧
  (∀ j, (v j)^2 < (n+3:ℝ)^2) ∧
  (∀ j, (a j)^2 < ((C+3)*(n+3:ℝ)+1)^2) ∧
  (∀ i, universalCaptureLevel D C h p v a i) ∧
  universalCaptureInterval D C h p v a outer (p .slabStart) (p .slabLength)

section Generic
variable {X ι : Type*} {n r e : ℕ}
    (c : X → ι → ℝ) (D : ℕ) (C : ℝ) (h : Fin (n+1))
    (p : X → CaptureParameter n r e → ℝ) (v a : X → Fin n → ℝ)
    (hp : ∀ q, PolynomialScalar c (fun x => p x q))
    (hv : ∀ j, PolynomialScalar c (fun x => v x j))
    (ha : ∀ j, PolynomialScalar c (fun x => a x j))

include hp hv ha

theorem universalCaptureNear_sign (t : X → ℝ) (ht : PolynomialScalar c t) (i : Fin r) :
    PolynomialSignSet c {x | universalCaptureNear D C h (p x) (v x) (a x) i (t x)} := by
  unfold universalCaptureNear
  apply polynomialSignSet_projection_finite (c := c)
    (A := {z : X × (Fin (n+1) → ℝ) | universalCapturePoint D C h (p z.1) (v z.1) (a z.1) i (t z.1) z.2})
  apply universalCapturePoint_sign (fun z : X × (Fin (n+1) → ℝ) => Sum.elim (c z.1) z.2)
    D C h (fun z => p z.1) (fun z => v z.1) (fun z => a z.1) (fun z => t z.1) Prod.snd
  · intro q; exact (hp q).coordinate_preimage Prod.fst Sum.inl (by intros; rfl)
  · intro j; exact (hv j).coordinate_preimage Prod.fst Sum.inl (by intros; rfl)
  · intro j; exact (ha j).coordinate_preimage Prod.fst Sum.inl (by intros; rfl)
  · exact ht.coordinate_preimage Prod.fst Sum.inl (by intros; rfl)
  · intro k; exact PolynomialScalar.coordinate (Sum.inr k)

theorem universalCaptureInterval_sign (s L : X → ℝ)
    (hs : PolynomialScalar c s) (hL : PolynomialScalar c L) (i : Fin r) :
    PolynomialSignSet c {x | universalCaptureInterval D C h (p x) (v x) (a x) i (s x) (L x)} := by
  let c' : X × ℝ → Option ι → ℝ := fun z o => o.elim z.2 (c z.1)
  have lift {f : X → ℝ} (hf : PolynomialScalar c f) : PolynomialScalar c' (fun z => f z.1) :=
    hf.coordinate_preimage Prod.fst Option.some (by intros; rfl)
  have ht : PolynomialScalar c' Prod.snd := PolynomialScalar.coordinate none
  have hnear := universalCaptureNear_sign c' D C h (fun z => p z.1) (fun z => v z.1)
    (fun z => a z.1) (fun q => lift (hp q)) (fun j => lift (hv j))
    (fun j => lift (ha j)) Prod.snd ht i
  have hguard := ((lift hs).le ht).inter (ht.le ((lift hs).add (lift hL)))
  unfold universalCaptureInterval
  apply polynomialSignSet_forall_real
  convert hguard.compl.union hnear using 1
  ext z
  simp only [mem_ofPred_eq,mem_union,mem_compl_iff,mem_inter_iff,mem_Icc]
  tauto

theorem universalCaptureLevel_sign (i : Fin r) :
    PolynomialSignSet c {x | universalCaptureLevel D C h (p x) (v x) (a x) i} := by
  let c' : X × ℝ → Option ι → ℝ := fun z o => o.elim z.2 (c z.1)
  have lift {f : X → ℝ} (hf : PolynomialScalar c f) : PolynomialScalar c' (fun z => f z.1) :=
    hf.coordinate_preimage Prod.fst Option.some (by intros; rfl)
  have hs : PolynomialScalar c' Prod.snd := PolynomialScalar.coordinate none
  have hlen : PolynomialScalar c' (fun z => p z.1 (.length i)/(4*(n+2:ℝ))) := by
    simpa only [div_eq_mul_inv] using (lift (hp (.length i))).mul (PolynomialScalar.const _)
  have hint := universalCaptureInterval_sign c' D C h (fun z => p z.1) (fun z => v z.1)
    (fun z => a z.1) (fun q => lift (hp q)) (fun j => lift (hv j))
    (fun j => lift (ha j)) Prod.snd _ hs hlen i
  unfold universalCaptureLevel
  exact polynomialSignSet_projection_one (c := c)
    ((((PolynomialScalar.const (-(C+3))).mul (lift (hp (.length i)))).le hs).inter
    (((hs.add hlen).le ((PolynomialScalar.const (C+3)).mul (lift (hp (.length i))))).inter hint))

end Generic

/-- Quantifier elimination proves the whole jointly parameterized geometric
relation semialgebraic, with coefficients, lengths and slab values still free. -/
theorem universalEligibleLine_sign (n r e D : ℕ) (C : ℝ) (h : Fin (n+1)) (outer : Fin r) :
    PolynomialSignSet
      (fun z : (((CaptureParameter n r e → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ)) =>
        Sum.elim (Sum.elim z.1.1 z.1.2) z.2)
      {z | universalEligibleLine D C h outer z.1.1 z.1.2 z.2} := by
  let X := ((CaptureParameter n r e → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ)
  let c : X → ((CaptureParameter n r e ⊕ Fin n) ⊕ Fin n) → ℝ :=
    fun z => Sum.elim (Sum.elim z.1.1 z.1.2) z.2
  have hp (q) : PolynomialScalar c (fun z => z.1.1 q) :=
    PolynomialScalar.coordinate (Sum.inl (Sum.inl q))
  have hv (j) : PolynomialScalar c (fun z => z.1.2 j) :=
    PolynomialScalar.coordinate (Sum.inl (Sum.inr j))
  have ha (j) : PolynomialScalar c (fun z => z.2 j) :=
    PolynomialScalar.coordinate (Sum.inr j)
  have hr := (PolynomialScalar.const (c := c) 0).lt (hp .radius)
  have hl := (PolynomialScalar.const (c := c) 0).lt (hp .slabLength)
  have hls := PolynomialSignSet.forall_finite _
    (fun i => (PolynomialScalar.const (c := c) 0).lt (hp (.length i)))
  have hvs := PolynomialSignSet.forall_finite _
    (fun j => ((hv j).pow 2).lt (PolynomialScalar.const ((n+3:ℝ)^2)))
  have has := PolynomialSignSet.forall_finite _
    (fun j => ((ha j).pow 2).lt (PolynomialScalar.const (((C+3)*(n+3:ℝ)+1)^2)))
  have hlevels := PolynomialSignSet.forall_finite _
    (universalCaptureLevel_sign c D C h (fun z => z.1.1) (fun z => z.1.2) Prod.snd hp hv ha)
  have hslab := universalCaptureInterval_sign c D C h (fun z => z.1.1) (fun z => z.1.2)
    Prod.snd hp hv ha (fun z => z.1.1 .slabStart) (fun z => z.1.1 .slabLength)
    (hp .slabStart) (hp .slabLength) outer
  exact hr.inter (hl.inter (hls.inter (hvs.inter (has.inter (hlevels.inter hslab)))))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.universalEligibleLine_sign
