module
public import KakeyaTwoScale.PolynomialSignQuantifiers
public import KakeyaTwoScale.FlatCylinderThickness

@[expose] public section

open Set MvPolynomial
open OAI.Release061 OAI.Release061.SignElimination
noncomputable section
namespace KakeyaTwoScale

/-- A literal polynomial formula for flat open cylinders in coordinates. -/
def flatCylinderFormula {d : ℕ} (b u x : Fin d→ℝ) (L r : ℝ) : Prop :=
  0<r ∧ ∃ t : ℝ, 0<t ∧ t<L ∧
    (∑ j, u j*(x j-(b j+t*u j)))=0 ∧
    (∑ j, (x j-(b j+t*u j))^2)<r^2

theorem flatCylinderFormula_geometry {d : ℕ} (b u x : EuclideanSpace ℝ (Fin d))
    (L r : ℝ) : flatCylinderFormula b.ofLp u.ofLp x.ofLp L r ↔ x∈flatCylinder b u L r := by
  have hi (t : ℝ) : (∑ j, u j*(x j-(b j+t*u j)))=inner ℝ u (x-(b+t • u)) := by
    simp [PiLp.inner_apply,mul_comm]
  have hn (t : ℝ) : (∑ j, (x j-(b j+t*u j))^2)=‖x-(b+t • u)‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  constructor
  · rintro ⟨hr,t,ht0,htL,he,hsq⟩
    exact ⟨t,ht0,htL,(hi t) ▸ he,(sq_lt_sq₀ (norm_nonneg _) hr.le).mp ((hn t) ▸ hsq)⟩
  · rintro ⟨t,ht0,htL,he,hnorm⟩
    have hr : 0<r := (norm_nonneg _).trans_lt hnorm
    exact ⟨hr,t,ht0,htL,(hi t).symm ▸ he,(hn t).symm ▸ (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr hnorm⟩

/-- Joint cylinder membership is polynomial-sign whenever all its coordinate
inputs are polynomial scalars. -/
theorem flatCylinderFormula_sign {X ι : Type*} {d : ℕ}
    (c : X→ι→ℝ) (b u x : X→Fin d→ℝ) (L r : X→ℝ)
    (hb : ∀ j, PolynomialScalar c (fun z => b z j))
    (hu : ∀ j, PolynomialScalar c (fun z => u z j))
    (hx : ∀ j, PolynomialScalar c (fun z => x z j))
    (hL : PolynomialScalar c L) (hr : PolynomialScalar c r) :
    PolynomialSignSet c {z | flatCylinderFormula (b z) (u z) (x z) (L z) (r z)} := by
  let c' : X × ℝ→Option ι→ℝ := fun z o => o.elim z.2 (c z.1)
  have lift {f : X→ℝ} (hf : PolynomialScalar c f) : PolynomialScalar c' (fun z => f z.1) :=
    hf.coordinate_preimage Prod.fst Option.some (by intros; rfl)
  have ht : PolynomialScalar c' Prod.snd := PolynomialScalar.coordinate none
  have he (j) : PolynomialScalar c' (fun z => x z.1 j-(b z.1 j+z.2*u z.1 j)) :=
    (lift (hx j)).sub ((lift (hb j)).add (ht.mul (lift (hu j))))
  have hi : PolynomialScalar c' (fun z => ∑ j, u z.1 j*(x z.1 j-(b z.1 j+z.2*u z.1 j))) := by
    exact PolynomialScalar.sum Finset.univ _ (fun j _ => (lift (hu j)).mul (he j))
  have hn : PolynomialScalar c' (fun z => ∑ j, (x z.1 j-(b z.1 j+z.2*u z.1 j))^2) :=
    PolynomialScalar.sum Finset.univ _ (fun j _ => (he j).pow 2)
  have htime := ((PolynomialScalar.const (c := c') 0).lt ht).inter
    ((ht.lt (lift hL)).inter (hi.eq_zero.inter (hn.lt ((lift hr).pow 2))))
  exact ((PolynomialScalar.const (c := c) 0).lt hr).inter
    (polynomialSignSet_projection_one htime)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.flatCylinderFormula_geometry
#print axioms KakeyaTwoScale.flatCylinderFormula_sign
