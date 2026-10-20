module
public import KakeyaTwoScale.CylinderContainmentFormula
public import KakeyaTwoScale.PrescribedCylinderFat

@[expose] public section

open Set MvPolynomial
open OAI.Release061 OAI.Release061.SignElimination
noncomputable section
namespace KakeyaTwoScale

/-- Fixed-format formula for the entire prescribed Fat union. -/
def prescribedFatFormula {d : ℕ} (a L w : ℝ) (E : Set (Fin d→ℝ)) (x : Fin d→ℝ) : Prop :=
  ∃ q : (Fin d⊕Fin d)→ℝ,
    (∑ j, (q (Sum.inr j))^2)=1 ∧
    (∀ y, flatCylinderFormula (fun j => q (Sum.inl j)) (fun j => q (Sum.inr j)) y L w → y∈E) ∧
    flatCylinderFormula (fun j => q (Sum.inl j)+((1-a)*L/2)*q (Sum.inr j))
      (fun j => q (Sum.inr j)) x (a*L) (a*w)

theorem euclidean_unit_iff_sum_sq {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) :
    ‖u‖=1 ↔ (∑ j, (u j)^2)=1 := by
  rw [← EuclideanSpace.real_norm_sq_eq]
  constructor
  · intro h; rw [h]; norm_num
  · intro h; nlinarith [norm_nonneg u]

theorem prescribedFatFormula_geometry {d : ℕ} (a L w : ℝ) (E : Set (Fin d→ℝ))
    (x : EuclideanSpace ℝ (Fin d)) :
    prescribedFatFormula a L w E x.ofLp ↔ x∈prescribedCylinderFat a L w (WithLp.ofLp ⁻¹' E) := by
  constructor
  · rintro ⟨q,hunit,hsub,hx⟩
    let b : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun j => q (Sum.inl j))
    let u : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun j => q (Sum.inr j))
    refine ⟨b,u,(euclidean_unit_iff_sum_sq u).mpr hunit,?_,?_⟩
    · intro y hy
      exact hsub y.ofLp ((flatCylinderFormula_geometry b u y L w).mpr hy)
    · exact (flatCylinderFormula_geometry (b+((1-a)*L/2) • u) u x (a*L) (a*w)).mp hx
  · rintro ⟨b,u,hu,hsub,hx⟩
    refine ⟨Sum.elim b.ofLp u.ofLp,(euclidean_unit_iff_sum_sq u).mp hu,?_,?_⟩
    · intro y hy
      exact hsub ((flatCylinderFormula_geometry b u (WithLp.toLp 2 y) L w).mp hy)
    · exact (flatCylinderFormula_geometry (b+((1-a)*L/2) • u) u x (a*L) (a*w)).mpr hx

/-- Joint semialgebraicity of the actual prescribed Fat operation. All source
set parameters and geometric scalars remain free during quantifier elimination. -/
theorem prescribedFatFormula_sign {X ι π : Type*} {d : ℕ}
    (c : X→ι→ℝ) (p : X→π→ℝ) (x : X→Fin d→ℝ) (a L w : X→ℝ)
    (S : Set ((π→ℝ) × (Fin d→ℝ)))
    (hS : PolynomialSignSet (fun z => Sum.elim z.1 z.2) S)
    (hp : ∀ j, PolynomialScalar c (fun z => p z j))
    (hx : ∀ j, PolynomialScalar c (fun z => x z j))
    (ha : PolynomialScalar c a) (hL : PolynomialScalar c L) (hw : PolynomialScalar c w) :
    PolynomialSignSet c {z | prescribedFatFormula (a z) (L z) (w z) {y | (p z,y)∈S} (x z)} := by
  let Y := X × ((Fin d⊕Fin d)→ℝ)
  let c' : Y → ι⊕(Fin d⊕Fin d)→ℝ := fun z => Sum.elim (c z.1) z.2
  have lift {f : X→ℝ} (hf : PolynomialScalar c f) : PolynomialScalar c' (fun z => f z.1) :=
    hf.coordinate_preimage Prod.fst Sum.inl (by intros; rfl)
  let b : Y→Fin d→ℝ := fun z j => z.2 (Sum.inl j)
  let u : Y→Fin d→ℝ := fun z j => z.2 (Sum.inr j)
  have hb (j) : PolynomialScalar c' (fun z => b z j) :=
    PolynomialScalar.coordinate (Sum.inr (Sum.inl j))
  have hu (j) : PolynomialScalar c' (fun z => u z j) :=
    PolynomialScalar.coordinate (Sum.inr (Sum.inr j))
  have hunit : PolynomialSignSet c' {z | (∑ j, (u z j)^2)=1} := by
    have hs := PolynomialScalar.sum Finset.univ _ (fun j _ => (hu j).pow 2)
    simpa only [sub_eq_zero] using (hs.sub (PolynomialScalar.const 1)).eq_zero
  have hsub := cylinder_containment_sign c' (fun z => p z.1) b u
    (fun z => L z.1) (fun z => w z.1) S hS (fun j => lift (hp j)) hb hu (lift hL) (lift hw)
  have hscale : PolynomialScalar c' (fun z => (1-a z.1)*L z.1/2) := by
    simpa only [div_eq_mul_inv,one_mul] using
      (((PolynomialScalar.const 1).sub (lift ha)).mul (lift hL)).mul (PolynomialScalar.const (1/2))
  have hdil := flatCylinderFormula_sign c'
    (fun z j => b z j+((1-a z.1)*L z.1/2)*u z j) u (fun z => x z.1)
    (fun z => a z.1*L z.1) (fun z => a z.1*w z.1)
    (fun j => (hb j).add (hscale.mul (hu j))) hu (fun j => lift (hx j))
    ((lift ha).mul (lift hL)) ((lift ha).mul (lift hw))
  exact polynomialSignSet_projection_finite (hunit.inter (hsub.inter hdil))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.euclidean_unit_iff_sum_sq
#print axioms KakeyaTwoScale.prescribedFatFormula_geometry
#print axioms KakeyaTwoScale.prescribedFatFormula_sign
