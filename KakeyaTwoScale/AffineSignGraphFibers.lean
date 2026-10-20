module
public import KakeyaTwoScale.OpenSignGraphFibers

@[expose] public section

open Set MvPolynomial
noncomputable section
namespace KakeyaTwoScale

theorem affine_graph_fiber_iff {n : ℕ} (G : (Fin n→ℝ)→(Fin n→ℝ))
    (c : ℝ) (hc : c≠0) (x z : Fin n→ℝ) :
    x+c • G x=z ↔ G x=c⁻¹ • z-c⁻¹ • x := by
  constructor
  · intro he
    funext j
    have hj := congrFun he j
    change x j+c*G x j=z j at hj
    change G x j=c⁻¹*z j-c⁻¹*x j
    field_simp
    linarith
  · intro he
    funext j
    have hj := congrFun he j
    change G x j=c⁻¹*z j-c⁻¹*x j at hj
    field_simp at hj
    change x j+c*G x j=z j
    linarith

/-- Uniform regular fibers for identity plus a scalar multiple of the selected
map. At scalar zero the map is exactly the identity; no singular rescaling of
its derivative is used. -/
theorem sign_graph_open_affine_fiber_encard_le {n s D : ℕ}
    (G : (Fin n→ℝ)→(Fin n→ℝ)) (U : Set (Fin n→ℝ)) (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) (P : Fin s→MvPolynomial (Fin n ⊕ Fin n) ℝ)
    (hP : ∀ j, (P j).totalDegree≤D) (accept : (Fin s→SignType)→Prop)
    (hgraph : ∀ x w, G x=w ↔ accept (fun j => SignType.sign (eval (Sum.elim w x) (P j))))
    (c : ℝ) (z : Fin n→ℝ) :
    Set.encard {x : Fin n→ℝ | x∈U ∧ x+c • G x=z ∧
      (fderiv ℝ (fun x => x+c • G x) x).det≠0}≤(2^s*(4*D+1)^n+1 : ℕ) := by
  by_cases hc : c=0
  · calc
      _ ≤ ({z} : Set (Fin n→ℝ)).encard := Set.encard_le_encard (by
        intro x hx; simpa [hc] using hx.2.1)
      _ = 1 := Set.encard_singleton _
      _ ≤ (2^s*(4*D+1)^n+1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 (2^s*(4*D+1)^n)
  · have hb := sign_description_open_regular_fiber_encard_le (fun x => x+c • G x) U
      (fun x hx => contDiffAt_id.add (((hG x hx).contDiffAt (hU.mem_nhds hx)).const_smul c))
      (fun j => sliceGraphPolynomial (P j) c⁻¹ (c⁻¹ • z))
      (fun j => (sliceGraphPolynomial_degree _ _ _).trans (hP j)) accept z (by
        intro x
        simp_rw [sliceGraphPolynomial_eval]
        rw [← hgraph]
        exact affine_graph_fiber_iff G c hc x z)
    exact hb.trans (by exact_mod_cast Nat.le_succ (2^s*(4*D+1)^n))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.affine_graph_fiber_iff
#print axioms KakeyaTwoScale.sign_graph_open_affine_fiber_encard_le
