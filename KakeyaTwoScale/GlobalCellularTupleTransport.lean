module
public import KakeyaTwoScale.CellularCylinderSplit
public import KakeyaTwoScale.TupleLengthSelection

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

def geometricCubeCell {n : ℕ} {C : Type*} (P : MvPolynomial (Fin n) ℝ)
    (Q : C → Set (EuclideanSpace ℝ (Fin n))) (q : C) : Set (EuclideanSpace ℝ (Fin n)) :=
  connectedComponentIn (ambientPolynomialZeroSet P)ᶜ (Classical.epsilon fun x => x ∈ Q q)

theorem geometricCubeCell_eq {n : ℕ} {C : Type*} (P : MvPolynomial (Fin n) ℝ)
    (Q : C → Set (EuclideanSpace ℝ (Fin n))) (q : C)
    (hQ : IsPreconnected (Q q)) (hsub : Q q ⊆ (ambientPolynomialZeroSet P)ᶜ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Q q) :
    connectedComponentIn (ambientPolynomialZeroSet P)ᶜ x = geometricCubeCell P Q q := by
  have hc : Classical.epsilon (fun z => z ∈ Q q) ∈ Q q := Classical.epsilon_spec ⟨x,hx⟩
  exact (connectedComponentIn_eq (hQ.subset_connectedComponentIn hc hsub hx)).symm

/-- All tube families and original tuple labels are transported together.
No nonlinear retention premise appears: cube-wide cellular labels imply the
exact objective identity, while actual root pieces realize every incidence.
Only already off-wall cubes are supplied; wall removal and later localization
are separate operations. -/
theorem global_cellular_tuple_transport {n k : ℕ} {T C J : Type*}
    [DecidableEq T] [DecidableEq C]
    (P : MvPolynomial (Fin n) ℝ) (Y : Finset T) (cube : T → C)
    (cubes : Finset C) (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (tube : T → Fin k → J) (b u : J → EuclideanSpace ℝ (Fin n)) (L : J → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hu : ∀ j, ‖u j‖=1) (hL : ∀ j, δ ≤ L j)
    (hY : ∀ y ∈ Y, cube y ∈ cubes)
    (hQ : ∀ q ∈ cubes, IsPreconnected (Q q))
    (hwall : ∀ q ∈ cubes, ∀ x ∈ Q q, x ∉ cthickening (2*δ) (ambientPolynomialZeroSet P))
    (hinc : ∀ y ∈ Y, ∀ j, (Q (cube y) ∩ flatCylinder (b (tube y j)) (u (tube y j))
      (L (tube y j)) δ).Nonempty) :
    ∃ start : T → Fin k → ℝ,
      (∀ y ∈ Y, ∀ j,
        let t := tube y j
        let a := start y j
        let len := rootNext (cellularRoots P (b t) (u t) (L t)) (L t) a-a
        a ∈ insert 0 (cellularRoots P (b t) (u t) (L t)) ∧ δ ≤ len ∧
        flatCylinder (b t+a • u t) (u t) len δ ⊆ flatCylinder (b t) (u t) (L t) δ ∧
        (Q (cube y) ∩ flatCylinder (b t+a • u t) (u t) len δ).Nonempty ∧
        ∀ r ∈ Ioo a (rootNext (cellularRoots P (b t) (u t) (L t)) (L t) a),
          b t+r • u t ∈ geometricCubeCell P Q (cube y)) ∧
      ∀ p : ℝ, 0 < p →
        (∑ G ∈ cubes.image (geometricCubeCell P Q),
          tupleCubeMass (Y.filter fun y => geometricCubeCell P Q (cube y)=G) cube cubes p) =
        tupleCubeMass Y cube cubes p := by
  classical
  have hlocal : ∀ y, ∃ a : Fin k → ℝ, y ∈ Y → ∀ j,
      let t := tube y j
      let len := rootNext (cellularRoots P (b t) (u t) (L t)) (L t) (a j)-a j
      a j ∈ insert 0 (cellularRoots P (b t) (u t) (L t)) ∧ δ ≤ len ∧
      flatCylinder (b t+a j • u t) (u t) len δ ⊆ flatCylinder (b t) (u t) (L t) δ ∧
      (Q (cube y) ∩ flatCylinder (b t+a j • u t) (u t) len δ).Nonempty ∧
      ∀ r ∈ Ioo (a j) (rootNext (cellularRoots P (b t) (u t) (L t)) (L t) (a j)),
        b t+r • u t ∈ geometricCubeCell P Q (cube y) := by
    intro y
    by_cases hy : y ∈ Y
    · have hp : ∀ j : Fin k, ∃ a : ℝ,
          a ∈ insert 0 (cellularRoots P (b (tube y j)) (u (tube y j)) (L (tube y j))) ∧
          δ ≤ rootNext (cellularRoots P (b (tube y j)) (u (tube y j)) (L (tube y j))) (L (tube y j)) a-a ∧
          flatCylinder (b (tube y j)+a • u (tube y j)) (u (tube y j))
            (rootNext (cellularRoots P (b (tube y j)) (u (tube y j)) (L (tube y j))) (L (tube y j)) a-a) δ ⊆
            flatCylinder (b (tube y j)) (u (tube y j)) (L (tube y j)) δ ∧
          (Q (cube y) ∩ flatCylinder (b (tube y j)+a • u (tube y j)) (u (tube y j))
            (rootNext (cellularRoots P (b (tube y j)) (u (tube y j)) (L (tube y j))) (L (tube y j)) a-a) δ).Nonempty ∧
          ∀ r ∈ Ioo a (rootNext (cellularRoots P (b (tube y j)) (u (tube y j)) (L (tube y j))) (L (tube y j)) a),
            b (tube y j)+r • u (tube y j) ∈ geometricCubeCell P Q (cube y) := by
        intro j
        obtain ⟨x,hxQ,hxT⟩ := hinc y hy j
        obtain ⟨a,ha,hlen,hx,hparent,haxis⟩ := exists_cellular_root_piece P
          (b (tube y j)) (u (tube y j)) x (L (tube y j)) δ
          (hu _) hδ (hL _) hxT (hwall _ (hY y hy) x hxQ)
        have he := geometricCubeCell_eq P Q (cube y) (hQ _ (hY y hy))
          (fun z hz hzZ => hwall _ (hY y hy) z hz
            (mem_cthickening_of_dist_le z z (2*δ) (ambientPolynomialZeroSet P) hzZ (by simp; positivity))) hxQ
        exact ⟨a,ha,hlen,hparent,⟨x,hxQ,hx⟩,fun r hr => he ▸ haxis r hr⟩
      choose a ha using hp
      exact ⟨a,fun _ j => ha j⟩
    · exact ⟨fun _ => 0,fun h => False.elim (hy h)⟩
  choose start hstart using hlocal
  refine ⟨start,fun y hy j => hstart y hy j,?_⟩
  intro p hp
  exact cube_label_mass_eq Y cube cubes (geometricCubeCell P Q) hp

end KakeyaTwoScale
#print axioms KakeyaTwoScale.geometricCubeCell_eq
#print axioms KakeyaTwoScale.global_cellular_tuple_transport
