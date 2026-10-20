module
public import KakeyaTwoScale.CoordinateConstraintRank

@[expose] public section

open Set
open scoped ContDiff
noncomputable section
namespace KakeyaTwoScale

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {d : ℕ}

/-- Simultaneous regularity of all coordinate-grid intersections, including
intersections with several grid walls. -/
def coordinateGridRegular (f : E→F) (g : Fin d→E→ℝ) (c : F)
    (h : ℝ) (theta : Fin d→ℝ) (S : Finset (Fin d)) : Prop :=
  ∀ J : Finset (Fin d), J⊆S → ∀ z : Fin d→ℤ, ∀ x : E,
    f x=c → (∀ j∈J, g j x=theta j+z j*h) →
    (fderiv ℝ (coordinateConstraint f g J) x).range=⊤

/-- Construct all grid offsets by finite induction and countable relative
Sard avoidance. The result is joint transversality, not separate regularity of
each coordinate on the original fiber. -/
theorem exists_transverse_coordinate_grid (f : E→F) (g : Fin d→E→ℝ) (c : F)
    (hf : ContDiff ℝ ∞ f) (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hreg : ∀ x, f x=c → (fderiv ℝ f x).range=⊤)
    (h : ℝ) (hh : 0<h) (S : Finset (Fin d)) :
    ∃ theta : Fin d→ℝ, (∀ j∈S, theta j∈Ioo 0 h) ∧
      coordinateGridRegular f g c h theta S := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0,by simp,?_⟩
    intro J hJ z x hx _
    have he : J=∅ := Finset.subset_empty.mp hJ
    subst J
    apply LinearMap.range_eq_top.mpr
    intro y
    obtain ⟨v,hv⟩ := LinearMap.range_eq_top.mp (hreg x hx) y.1
    refine ⟨v,?_⟩
    change fderiv ℝ (coordinateConstraint f g ∅) x v=y
    rw [coordinateConstraint_fderiv f g hf hg]
    apply Prod.ext hv
    funext j
    exact False.elim (Finset.notMem_empty j.val j.property)
  | @insert i S hi ih =>
    obtain ⟨theta,htheta,hgrid⟩ := ih
    let I := {J : Finset (Fin d) // J⊆S} × (Fin d→ℤ)
    let codomain : I→Type := fun p => F×(p.1.val→ℝ)
    let maps : ∀ p : I, E→codomain p := fun p => coordinateConstraint f g p.1.val
    let levels : ∀ p : I, codomain p := fun p =>
      (c,fun j => theta j+p.2 j*h)
    have hmaps (p : I) : ContDiff ℝ ∞ (maps p) := coordinateConstraint_contDiff f g hf hg _
    have hmapsreg (p : I) (x : E) (hx : maps p x=levels p) :
        (fderiv ℝ (maps p) x).range=⊤ := by
      apply hgrid p.1.val p.1.property p.2 x (congrArg Prod.fst hx)
      intro j hj
      exact congrArg (fun v : codomain p => v.2 ⟨j,hj⟩) hx
    obtain ⟨a,ha,htrans⟩ := countable_fibers_transverse_grid_offset codomain maps (g i) levels
      (fun p _ _ => (hmaps p).contDiffAt) (hg i) hmapsreg h hh
    let theta' := Function.update theta i a
    have hsame (j) (hj : j∈S) : theta' j=theta j := by
      apply Function.update_of_ne
      intro he; exact hi (he ▸ hj)
    refine ⟨theta',?_,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa [theta'] using ha
      · rw [hsame j hj]; exact htheta j hj
    · intro J hJ z x hx hxg
      by_cases hiJ : i∈J
      · let K := J.erase i
        have hKS : K⊆S := by
          intro j hj
          have hjJ := (Finset.mem_erase.mp hj).2
          exact (Finset.mem_insert.mp (hJ hjJ)).resolve_left (Finset.mem_erase.mp hj).1
        let p : I := (⟨K,hKS⟩,z)
        have hxold : maps p x=levels p := by
          apply Prod.ext hx
          funext j
          have hjJ := (Finset.mem_erase.mp j.property).2
          have he := hxg j hjJ
          rw [hsame j (hKS j.property)] at he
          exact he
        have hxi : g i x=a+z i*h := by simpa [theta'] using hxg i hiJ
        obtain ⟨v,hv,hvi⟩ := htrans p (z i) x hxold hxi
        have hr := coordinateConstraint_insert_range f g hf hg K i x (hmapsreg p x hxold) v hv hvi
        have he : insert i K=J := Finset.insert_erase hiJ
        exact (congrArg (fun L : Finset (Fin d) =>
          (fderiv ℝ (coordinateConstraint f g L) x).range=⊤) he).mp hr
      · have hJS : J⊆S := by
          intro j hj
          rcases Finset.mem_insert.mp (hJ hj) with he | hjS
          · exact False.elim (hiJ (he ▸ hj))
          · exact hjS
        apply hgrid J hJS z x hx
        intro j hj
        have he := hxg j hj
        rw [hsame j (hJS hj)] at he
        exact he

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_transverse_coordinate_grid
