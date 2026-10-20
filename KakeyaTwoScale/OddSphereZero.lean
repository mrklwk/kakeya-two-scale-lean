module
public import HamSandwich.SphereOddDegree.BorsukUlam
public import KakeyaTwoScale.BoxHamSandwich

@[expose] public section

noncomputable section
namespace KakeyaTwoScale

/-- An odd map into a strictly lower-dimensional Euclidean space has a zero. -/
theorem coefficient_odd_sphere_zero {ι : Type*} [Fintype ι] (M : ℕ)
    (hd : M < Fintype.card ι)
    (f : CoefficientSphere ι → EuclideanSpace ℝ (Fin M))
    (hf : Continuous f) (ho : ∀ c, f (coefficientAntipode c) = -f c) :
    ∃ c, f c = 0 := by
  classical
  by_cases hM : M = 0
  · subst M
    have hi : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    let i : ι := Classical.choice hi
    refine ⟨⟨PiLp.single 2 i (1 : ℝ), by simp⟩, ?_⟩
    ext j
    exact Fin.elim0 j
  have hdim : 2 ≤ Fintype.card ι := by omega
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι = n + 2 := ⟨Fintype.card ι - 2, by omega⟩
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFinOfCardEq hn).symm
  let a : SphereOddDegree.Sphere (n+1) → CoefficientSphere ι := fun x =>
    ⟨e x.val, by rw [e.norm_map]; simp⟩
  have ha : Continuous a := by
    exact (e.continuous.comp continuous_subtype_val).subtype_mk _
  have han : ∀ x, a (-x) = coefficientAntipode (a x) := by
    intro x
    apply Subtype.ext
    exact e.map_neg x.val
  let pad : EuclideanSpace ℝ (Fin M) → EuclideanSpace ℝ (Fin (n+1)) := fun v =>
    WithLp.toLp 2 (fun j => if h : j.val < M then v ⟨j.val,h⟩ else 0)
  have hp : Continuous pad := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => ℝ)).comp
    apply continuous_pi
    intro j
    by_cases h : j.val < M
    · simpa [h] using (show Continuous (fun v : EuclideanSpace ℝ (Fin M) => v ⟨j.val,h⟩) by fun_prop)
    · simpa [h] using (continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin M) => (0:ℝ)))
  let g : C(SphereOddDegree.Sphere (n+1), EuclideanSpace ℝ (Fin (n+1))) :=
    ⟨pad ∘ f ∘ a, hp.comp (hf.comp ha)⟩
  obtain ⟨x,hx⟩ := SphereOddDegree.borsuk_ulam g
  refine ⟨a x, ?_⟩
  ext j
  have hj : j.val < n+1 := by omega
  have he := congrArg (fun v : EuclideanSpace ℝ (Fin (n+1)) => v ⟨j.val,hj⟩) hx
  change (if h : j.val < M then f (a x) ⟨j.val,h⟩ else 0) =
    (if h : j.val < M then f (a (-x)) ⟨j.val,h⟩ else 0) at he
  simp only [j.isLt, dite_true, han, ho, PiLp.neg_apply] at he
  change f (a x) j = 0
  linarith

theorem boxOddSphereZero_of_dimension (n D M : ℕ) (hd : M < (D+1)^n) :
    BoxOddSphereZero n D M := by
  intro f hf ho
  exact coefficient_odd_sphere_zero M (by simpa using hd) f hf ho
end KakeyaTwoScale
#print axioms KakeyaTwoScale.coefficient_odd_sphere_zero
#print axioms KakeyaTwoScale.boxOddSphereZero_of_dimension
