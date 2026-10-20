module
public import KakeyaTwoScale.FrozenGeometryState

@[expose] public section

open Set Metric Classical
noncomputable section
namespace KakeyaTwoScale
namespace FrozenGeometryState
variable {n k : ℕ} {T C O : Type}

/-- A genuine next-stage tag is chosen on the incoming variety using an
actual incidence point. The bound controls the whole occupied cube. -/
theorem exists_successor_tags
    (W : FrozenGeometryState n k T C O) (Y₀ : Finset T) (cube : T→C)
    (tube : T→Fin k→O) (Q : C→Set (EuclideanSpace ℝ (Fin n)))
    (δ A K : ℝ) (hk : 0<k) (hW : W.Valid Y₀ cube tube Q δ)
    (V : W.Grain→Set (EuclideanSpace ℝ (Fin n)))
    (hcapture : ∀ y∈W.tuples, ∀ j,
      W.geometry δ j (W.parent y j) ⊆ thickening (K*δ) (V (W.grain (cube y))))
    (center : C→EuclideanSpace ℝ (Fin n))
    (hdiam : ∀ q∈W.tuples.image cube, ∀ x∈Q q, dist x (center q)≤A*δ) :
    ∃ tag : C→EuclideanSpace ℝ (Fin n),
      (∀ q∈W.tuples.image cube, tag q∈V (W.grain q)) ∧
      (∀ q∈W.tuples.image cube, ∀ x∈Q q, dist x (tag q)<(2*A+K)*δ) := by
  classical
  have hex (q) (hq : q∈W.tuples.image cube) :
      ∃ z∈V (W.grain q), ∀ x∈Q q, dist x z<(2*A+K)*δ := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨x,hxQ,hx⟩ := hW.2.2.2.2.1 y hy ⟨0,hk⟩
    obtain ⟨z,hz,hxz⟩ := mem_thickening_iff.mp (hcapture y hy ⟨0,hk⟩ hx)
    refine ⟨z,hz,?_⟩
    intro w hw
    have hwc := hdiam _ hq w hw
    have hxc := hdiam _ hq x hxQ
    have hdist := dist_triangle w (center (cube y)) x
    rw [dist_comm (center (cube y)) x] at hdist
    have hdist2 := dist_triangle w x z
    linarith
  choose witness hvar hnear using hex
  refine ⟨fun q=>if h:q∈W.tuples.image cube then witness q h else 0,?_,?_⟩
  · intro q hq
    simpa only [dite_eq_left hq] using hvar q hq
  · intro q hq x hx
    simpa only [dite_eq_left hq] using hnear q hq x hx

end FrozenGeometryState
end KakeyaTwoScale
set_option pp.fullNames true
#print axioms KakeyaTwoScale.FrozenGeometryState.exists_successor_tags
