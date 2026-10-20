module
public import KakeyaTwoScale.FiniteVectorEncoding

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- A common positive integer multiplier clears a specified finite collection
of rational denominators. Its size is unrestricted and may depend on the set. -/
theorem finite_clear_denominators (S : Finset ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∀ q ∈ S, ∃ z : ℤ, (z:ℚ) = (d:ℚ)*q := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert q S hq ih =>
    obtain ⟨d,hd,h⟩ := ih
    refine ⟨d*q.den,Nat.mul_pos hd q.den_pos,?_⟩
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · refine ⟨(d:ℤ)*a.num,?_⟩
      push_cast
      have hrat : (a.num:ℚ) = a*(a.den:ℚ) :=
        (div_eq_iff (by exact_mod_cast a.den_ne_zero)).mp (Rat.num_div_den a)
      rw [hrat]
      ring
    · obtain ⟨z,hz⟩ := h a ha
      refine ⟨(q.den:ℤ)*z,?_⟩
      push_cast
      rw [hz]
      ring

def integerProjection (r : ℚ) (v : ℤ × ℤ) : ℚ := (v.1:ℚ)+r*(v.2:ℚ)

/-- Integer realization of a rational finite set by one common dilation.
Both coordinates use the same positive factor, hence every rational
projection, not just a selected list, commutes with the realization. -/
theorem exists_integer_pair_encoder (G : Finset ArithmeticPoint) :
    ∃ d : ℕ, 0 < d ∧ ∃ e : ArithmeticPoint → ℤ × ℤ,
      (∀ v ∈ G, ((e v).1:ℚ) = (d:ℚ)*v.1 ∧ ((e v).2:ℚ) = (d:ℚ)*v.2) ∧
      Set.InjOn e (↑G : Set ArithmeticPoint) ∧
      (∀ v ∈ G, ∀ w ∈ G, (e v).2 = (e w).2 ↔ v.2 = w.2) ∧
      (∀ r : ℚ, ∀ v ∈ G, integerProjection r (e v) = (d:ℚ)*arithmeticProjection r v) := by
  let S := G.image Prod.fst ∪ G.image Prod.snd
  obtain ⟨d,hd,h⟩ := finite_clear_denominators S
  have hz : ∀ q : ℚ, ∃ z : ℤ, q ∈ S → (z:ℚ) = (d:ℚ)*q := by
    intro q
    by_cases hq : q ∈ S
    · obtain ⟨z,hz⟩ := h q hq
      exact ⟨z,fun _ => hz⟩
    · exact ⟨0,fun h' => False.elim (hq h')⟩
  choose z hz using hz
  let e := fun v : ArithmeticPoint => (z v.1,z v.2)
  have he (v) (hv : v ∈ G) : ((e v).1:ℚ) = (d:ℚ)*v.1 ∧ ((e v).2:ℚ) = (d:ℚ)*v.2 := by
    exact ⟨hz _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)),
      hz _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩))⟩
  have hdq : (d:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  refine ⟨d,hd,e,he,?_,?_,?_⟩
  · intro v hv w hw hEq
    apply Prod.ext
    · apply mul_left_cancel₀ hdq
      rw [← (he v hv).1,← (he w hw).1,hEq]
    · apply mul_left_cancel₀ hdq
      rw [← (he v hv).2,← (he w hw).2,hEq]
  · intro v hv w hw
    constructor
    · intro hEq
      apply mul_left_cancel₀ hdq
      rw [← (he v hv).2,← (he w hw).2,hEq]
    · intro hEq
      change z v.2 = z w.2
      rw [hEq]
  · intro r v hv
    simp only [integerProjection,arithmeticProjection,(he v hv).1,(he v hv).2]
    ring

/-- Simultaneous integer encoding of finite rational vector pairs. It
preserves the joint set, the vertical coordinate, and every selected rational
projection by equality equivalences; consequently individual fibers survive. -/
theorem exists_integer_vector_encoder {n : ℕ}
    (G : Finset ((Fin n → ℚ) × (Fin n → ℚ))) (R : Finset ℚ) :
    ∃ e : ((Fin n → ℚ) × (Fin n → ℚ)) → ℤ × ℤ,
      Set.InjOn e (↑G : Set _) ∧
      (∀ v ∈ G, ∀ w ∈ G, (e v).2 = (e w).2 ↔ v.2 = w.2) ∧
      (∀ r ∈ R, ∀ v ∈ G, ∀ w ∈ G,
        integerProjection r (e v) = integerProjection r (e w) ↔
          vectorProjection r v = vectorProjection r w) := by
  let S := G.image Prod.fst ∪ G.image Prod.snd ∪ R.biUnion (fun r => G.image (vectorProjection r))
  obtain ⟨f,hf⟩ := exists_finite_vector_encoder n S
  have hfst (v) (hv : v ∈ G) : v.1 ∈ S :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩))
  have hsnd (v) (hv : v ∈ G) : v.2 ∈ S :=
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩))
  have hproj (r) (hr : r ∈ R) (v) (hv : v ∈ G) : vectorProjection r v ∈ S :=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,hr,Finset.mem_image.mpr ⟨v,hv,rfl⟩⟩)
  let g := encodeVectorPair f
  obtain ⟨d,hd,e,_,hei,hev,hep⟩ := exists_integer_pair_encoder (G.image g)
  have hg (v) (hv : v ∈ G) : g v ∈ G.image g := Finset.mem_image.mpr ⟨v,hv,rfl⟩
  have hdq : (d:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  refine ⟨e ∘ g,?_,?_,?_⟩
  · intro v hv w hw he
    have h := hei (hg v hv) (hg w hw) he
    exact Prod.ext (hf (hfst v hv) (hfst w hw) (congrArg Prod.fst h))
      (hf (hsnd v hv) (hsnd w hw) (congrArg Prod.snd h))
  · intro v hv w hw
    rw [Function.comp_apply,Function.comp_apply,hev _ (hg v hv) _ (hg w hw)]
    change f v.2 = f w.2 ↔ v.2 = w.2
    exact ⟨hf (hsnd v hv) (hsnd w hw),congrArg f⟩
  · intro r hr v hv w hw
    rw [Function.comp_apply,Function.comp_apply,hep r _ (hg v hv),hep r _ (hg w hw),
      encoder_projection,encoder_projection]
    constructor
    · intro h
      exact hf (hproj r hr v hv) (hproj r hr w hw) (mul_left_cancel₀ hdq h)
    · intro h
      rw [h]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_clear_denominators
#print axioms KakeyaTwoScale.exists_integer_pair_encoder
#print axioms KakeyaTwoScale.exists_integer_vector_encoder
