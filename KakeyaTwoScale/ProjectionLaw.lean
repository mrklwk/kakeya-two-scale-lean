module
public import KakeyaTwoScale.FiberEntropy

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

def slopeSupport (G : Finset (ℤ × ℤ)) : Finset ℤ := G.image Prod.snd

def slopeFiber (G : Finset (ℤ × ℤ)) (v : ℤ) : Finset (ℤ × ℤ) := G.filter (fun z => z.2 = v)

def slopeMass (G : Finset (ℤ × ℤ)) (v : ℤ) : ℝ := (slopeFiber G v).card

theorem slopeFiber_nonempty {G : Finset (ℤ × ℤ)} {v : ℤ} (hv : v ∈ slopeSupport G) :
    (slopeFiber G v).Nonempty := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
  exact ⟨z, Finset.mem_filter.mpr ⟨hz, rfl⟩⟩

theorem slopeMass_pos (G : Finset (ℤ × ℤ)) :
    ∀ v ∈ slopeSupport G, 0 < slopeMass G v := by
  intro v hv
  unfold slopeMass
  exact_mod_cast (slopeFiber_nonempty hv).card_pos

def jointFiberLaw (G : Finset (ℤ × ℤ)) (p : ℝ) (z : ℤ × ℤ) : ℝ :=
  fiberLaw (slopeSupport G) (slopeMass G) p z.2 / slopeMass G z.2

/-- Every actual slope fiber has the prescribed normalized probability. -/
theorem jointFiberLaw_marginal (G : Finset (ℤ × ℤ)) (p : ℝ)
    {v : ℤ} (hv : v ∈ slopeSupport G) :
    ∑ z ∈ slopeFiber G v, jointFiberLaw G p z = fiberLaw (slopeSupport G) (slopeMass G) p v := by
  have hm := slopeMass_pos G v hv
  calc
    _ = ∑ _z ∈ slopeFiber G v, fiberLaw (slopeSupport G) (slopeMass G) p v / slopeMass G v := by
      apply Finset.sum_congr rfl
      intro z hz
      simp only [jointFiberLaw, (Finset.mem_filter.mp hz).2]
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      change slopeMass G v * (_ / slopeMass G v) = _
      field_simp

theorem jointFiberLaw_sum (G : Finset (ℤ × ℤ)) (hG : G.Nonempty) (p : ℝ) :
    ∑ z ∈ G, jointFiberLaw G p z = 1 := by
  have hmap : ∀ z ∈ G, z.2 ∈ slopeSupport G := fun z hz => Finset.mem_image.mpr ⟨z,hz,rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  change (∑ v ∈ slopeSupport G, ∑ z ∈ slopeFiber G v, jointFiberLaw G p z) = _
  rw [Finset.sum_congr rfl (fun v hv => jointFiberLaw_marginal G p hv)]
  exact fiberLaw_sum _ _ p (hG.image _) (slopeMass_pos G)

theorem jointFiberLaw_pos (G : Finset (ℤ × ℤ)) (hG : G.Nonempty) (p : ℝ)
    {z : ℤ × ℤ} (hz : z ∈ G) : 0 < jointFiberLaw G p z := by
  have hv : z.2 ∈ slopeSupport G := Finset.mem_image.mpr ⟨z,hz,rfl⟩
  exact div_pos (fiberLaw_pos _ _ p (hG.image _) (slopeMass_pos G) hv) (slopeMass_pos G _ hv)

/-- The source's conditional-uniform entropy is explicitly computed on each
actual fiber. Together with the joint marginal theorem this is its genuine law. -/
theorem source_fiber_conditional_identity (G : Finset (ℤ × ℤ)) (hG : G.Nonempty) :
    finiteEntropy (slopeSupport G) (fiberLaw (slopeSupport G) (slopeMass G) (252/373)) +
      ((625/373:ℝ)-1) * ∑ v ∈ slopeSupport G,
        fiberLaw (slopeSupport G) (slopeMass G) (252/373) v *
          finiteEntropy (slopeFiber G v) (fun _ => (slopeMass G v)⁻¹) =
      Real.log (fiberPartition (slopeSupport G) (slopeMass G) (252/373)) := by
  have he (v) (hv : v ∈ slopeSupport G) :
      finiteEntropy (slopeFiber G v) (fun _ => (slopeMass G v)⁻¹) = Real.log (slopeMass G v) :=
    finiteEntropy_uniform _ (slopeFiber_nonempty hv)
  simp_rw [Finset.sum_congr rfl (fun v hv => congrArg
    (fun x => fiberLaw (slopeSupport G) (slopeMass G) (252/373) v*x) (he v hv))]
  exact source_fiber_entropy_identity _ _ (hG.image _) (slopeMass_pos G)
/-- Push forward a finite law by summing its actual fibers. -/
def finitePushLaw {A B : Type*} [DecidableEq B] (S : Finset A) (q : A → ℝ) (f : A → B) (y : B) : ℝ :=
  ∑ x ∈ S.filter (fun x => f x = y), q x

theorem finitePushLaw_sum {A B : Type*} [DecidableEq B] (S : Finset A) (q : A → ℝ) (f : A → B) :
    ∑ y ∈ S.image f, finitePushLaw S q f y = ∑ x ∈ S, q x := by
  have hmap : ∀ x ∈ S, f x ∈ S.image f := fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩
  exact Finset.sum_fiberwise_of_maps_to hmap q

theorem finitePushLaw_nonneg {A B : Type*} [DecidableEq B] (S : Finset A) (q : A → ℝ) (f : A → B)
    (hq : ∀ x ∈ S, 0 ≤ q x) (y : B) : 0 ≤ finitePushLaw S q f y :=
  Finset.sum_nonneg (fun x hx => hq x (Finset.mem_filter.mp hx).1)

/-- Every actual rational projection of the constructed joint law obeys its
support bound. No projection entropy bound is assumed. -/
theorem rational_projection_entropy_bound (G : Finset (ℤ × ℤ)) (hG : G.Nonempty)
    (p : ℝ) (r : ℚ) :
    finiteEntropy (G.image (fun z => (z.1:ℚ)+r*z.2))
      (finitePushLaw G (jointFiberLaw G p) (fun z => (z.1:ℚ)+r*z.2)) ≤
      Real.log (G.image (fun z => (z.1:ℚ)+r*z.2)).card := by
  apply finiteEntropy_le_log_card
  · intro y hy
    exact finitePushLaw_nonneg _ _ _ (fun z hz => (jointFiberLaw_pos G hG p hz).le) y
  · exact (finitePushLaw_sum G (jointFiberLaw G p)
      (fun z : ℤ × ℤ => (z.1:ℚ)+r*z.2)).trans (jointFiberLaw_sum G hG p)

/-- Conditional probabilities on every nonempty actual fiber are uniform. -/
theorem jointFiberLaw_conditional (G : Finset (ℤ × ℤ)) (hG : G.Nonempty) (p : ℝ)
    {v : ℤ} (hv : v ∈ slopeSupport G) {z : ℤ × ℤ} (hz : z ∈ slopeFiber G v) :
    jointFiberLaw G p z / fiberLaw (slopeSupport G) (slopeMass G) p v = (slopeMass G v)⁻¹ := by
  have hq := fiberLaw_pos (slopeSupport G) (slopeMass G) p (hG.image _) (slopeMass_pos G) hv
  have hm := slopeMass_pos G v hv
  rw [jointFiberLaw, (Finset.mem_filter.mp hz).2]
  field_simp

/-- Pair-fiber cardinality is exactly the source's number of intercepts. -/
theorem slopeFiber_intercepts_card (G : Finset (ℤ × ℤ)) (v : ℤ) :
    ((slopeFiber G v).image Prod.fst).card = (slopeFiber G v).card := by
  apply Finset.card_image_iff.mpr
  intro z hz w hw he
  exact Prod.ext he ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hw).2.symm)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.jointFiberLaw_marginal
#print axioms KakeyaTwoScale.jointFiberLaw_sum
#print axioms KakeyaTwoScale.source_fiber_conditional_identity

#print axioms KakeyaTwoScale.rational_projection_entropy_bound
#print axioms KakeyaTwoScale.jointFiberLaw_conditional

#print axioms KakeyaTwoScale.slopeFiber_intercepts_card
