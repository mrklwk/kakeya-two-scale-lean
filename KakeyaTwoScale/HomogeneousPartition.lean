module
public import KakeyaTwoScale.FiniteSubtypeEntropy
public import KakeyaTwoScale.HomogeneousEntropyApplication

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- The source's optimized finite partition bound, now with its homogeneous
entropy premise discharged. One fixed finite rational slope family works
for every nonempty finite integer graph. -/
theorem finite_homogeneous_partition_625_373 :
    ∃ R : Finset ℚ, R.Nonempty ∧ ∀ G : Finset (ℤ × ℤ), G.Nonempty →
      ∃ r ∈ R, fiberPartition (slopeSupport G) (slopeMass G) (252/373) ≤
        ((G.image (integerProjection r)).card:ℝ)^(625/373:ℝ) := by
  obtain ⟨R,hR,hEnt⟩ := finite_homogeneous_entropy_625_373
  refine ⟨R,hR,?_⟩
  intro G hG
  let q0 := jointFiberLaw G (252/373)
  let q : G → ℝ := fun z => q0 z.val
  let f : G → ArithmeticPoint := fun z => ((z.val.1:ℚ),(z.val.2:ℚ))
  have hq (z : G) : 0 ≤ q z := (jointFiberLaw_pos G hG (252/373) z.property).le
  have hsum : ∑ z, q z = 1 := by
    change (∑ z : G, q0 z.val) = 1
    rw [← Finset.sum_subtype G (by intro z; rfl) q0]
    exact jointFiberLaw_sum G hG (252/373)
  have hinj : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    apply Prod.ext
    · have hh := congrArg Prod.fst h
      dsimp [f] at hh
      exact_mod_cast hh
    · have hh := congrArg Prod.snd h
      dsimp [f] at hh
      exact_mod_cast hh
  have hJ : pushEntropy q f = finiteEntropy G q0 := by
    unfold pushEntropy
    rw [finiteEntropy_push_injective Finset.univ q f hinj.injOn]
    exact finiteEntropy_subtype G q0
  have hV : pushEntropy q (Prod.snd ∘ f) =
      finiteEntropy (slopeSupport G) (fiberLaw (slopeSupport G) (slopeMass G) (252/373)) := by
    have he : Prod.snd ∘ f = (fun z : ℤ => (z:ℚ)) ∘ (fun z : G => z.val.2) := rfl
    rw [he,pushEntropy_injective_post q (fun z : G => z.val.2) (fun z : ℤ => (z:ℚ))
      (fun a b h => by change (a:ℚ) = (b:ℚ) at h; exact_mod_cast h)]
    change pushEntropy (fun z : G => q0 z.val) (fun z : G => Prod.snd z.val) = _
    rw [pushEntropy_subtype]
    apply finiteEntropy_congr
    intro y hy
    exact jointFiberLaw_marginal G (252/373) hy
  have hproj (r : ℚ) : pushEntropy q (arithmeticProjection r ∘ f) =
      finiteEntropy (G.image (integerProjection r)) (finitePushLaw G q0 (integerProjection r)) :=
    pushEntropy_subtype G q0 (integerProjection r)
  obtain ⟨r,hr,he⟩ := Finset.exists_mem_eq_sup' hR (fun r => pushEntropy q (arithmeticProjection r ∘ f))
  have hh := hEnt G q hq hsum f
  rw [hJ,hV,he,hproj] at hh
  refine ⟨r,hr,?_⟩
  exact source_partition_bound_of_homogeneous_entropy G hG r hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finite_homogeneous_partition_625_373
