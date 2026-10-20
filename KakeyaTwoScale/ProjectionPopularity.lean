module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- Actual popularity refinement using the original projection fibers.
The division-free threshold also makes sense for empty source or target. -/
def projectionPopular {J K : Type*} (S : Finset J) (T : Finset K) (f : J → K) : Finset J :=
  S.filter (fun j => S.card ≤ 2*T.card*(S.filter (fun i => f i = f j)).card)

/-- Every point retained by the explicit popularity filter has an original
fiber at least the average divided by two. -/
theorem projectionPopular_fiber_lower {J K : Type*} (S : Finset J) (T : Finset K)
    (f : J → K) {j : J} (hj : j ∈ projectionPopular S T f) :
    S.card ≤ 2*T.card*(S.filter (fun i => f i = f j)).card :=
  (Finset.mem_filter.mp hj).2

/-- Popularity deletes at most half the points, derived by summing actual
small fibers over the projection target, with no bad-mass assumption. -/
theorem projectionPopular_half {J K : Type*} (S : Finset J) (T : Finset K)
    (f : J → K) (hf : ∀ j ∈ S, f j ∈ T) :
    S.card ≤ 2*(projectionPopular S T f).card := by
  let bad := S.filter (fun j => ¬ S.card ≤ 2*T.card*(S.filter (fun i => f i = f j)).card)
  have hpartition : (projectionPopular S T f).card + bad.card = S.card := by
    exact Finset.card_filter_add_card_filter_not _
  by_cases hT : T.card = 0
  · have hS : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have := hf j hj
      simp [Finset.card_eq_zero.mp hT] at this
    simp [hS, projectionPopular]
  have hTpos : 0 < T.card := Nat.pos_of_ne_zero hT
  have hfib : ∀ t ∈ T, 2*T.card*(bad.filter (fun j => f j = t)).card ≤ S.card := by
    intro t ht
    by_cases hne : (bad.filter (fun j => f j = t)).Nonempty
    · obtain ⟨j, hj⟩ := hne
      obtain ⟨hj, hft⟩ := Finset.mem_filter.mp hj
      have hbad := (Finset.mem_filter.mp hj).2
      rw [hft] at hbad
      have hsub : bad.filter (fun j => f j = t) ⊆ S.filter (fun j => f j = t) := by
        intro i hi
        obtain ⟨hi, he⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, he⟩
      exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans (Nat.le_of_lt (Nat.lt_of_not_ge hbad))
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  have hmaps : ∀ j ∈ bad, f j ∈ T := fun j hj => hf j (Finset.mem_filter.mp hj).1
  have hsum : (∑ t ∈ T, (bad.filter (fun j => f j = t)).card) = bad.card := by
    simpa using Finset.sum_fiberwise_of_maps_to hmaps (fun _ => (1:ℕ))
  have hbound : 2*T.card*bad.card ≤ T.card*S.card := by
    calc
      _ = ∑ t ∈ T, 2*T.card*(bad.filter (fun j => f j = t)).card := by rw [← Finset.mul_sum, hsum]
      _ ≤ ∑ _t ∈ T, S.card := Finset.sum_le_sum hfib
      _ = _ := by simp
  nlinarith

/-- Refinement keeps entire projection fibers. A retained point has exactly
the same fiber in the refined set as in the original set. -/
theorem projectionPopular_fiber_eq {J K : Type*} (S : Finset J) (T : Finset K)
    (f : J → K) {j : J} (hj : j ∈ projectionPopular S T f) :
    (projectionPopular S T f).filter (fun i => f i = f j) =
      S.filter (fun i => f i = f j) := by
  ext i
  constructor
  · intro hi
    obtain ⟨hi, he⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, he⟩
  · intro hi
    obtain ⟨hi, he⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hi, ?_⟩, he⟩
    rw [he]
    exact projectionPopular_fiber_lower S T f hj

/-- The actual retained fibers, not merely original fibers, satisfy the
popularity threshold. -/
theorem projectionPopular_retained_fiber_lower {J K : Type*} (S : Finset J) (T : Finset K)
    (f : J → K) {j : J} (hj : j ∈ projectionPopular S T f) :
    S.card ≤ 2*T.card*((projectionPopular S T f).filter (fun i => f i = f j)).card := by
  rw [projectionPopular_fiber_eq S T f hj]
  exact projectionPopular_fiber_lower S T f hj

end KakeyaTwoScale
#print axioms KakeyaTwoScale.projectionPopular_fiber_lower
#print axioms KakeyaTwoScale.projectionPopular_half

#print axioms KakeyaTwoScale.projectionPopular_fiber_eq
#print axioms KakeyaTwoScale.projectionPopular_retained_fiber_lower
