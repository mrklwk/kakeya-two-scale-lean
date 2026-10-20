module
public import KakeyaTwoScale.WeightedHeavyCubes
public import KakeyaTwoScale.NonlinearTupleSelection

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Selecting whole cubes keeps the original weight on each selected cube,
and contributes zero elsewhere. No geometric alternative is assumed. -/
theorem whole_cube_selection_mass {T Q : Type*} [DecidableEq Q]
    (Y : Finset T) (cube : T → Q) (cubes G : Finset Q)
    (hG : G ⊆ cubes) {p : ℝ} (hp : 0 < p) :
    tupleCubeMass (Y.filter fun y => cube y ∈ G) cube cubes p =
      ∑ q ∈ G, (ParentLevel.capacity Y cube q : ℝ)^p := by
  classical
  have hf (q : Q) :
      ParentLevel.capacity (Y.filter fun y => cube y ∈ G) cube q =
        if q ∈ G then ParentLevel.capacity Y cube q else 0 := by
    by_cases hq : q ∈ G
    · simp only [ite_eq_left hq, ParentLevel.capacity]
      rw [cube_selection_full_fiber Y cube G hq]
    · simp only [ite_eq_right hq, ParentLevel.capacity]
      have he : (Y.filter fun y => cube y ∈ G).filter (fun y => cube y=q) = ∅ := by
        ext y
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hy hEq
        exact hq (hEq ▸ hy.2)
      rw [he, Finset.card_empty]
  unfold tupleCubeMass
  simp only [hf, Nat.cast_ite, Nat.cast_zero, ite_pow, Real.zero_rpow hp.ne']
  rw [← Finset.sum_filter]
  congr 1
  ext q
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hG h,h⟩⟩

/-- Complementary whole-cube selections conserve the actual nonlinear mass
exactly, for every positive exponent (concavity is unnecessary). -/
theorem whole_cube_selection_complement_mass {T Q : Type*} [DecidableEq Q]
    (Y : Finset T) (cube : T → Q) (cubes G : Finset Q)
    (hG : G ⊆ cubes) {p : ℝ} (hp : 0 < p) :
    tupleCubeMass (Y.filter fun y => cube y ∈ G) cube cubes p +
      tupleCubeMass (Y.filter fun y => cube y ∈ cubes \ G) cube cubes p =
      tupleCubeMass Y cube cubes p := by
  rw [whole_cube_selection_mass Y cube cubes G hG hp,
    whole_cube_selection_mass Y cube cubes (cubes \ G) Finset.sdiff_subset hp]
  change _ = ∑ q ∈ cubes, (ParentLevel.capacity Y cube q : ℝ)^p
  have hd : Disjoint G (cubes \ G) := by
    apply Finset.disjoint_left.mpr
    intro q hq ht
    exact (Finset.mem_sdiff.mp ht).2 hq
  rw [← Finset.sum_union hd, Finset.union_sdiff_of_subset hG]

/-- At least one of the two literal whole-fiber selections retains half the
mass; this is an algebraic dichotomy, not a geometric split theorem. -/
theorem whole_cube_selection_half {T Q : Type*} [DecidableEq Q]
    (Y : Finset T) (cube : T → Q) (cubes G : Finset Q)
    (hG : G ⊆ cubes) {p : ℝ} (hp : 0 < p) :
    tupleCubeMass Y cube cubes p / 2 ≤
      tupleCubeMass (Y.filter fun y => cube y ∈ G) cube cubes p ∨
    tupleCubeMass Y cube cubes p / 2 ≤
      tupleCubeMass (Y.filter fun y => cube y ∈ cubes \ G) cube cubes p := by
  have he := whole_cube_selection_complement_mass Y cube cubes G hG hp
  by_cases h : tupleCubeMass Y cube cubes p / 2 ≤
      tupleCubeMass (Y.filter fun y => cube y ∈ G) cube cubes p
  · exact Or.inl h
  · exact Or.inr (by linarith)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.whole_cube_selection_mass
#print axioms KakeyaTwoScale.whole_cube_selection_complement_mass
#print axioms KakeyaTwoScale.whole_cube_selection_half
