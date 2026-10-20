module
public import KakeyaTwoScale.ActualBufferedCubeForest
public import KakeyaTwoScale.WholeCubeTupleSelection

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

/-- Extend occupied-cube weights to a global unit floor without changing any
original weight on the actual occupied root. -/
def bufferedTupleWeight {T C : Type*} [DecidableEq C]
    (Y : Finset T) (cube : T → C) (p : ℝ) (q : C) : ℝ :=
  max 1 ((ParentLevel.capacity Y cube q:ℝ)^p)

/-- The constructed geometric forest retains literal original tuple fibers
and their nonlinear mass. The unit-floor extension is eliminated on the root. -/
theorem actual_buffered_forest_tuple_retention {b c J s depth : ℕ} {T C : Type}
    [DecidableEq C]
    (P : Fin c → MvPolynomial (Fin b ⊕ Fin c) ℝ) (D : ℕ → ℕ)
    (S : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c)))
    (Y : Finset T) (cube : T → C) (root : Finset C)
    (Q : C → Set (EuclideanSpace ℝ (Fin b ⊕ Fin c))) (p η r : ℝ)
    (hp : 0 < p) (hactive : ∀ q ∈ root, 1 ≤ ParentLevel.capacity Y cube q)
    (F : ActualBufferedCubeForest (J:=J) (s:=s) P D S root Q (bufferedTupleWeight Y cube p) η r depth) :
    let selected := F.frontier.biUnion (ownedPartitionSelected root F.node)
    tupleCubeMass Y cube root p / ((2*(S.card:ℝ))^depth*((2*(S.card:ℝ))*(s+1:ℕ))) ≤
      tupleCubeMass (Y.filter fun y => cube y ∈ selected) cube root p ∧
    (∀ q ∈ selected, (Y.filter fun y => cube y ∈ selected).filter (fun y => cube y=q) =
      Y.filter (fun y => cube y=q)) := by
  classical
  dsimp only
  have heq : ∀ q ∈ root, bufferedTupleWeight Y cube p q = (ParentLevel.capacity Y cube q:ℝ)^p := by
    intro q hq
    exact max_eq_right (Real.one_le_rpow (by exact_mod_cast hactive q hq) hp.le)
  have htotal : ownedCubeMass (bufferedTupleWeight Y cube p) root=tupleCubeMass Y cube root p :=
    Finset.sum_congr rfl (fun q hq => heq q hq)
  have hselected : ownedCubeMass (bufferedTupleWeight Y cube p)
      (F.frontier.biUnion (ownedPartitionSelected root F.node)) =
      tupleCubeMass (Y.filter fun y => cube y ∈ F.frontier.biUnion (ownedPartitionSelected root F.node)) cube root p := by
    rw [whole_cube_selection_mass Y cube root _ F.selected_subset hp]
    exact Finset.sum_congr rfl (fun q hq => heq q (F.selected_subset hq))
  constructor
  · simpa only [htotal,hselected] using F.retention
  · intro q hq
    exact cube_selection_full_fiber Y cube _ hq

end KakeyaTwoScale
#print axioms KakeyaTwoScale.actual_buffered_forest_tuple_retention
