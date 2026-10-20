module
public import KakeyaTwoScale.NonlinearTupleSelection
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Actual tuples over one cube inject into their family piece records. The
right side counts all available pieces in each family, without any lower bound
or Cartesian-product assumption on the relation. -/
theorem terminal_fiber_card_le {T Q P : Type*} [DecidableEq T] [DecidableEq Q]
    [DecidableEq P] {k : ℕ} (Y : Finset T) (cube : T → Q)
    (piece : T → Fin k → P) (pieces : Fin k → Finset P)
    (hmem : ∀ y ∈ Y, ∀ j, piece y j ∈ pieces j)
    (hinj : ∀ y ∈ Y, ∀ z ∈ Y, cube y=cube z → piece y=piece z → y=z)
    (q : Q) : ParentLevel.capacity Y cube q ≤ ∏ j, (pieces j).card := by
  classical
  have h := Finset.card_le_card_of_injOn (s:=Y.filter fun y => cube y=q)
    (t:=Fintype.piFinset pieces) piece
    (fun y hy => Fintype.mem_piFinset.mpr (hmem y (Finset.mem_filter.mp hy).1))
    (by
      intro y hy z hz he
      obtain ⟨hy,hq⟩ := Finset.mem_filter.mp hy
      obtain ⟨hz,hr⟩ := Finset.mem_filter.mp hz
      exact hinj y hy z hz (hq.trans hr.symm) he)
  simpa only [ParentLevel.capacity,Fintype.card_piFinset] using h

/-- The all-small terminal finite estimate on the ACTUAL nonlinear mass.
A geometric small-ball lattice bound may supply `cubes.card ≤ B`. This theorem
itself neither asserts that geometry nor uses a multilinear Kakeya input. -/
theorem terminal_tuple_mass_le {T Q P : Type*} [DecidableEq T] [DecidableEq Q]
    [DecidableEq P] {k : ℕ} (Y : Finset T) (cube : T → Q) (cubes : Finset Q)
    (piece : T → Fin k → P) (pieces : Fin k → Finset P)
    (hmem : ∀ y ∈ Y, ∀ j, piece y j ∈ pieces j)
    (hinj : ∀ y ∈ Y, ∀ z ∈ Y, cube y=cube z → piece y=piece z → y=z)
    {p : ℝ} (hp : 0 ≤ p) {B : ℝ} (hB : (cubes.card:ℝ) ≤ B) :
    tupleCubeMass Y cube cubes p ≤ B*(∏ j, ((pieces j).card:ℝ))^p := by
  have hpoint (q : Q) : (ParentLevel.capacity Y cube q:ℝ) ≤
      ∏ j, ((pieces j).card:ℝ) := by
    exact_mod_cast terminal_fiber_card_le Y cube piece pieces hmem hinj q
  calc
    tupleCubeMass Y cube cubes p ≤
        ∑ _q ∈ cubes, (∏ j, ((pieces j).card:ℝ))^p := by
      exact Finset.sum_le_sum (fun q _ => Real.rpow_le_rpow (Nat.cast_nonneg _) (hpoint q) hp)
    _ = (cubes.card:ℝ)*(∏ j, ((pieces j).card:ℝ))^p := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg (by positivity) _)

/-- Exact exponent of each degree in the all-small terminal estimate. This is
why truncating the run preserves the same denominator as the multilinear
branch with subsequent virtual degrees one. -/
theorem terminal_degree_exponent (n k s : ℝ) :
    (n-s+1)*(k-1)+k*(s-n) = -((n-k)-s+1) := by ring

theorem terminal_delta_exponent (n k : ℝ) :
    n*(k-1)=k-n+k*(n-1) := by ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.terminal_fiber_card_le
#print axioms KakeyaTwoScale.terminal_tuple_mass_le
#print axioms KakeyaTwoScale.terminal_degree_exponent
#print axioms KakeyaTwoScale.terminal_delta_exponent
