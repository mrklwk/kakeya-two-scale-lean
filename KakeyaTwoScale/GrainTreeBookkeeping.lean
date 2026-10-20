module
public import KakeyaTwoScale.SlopeTree
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open scoped BigOperators
namespace KakeyaTwoScale

/-- Branching propagates to actual generated finite levels, without a geometry
premise. Roots may merge; this only improves the upper bound. -/
theorem grainTree_level_card_le {A : Type*} [DecidableEq A]
    (roots : Finset A) (children : A → Finset A) (B : ℕ)
    (hB : ∀ s, ∀ x ∈ slopeTreeLevels roots children s, (children x).card ≤ B)
    (s : ℕ) : (slopeTreeLevels roots children s).card ≤ roots.card*B^s := by
  induction s with
  | zero => simp [slopeTreeLevels]
  | succ s ih =>
    calc
      _ ≤ ∑ x ∈ slopeTreeLevels roots children s, (children x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ slopeTreeLevels roots children s, B :=
        Finset.sum_le_sum fun x hx => hB s x hx
      _ = (slopeTreeLevels roots children s).card*B := by simp
      _ ≤ (roots.card*B^s)*B := Nat.mul_le_mul_right B ih
      _ = _ := by rw [pow_succ, Nat.mul_assoc]

/-- At most K terminal pieces per level-s interval, with E+1 successors per
interval, gives K * roots.card * (E+1)^s pieces. No subtubes are postulated. -/
theorem grainTree_piece_sum_le {A : Type*} [DecidableEq A]
    (roots : Finset A) (children : A → Finset A) (E K s : ℕ) (pieces : A → ℕ)
    (hB : ∀ t, ∀ x ∈ slopeTreeLevels roots children t, (children x).card ≤ E+1)
    (hK : ∀ x ∈ slopeTreeLevels roots children s, pieces x ≤ K) :
    ∑ x ∈ slopeTreeLevels roots children s, pieces x ≤ K*roots.card*(E+1)^s := by
  calc
    _ ≤ ∑ _x ∈ slopeTreeLevels roots children s, K := Finset.sum_le_sum hK
    _ = K*(slopeTreeLevels roots children s).card := by simp [Nat.mul_comm]
    _ ≤ K*(roots.card*(E+1)^s) := Nat.mul_le_mul_left K
      (grainTree_level_card_le roots children (E+1) hB s)
    _ = _ := by rw [Nat.mul_assoc]

/-- Actual positive integer occupancy contracts along a generated child path. -/
theorem grainTree_occupancy_le {A : Type*} [DecidableEq A]
    (roots : Finset A) (children : A → Finset A) (q : A → ℕ)
    (β Q : ℝ) (hβ : 0 ≤ β)
    (hroot : ∀ x ∈ roots, (q x:ℝ) ≤ Q)
    (hchild : ∀ s, ∀ x ∈ slopeTreeLevels roots children s,
      ∀ y ∈ children x, (q y:ℝ) ≤ β*q x) :
    ∀ s, ∀ x ∈ slopeTreeLevels roots children s, (q x:ℝ) ≤ β^s*Q := by
  intro s
  induction s with
  | zero => simpa [slopeTreeLevels] using hroot
  | succ s ih =>
    intro y hy
    obtain ⟨x,hx,hyx⟩ := Finset.mem_biUnion.mp hy
    calc
      _ ≤ β*q x := hchild s x hx y hyx
      _ ≤ β*(β^s*Q) := mul_le_mul_of_nonneg_left (ih x hx) hβ
      _ = β^(s+1)*Q := by rw [pow_succ]; ring

/-- A nonempty occupied vertex gives an explicit logarithmic depth bound.
β is the actual contraction factor; selecting E to ensure β<1 is separate. -/
theorem grainTree_occupied_depth_le {A : Type*} [DecidableEq A]
    (roots : Finset A) (children : A → Finset A) (q : A → ℕ)
    (β Q : ℝ) (hβ : 0 < β) (hβone : β < 1) (hQ : 0 < Q)
    (hroot : ∀ x ∈ roots, (q x:ℝ) ≤ Q)
    (hchild : ∀ s, ∀ x ∈ slopeTreeLevels roots children s,
      ∀ y ∈ children x, (q y:ℝ) ≤ β*q x)
    {s : ℕ} {x : A} (hx : x ∈ slopeTreeLevels roots children s) (hq : 0 < q x) :
    (s:ℝ) ≤ Real.log Q / (-Real.log β) := by
  have hlow : (1:ℝ) ≤ (q x:ℝ) := by exact_mod_cast hq
  have hbound := hlow.trans (grainTree_occupancy_le roots children q β Q hβ.le hroot hchild s x hx)
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<1) hbound
  rw [Real.log_one, Real.log_mul (pow_pos hβ _).ne' hQ.ne', Real.log_pow] at hl
  have hneg : Real.log β < 0 := Real.log_neg hβ hβone
  apply (le_div_iff₀ (neg_pos.mpr hneg)).mpr
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.grainTree_level_card_le
#print axioms KakeyaTwoScale.grainTree_piece_sum_le
#print axioms KakeyaTwoScale.grainTree_occupancy_le
#print axioms KakeyaTwoScale.grainTree_occupied_depth_le
