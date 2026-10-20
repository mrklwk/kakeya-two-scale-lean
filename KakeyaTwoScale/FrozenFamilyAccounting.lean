module
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators
namespace KakeyaTwoScale

/-- In a monotone dyadic-length history, a family with positive terminal
height could not previously have been frozen at height zero. -/
theorem positive_terminal_family_not_frozen {k : ℕ}
    (height : ℕ → Fin k → ℕ) (frozen : ℕ → Finset (Fin k))
    (hmono : ∀ t i, height (t+1) i ≤ height t i)
    (hfloor : ∀ t i, i ∈ frozen t → height t i=0)
    {s t : ℕ} (hst : s ≤ t) {i : Fin k} (hpos : 0 < height t i) : i ∉ frozen s := by
  have hh : height t i ≤ height s i := by
    exact (antitone_nat_of_succ_le (f:=fun t => height t i) (fun t => hmono t i)) hst
  intro hi
  have hf := hfloor s i hi
  omega

/-- A legal normalization history has a quantitative finite round budget.
Each step either lowers total dyadic height by d or freezes a new family;
heights never increase and frozen sets never shrink. This proves termination
accounting only, not geometric feasibility or lower-count success. -/
theorem frozen_normalization_round_budget {k B d N : ℕ}
    (height : ℕ → Fin k → ℕ) (frozen : ℕ → Finset (Fin k))
    (hinit : ∀ i, height 0 i ≤ B)
    (hmono : ∀ t < N, ∀ i, height (t+1) i ≤ height t i)
    (hfrozen : ∀ t < N, frozen t ⊆ frozen (t+1))
    (hstep : ∀ t < N,
      (∑ i, height (t+1) i)+d ≤ ∑ i, height t i ∨
      (frozen t).card+1 ≤ (frozen (t+1)).card) :
    N*d ≤ k*B+d*k := by
  let potential (t : ℕ) := (∑ i, height t i)+d*(k-(frozen t).card)
  have hcard (t : ℕ) : (frozen t).card ≤ k := by
    simpa using Finset.card_le_univ (frozen t)
  have hdrop : ∀ t < N, potential (t+1)+d ≤ potential t := by
    intro t ht
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hmono t ht i)
    have hf := Finset.card_le_card (hfrozen t ht)
    have hrem : k-(frozen (t+1)).card ≤ k-(frozen t).card := Nat.sub_le_sub_left hf k
    have hm := Nat.mul_le_mul_left d hrem
    rcases hstep t ht with hs | hs
    · dsimp [potential]
      omega
    · have hr : k-(frozen (t+1)).card+1 ≤ k-(frozen t).card := by
        have hc := hcard (t+1)
        omega
      have hmul := Nat.mul_le_mul_left d hr
      dsimp [potential]
      nlinarith
  have htel : ∀ t ≤ N, t*d+potential t ≤ potential 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      intro ht
      have hi := ih (by omega)
      have hh := hdrop t (by omega)
      nlinarith
  have h0 : potential 0 ≤ k*B+d*k := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hinit i)
    have hm := Nat.mul_le_mul_left d (Nat.sub_le k (frozen 0).card)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hh
    dsimp [potential]
    omega
  exact (Nat.le_add_right (N*d) (potential N)).trans ((htel N le_rfl).trans h0)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.positive_terminal_family_not_frozen
#print axioms KakeyaTwoScale.frozen_normalization_round_budget
