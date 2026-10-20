module
public import KakeyaTwoScale.BalancedVertical
public import KakeyaTwoScale.RefinedFiberProjection

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- Corner retention with a balanced second wing and an arbitrary selected
first-wing family. Q is an actual refinement of the selected vertical set;
the error is its actual number of deleted edges. -/
theorem balanced_corner_retention {A B I : Type*} [DecidableEq A]
    (S : Finset A) (T : I → Finset B) (f : I → A → B) (is : List I)
    (N : ℕ) {i j : I} (hi : i ∈ is) (hj : j ∈ is)
    (hNi : (T i).card ≤ N) (hNj : (T j).card ≤ N)
    (W : A → Finset A)
    (hW : ∀ x ∈ popularRounds T f 2 is S,
      W x ⊆ balancedWing S (f i) x ((popularRounds T f 2 is S).card/(2*N)))
    (Q : Finset (Σ _ : A, A)) (hQ : Q ⊆ balancedVertical S T f is N j) :
    let R := popularRounds T f 2 is S
    let L := R.card/(2*N)
    let V := balancedVertical S T f is N j
    L*(wingEdges R W).card ≤
      (wingCorners R W (fun x => (balancedWing S (f j) x L).filter
        (fun y => Sigma.mk x y ∈ Q))).card + L*(V.card-Q.card) := by
  dsimp only
  let R := popularRounds T f 2 is S
  let L := R.card/(2*N)
  let right := fun x => balancedWing S (f j) x L
  let keep := fun x y => Sigma.mk x y ∈ Q
  have hleft : ∀ x ∈ R, L ≤ (right x).card := by
    intro x hx
    exact (popular_balanced_wing_card S T f is N hj hNj hx).ge
  have hright : ∀ x ∈ R, (W x).card ≤ L := by
    intro x hx
    exact (Finset.card_le_card (hW x hx)).trans_eq
      (popular_balanced_wing_card S T f is N hi hNi hx)
  have h := wingCorners_retention R right W keep L L hleft hright
  have hbad : wingEdges R (fun x => (right x).filter (fun y => ¬ keep x y)) =
      (balancedVertical S T f is N j) \ Q := by
    ext v
    simp only [wingEdges, right, keep, balancedVertical, R, L,
      Finset.mem_sigma, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hswap : (wingCorners R (fun x => (right x).filter (keep x)) W).card =
      (wingCorners R W (fun x => (right x).filter (keep x))).card := by
    simp only [wingCorners_card]
    exact Finset.sum_congr rfl fun x _ => Nat.mul_comm _ _
  rw [hbad, Finset.card_sdiff_of_subset hQ, hswap] at h
  exact h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.balanced_corner_retention
