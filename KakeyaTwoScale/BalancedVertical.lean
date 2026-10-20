module
public import KakeyaTwoScale.CornerRetention
public import KakeyaTwoScale.StrongPopularity

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- Half-popularity through s successive projections retains at least 2⁻ˢ. -/
theorem popularRounds_half {A B I : Type*} (T : I → Finset B) (f : I → A → B)
    (is : List I) (S : Finset A) (hf : ∀ i ∈ is, ∀ x ∈ S, f i x ∈ T i) :
    S.card ≤ 2^is.length * (popularRounds T f 2 is S).card := by
  induction is generalizing S with
  | nil => simp [popularRounds]
  | cons i is ih =>
    let P := strongPopular S (T i) (f i) 2
    have hPS : P ⊆ S := Finset.filter_subset _ _
    have hcard := Finset.card_le_card hPS
    have hl := strongPopular_loss S (T i) (f i) 2 (hf i (by simp))
    change 2*(S.card-P.card) ≤ S.card at hl
    have hh : S.card ≤ 2*P.card := by omega
    have htail := ih P (fun j hj x hx => hf j (by simp [hj]) x (hPS hx))
    change S.card ≤ 2^(is.length+1) * (popularRounds T f 2 is P).card
    rw [pow_succ]
    nlinarith

/-- Choose exactly L points from the original fiber when it is large enough. -/
def balancedWing {A B : Type*} (S : Finset A) (f : A → B) (x : A) (L : ℕ) : Finset A :=
  if h : L ≤ (S.filter (fun y => f y = f x)).card then
    Classical.choose (Finset.exists_subset_card_eq h)
  else ∅

theorem balancedWing_subset {A B : Type*} (S : Finset A) (f : A → B) (x : A) (L : ℕ) :
    balancedWing S f x L ⊆ S.filter (fun y => f y = f x) := by
  unfold balancedWing
  split
  · rename_i h
    exact (Classical.choose_spec (Finset.exists_subset_card_eq h)).1
  · exact Finset.empty_subset _

theorem balancedWing_card {A B : Type*} (S : Finset A) (f : A → B) (x : A) (L : ℕ)
    (h : L ≤ (S.filter (fun y => f y = f x)).card) :
    (balancedWing S f x L).card = L := by
  unfold balancedWing
  rw [dite_eq_left h]
  exact (Classical.choose_spec (Finset.exists_subset_card_eq h)).2

/-- The selected vertical family has popular centers and exactly the same
integer number of wings at every center and for every listed projection. -/
def balancedVertical {A B I : Type*} (S : Finset A) (T : I → Finset B)
    (f : I → A → B) (is : List I) (N : ℕ) (i : I) : Finset (Σ _ : A, A) :=
  let R := popularRounds T f 2 is S
  R.sigma (fun x => balancedWing S (f i) x (R.card/(2*N)))

theorem popular_balanced_wing_card {A B I : Type*} (S : Finset A) (T : I → Finset B)
    (f : I → A → B) (is : List I) (N : ℕ) {i : I} (hi : i ∈ is)
    (hN : (T i).card ≤ N) {x : A} (hx : x ∈ popularRounds T f 2 is S) :
    (balancedWing S (f i) x ((popularRounds T f 2 is S).card/(2*N))).card =
      (popularRounds T f 2 is S).card/(2*N) := by
  apply balancedWing_card
  have h := popularRounds_original_fiber T f 2 is S hx i hi
  apply Nat.div_le_of_le_mul
  have hm := Nat.mul_le_mul_right (S.filter (fun y => f i y = f i x)).card
    (Nat.mul_le_mul_left 2 hN)
  exact h.trans hm

theorem balancedVertical_card {A B I : Type*} (S : Finset A) (T : I → Finset B)
    (f : I → A → B) (is : List I) (N : ℕ) {i : I} (hi : i ∈ is)
    (hN : (T i).card ≤ N) :
    (balancedVertical S T f is N i).card =
      (popularRounds T f 2 is S).card * ((popularRounds T f 2 is S).card/(2*N)) := by
  unfold balancedVertical
  rw [Finset.card_sigma]
  calc
    _ = ∑ _x ∈ popularRounds T f 2 is S, (popularRounds T f 2 is S).card/(2*N) :=
      Finset.sum_congr rfl (fun x hx => popular_balanced_wing_card S T f is N hi hN hx)
    _ = _ := by simp

/-- Exact division-free mass bounds corresponding to |V| comparable to
|S|²/N, with all constants and the rounding-size condition explicit. -/
theorem balancedVertical_mass {A B I : Type*} (S : Finset A) (T : I → Finset B)
    (f : I → A → B) (is : List I) (N : ℕ) {i : I} (hi : i ∈ is)
    (hf : ∀ j ∈ is, ∀ x ∈ S, f j x ∈ T j)
    (hN : (T i).card ≤ N) (hNpos : 0 < N)
    (hlarge : 2*N ≤ (popularRounds T f 2 is S).card) :
    S.card^2 ≤ 4*(2^is.length)^2*N*(balancedVertical S T f is N i).card ∧
      2*N*(balancedVertical S T f is N i).card ≤ S.card^2 := by
  let R := popularRounds T f 2 is S
  let L := R.card/(2*N)
  have hcard := balancedVertical_card S T f is N hi hN
  change (balancedVertical S T f is N i).card = R.card*L at hcard
  have hpos : 0 < L := Nat.div_pos hlarge (by omega)
  have hfloor := Nat.lt_mul_div_succ R.card (by omega : 0 < 2*N)
  change R.card < 2*N*(L+1) at hfloor
  have hround : R.card ≤ 4*N*L := by nlinarith
  have hret := popularRounds_half T f is S hf
  change S.card ≤ 2^is.length*R.card at hret
  have hsub := Finset.card_le_card (popularRounds_subset T f 2 is S)
  change R.card ≤ S.card at hsub
  have hdiv := Nat.div_mul_le_self R.card (2*N)
  change L*(2*N) ≤ R.card at hdiv
  rw [hcard]
  constructor
  · have hsq := Nat.mul_le_mul hret hret
    have hm := Nat.mul_le_mul_left ((2^is.length)^2*R.card) hround
    nlinarith
  · have hm := Nat.mul_le_mul_left R.card hdiv
    have hsq := Nat.mul_le_mul hsub hsub
    nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.popularRounds_half
#print axioms KakeyaTwoScale.balancedWing_subset
#print axioms KakeyaTwoScale.balancedWing_card
#print axioms KakeyaTwoScale.popular_balanced_wing_card
#print axioms KakeyaTwoScale.balancedVertical_card
#print axioms KakeyaTwoScale.balancedVertical_mass
