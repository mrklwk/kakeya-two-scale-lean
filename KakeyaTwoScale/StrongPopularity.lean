module
public import KakeyaTwoScale.ProjectionPopularity

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- Strong popularity at reciprocal-integer threshold 1/d. -/
def strongPopular {J K : Type*} (S : Finset J) (T : Finset K)
    (f : J → K) (d : ℕ) : Finset J :=
  S.filter (fun j => S.card ≤ d*T.card*(S.filter (fun i => f i = f j)).card)

theorem strongPopular_loss {J K : Type*} (S : Finset J) (T : Finset K)
    (f : J → K) (d : ℕ) (hf : ∀ j ∈ S, f j ∈ T) :
    d * (S.card - (strongPopular S T f d).card) ≤ S.card := by
  let bad := S.filter (fun j => ¬ S.card ≤ d*T.card*(S.filter (fun i => f i = f j)).card)
  have hpartition : (strongPopular S T f d).card + bad.card = S.card := by
    exact Finset.card_filter_add_card_filter_not _
  by_cases hT : T.card = 0
  · have hS : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have := hf j hj
      simp [Finset.card_eq_zero.mp hT] at this
    simp [hS, strongPopular]
  have hTpos : 0 < T.card := Nat.pos_of_ne_zero hT
  have hfib : ∀ t ∈ T, d*T.card*(bad.filter (fun j => f j = t)).card ≤ S.card := by
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
  have hbound : d*T.card*bad.card ≤ T.card*S.card := by
    calc
      _ = ∑ t ∈ T, d*T.card*(bad.filter (fun j => f j = t)).card := by rw [← Finset.mul_sum, hsum]
      _ ≤ ∑ _t ∈ T, S.card := Finset.sum_le_sum hfib
      _ = _ := by simp
  have hbad : d*bad.card ≤ S.card := by nlinarith
  have he : S.card - (strongPopular S T f d).card = bad.card := by omega
  simpa only [he] using hbad

/-- Successive filters use each projection's own finite target. -/
def popularRounds {A B I : Type*} (T : I → Finset B) (f : I → A → B)
    (d : ℕ) : List I → Finset A → Finset A
  | [], S => S
  | i :: is, S => popularRounds T f d is (strongPopular S (T i) (f i) d)

theorem popularRounds_subset {A B I : Type*} (T : I → Finset B) (f : I → A → B)
    (d : ℕ) (is : List I) (S : Finset A) : popularRounds T f d is S ⊆ S := by
  induction is generalizing S with
  | nil => exact Finset.Subset.refl _
  | cons i is ih =>
    exact (ih _).trans (Finset.filter_subset _ _)

/-- Losses add over rounds: d times the number deleted is at most the
number of rounds times the ORIGINAL source size, not an unspecified constant. -/
theorem popularRounds_loss {A B I : Type*} (T : I → Finset B) (f : I → A → B)
    (d : ℕ) (is : List I) (S : Finset A)
    (hf : ∀ i ∈ is, ∀ x ∈ S, f i x ∈ T i) :
    d * (S.card - (popularRounds T f d is S).card) ≤ is.length * S.card := by
  induction is generalizing S with
  | nil => simp [popularRounds]
  | cons i is ih =>
    let P := strongPopular S (T i) (f i) d
    have hPS : P ⊆ S := Finset.filter_subset _ _
    have h1 := strongPopular_loss S (T i) (f i) d (hf i (by simp))
    have h2 := ih P (fun j hj x hx => hf j (by simp [hj]) x (hPS hx))
    have hp := Finset.card_le_card hPS
    have hq := Finset.card_le_card (popularRounds_subset T f d is P)
    have he : S.card - (popularRounds T f d is P).card =
        (S.card - P.card) + (P.card - (popularRounds T f d is P).card) := by omega
    change d*(S.card-(popularRounds T f d is P).card) ≤ (is.length+1)*S.card
    rw [he, Nat.mul_add]
    have h3 := Nat.mul_le_mul_left is.length hp
    change d*(S.card-P.card) ≤ S.card at h1
    nlinarith

/-- Each surviving point has a large fiber in the ORIGINAL set for every
projection used. Subsequent filters need not preserve earlier refined fibers. -/
theorem popularRounds_original_fiber {A B I : Type*} (T : I → Finset B)
    (f : I → A → B) (d : ℕ) (is : List I) (S : Finset A)
    {x : A} (hx : x ∈ popularRounds T f d is S) :
    ∀ i ∈ is, (popularRounds T f d is S).card ≤
      d*(T i).card*(S.filter (fun y => f i y = f i x)).card := by
  induction is generalizing S with
  | nil => simp
  | cons j is ih =>
    let P := strongPopular S (T j) (f j) d
    have hPS : P ⊆ S := Finset.filter_subset _ _
    have hxP : x ∈ P := popularRounds_subset T f d is P hx
    intro i hi
    rcases List.mem_cons.mp hi with he | hi
    · subst i
      have ht := (Finset.mem_filter.mp hxP).2
      exact (Finset.card_le_card (popularRounds_subset T f d (j::is) S)).trans ht
    · have ht := ih P hx i hi
      have hsub : P.filter (fun y => f i y = f i x) ⊆ S.filter (fun y => f i y = f i x) :=
        Finset.filter_subset_filter _ hPS
      exact ht.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.strongPopular_loss
#print axioms KakeyaTwoScale.popularRounds_subset
#print axioms KakeyaTwoScale.popularRounds_loss
#print axioms KakeyaTwoScale.popularRounds_original_fiber
