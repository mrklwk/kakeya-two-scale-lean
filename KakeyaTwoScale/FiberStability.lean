module
public import KakeyaTwoScale.StrongPopularity
public import Mathlib.Data.Finset.Image

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- Keep points whose refined fiber has at least half its original size. -/
def stableFibers {A B : Type*} (S R : Finset A) (f : A → B) : Finset A :=
  R.filter (fun x => (S.filter (fun y => f y = f x)).card ≤
    2*(R.filter (fun y => f y = f x)).card)

/-- Restoring fiber comparability costs at most the original number deleted,
in addition to the original deletion. This is an actual filter of R. -/
theorem stableFibers_loss {A B : Type*} (S R : Finset A) (f : A → B)
    (hRS : R ⊆ S) :
    S.card - (stableFibers S R f).card ≤ 2*(S.card-R.card) := by
  let T := S.image f
  let D := S \ R
  let bad := R.filter (fun x => ¬ (S.filter (fun y => f y = f x)).card ≤
    2*(R.filter (fun y => f y = f x)).card)
  have hpartition : (stableFibers S R f).card + bad.card = R.card :=
    Finset.card_filter_add_card_filter_not _
  have hbound (t) (_ht : t ∈ T) :
      (bad.filter (fun x => f x = t)).card ≤ (D.filter (fun x => f x = t)).card := by
    by_cases hne : (bad.filter (fun x => f x = t)).Nonempty
    · obtain ⟨x,hx⟩ := hne
      obtain ⟨hx,hft⟩ := Finset.mem_filter.mp hx
      have hbad := (Finset.mem_filter.mp hx).2
      rw [hft] at hbad
      have hsub : R.filter (fun x => f x = t) ⊆ S.filter (fun x => f x = t) :=
        Finset.filter_subset_filter _ hRS
      have he : D.filter (fun x => f x = t) =
          (S.filter (fun x => f x = t)) \ (R.filter (fun x => f x = t)) := by
        ext x
        simp only [D, Finset.mem_filter, Finset.mem_sdiff]
        tauto
      have hc : (D.filter (fun x => f x = t)).card =
          (S.filter (fun x => f x = t)).card - (R.filter (fun x => f x = t)).card := by
        rw [he, Finset.card_sdiff_of_subset hsub]
      have hbsub : bad.filter (fun x => f x = t) ⊆ R.filter (fun x => f x = t) :=
        Finset.filter_subset_filter _ (Finset.filter_subset _ _)
      have hb := Finset.card_le_card hbsub
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  have hmapB : ∀ x ∈ bad, f x ∈ T := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hRS (Finset.mem_filter.mp hx).1, rfl⟩
  have hmapD : ∀ x ∈ D, f x ∈ T := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, (Finset.mem_sdiff.mp hx).1, rfl⟩
  have hb : (∑ t ∈ T, (bad.filter (fun x => f x = t)).card) = bad.card := by
    simpa using Finset.sum_fiberwise_of_maps_to hmapB (fun _ => (1:ℕ))
  have hd : (∑ t ∈ T, (D.filter (fun x => f x = t)).card) = D.card := by
    simpa using Finset.sum_fiberwise_of_maps_to hmapD (fun _ => (1:ℕ))
  have hh : bad.card ≤ D.card := by
    rw [← hb, ← hd]
    exact Finset.sum_le_sum hbound
  have hD : D.card = S.card - R.card := Finset.card_sdiff_of_subset hRS
  omega

/-- This filter retains whole refined fibers; the half-original lower bound
therefore holds in the output itself, not just in the input refinement R. -/
theorem stableFibers_fiber_eq {A B : Type*} (S R : Finset A) (f : A → B)
    {x : A} (hx : x ∈ stableFibers S R f) :
    (stableFibers S R f).filter (fun y => f y = f x) = R.filter (fun y => f y = f x) := by
  ext y
  constructor
  · intro hy
    obtain ⟨hy,he⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,he⟩
  · intro hy
    obtain ⟨hy,he⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hy, ?_⟩,he⟩
    rw [he]
    exact (Finset.mem_filter.mp hx).2

theorem stableFibers_comparable {A B : Type*} (S R : Finset A) (f : A → B)
    {x : A} (hx : x ∈ stableFibers S R f) :
    (S.filter (fun y => f y = f x)).card ≤
      2*((stableFibers S R f).filter (fun y => f y = f x)).card := by
  rw [stableFibers_fiber_eq S R f hx]
  exact (Finset.mem_filter.mp hx).2

/-- Combined explicit loss for iterated strong popularity followed by a
single chosen fiber-comparability refinement. -/
theorem stablePopularRounds_loss {A B I D : Type*} (T : I → Finset B)
    (f : I → A → B) (g : A → D) (d : ℕ) (is : List I) (S : Finset A)
    (hf : ∀ i ∈ is, ∀ x ∈ S, f i x ∈ T i) :
    d * (S.card - (stableFibers S (popularRounds T f d is S) g).card) ≤
      2*is.length*S.card := by
  have h1 := stableFibers_loss S (popularRounds T f d is S) g
    (popularRounds_subset T f d is S)
  have h2 := popularRounds_loss T f d is S hf
  have h3 := Nat.mul_le_mul_left d h1
  nlinarith

/-- Original projection-fiber lower bounds survive the additional stability
filter, with the cardinality of the actual final set on the left. -/
theorem stablePopularRounds_original_fiber {A B I D : Type*} (T : I → Finset B)
    (f : I → A → B) (g : A → D) (d : ℕ) (is : List I) (S : Finset A)
    {x : A} (hx : x ∈ stableFibers S (popularRounds T f d is S) g) :
    ∀ i ∈ is, (stableFibers S (popularRounds T f d is S) g).card ≤
      d*(T i).card*(S.filter (fun y => f i y = f i x)).card := by
  intro i hi
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (popularRounds_original_fiber T f d is S (Finset.mem_filter.mp hx).1 i hi)

/-- Simultaneous static filters have an additive deletion budget. -/
theorem simultaneous_filter_loss {A I : Type*} (S : Finset A) (F : Finset I)
    (p : I → A → Prop) [∀ i, DecidablePred (p i)] :
    S.card - (S.filter (fun x => ∀ i ∈ F, p i x)).card ≤
      ∑ i ∈ F, (S.filter (fun x => ¬ p i x)).card := by
  let bad := S.filter (fun x => ¬ ∀ i ∈ F, p i x)
  have hp : (S.filter (fun x => ∀ i ∈ F, p i x)).card + bad.card = S.card :=
    Finset.card_filter_add_card_filter_not _
  have hsub : bad ⊆ F.biUnion (fun i => S.filter (fun x => ¬ p i x)) := by
    intro x hx
    obtain ⟨hx,hn⟩ := Finset.mem_filter.mp hx
    push Not at hn
    obtain ⟨i,hi,hp⟩ := hn
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hx,hp⟩⟩
  have hb := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have he : S.card - (S.filter (fun x => ∀ i ∈ F, p i x)).card = bad.card := by omega
  rw [he]
  exact hb

/-- Simultaneous comparability tests retain most points, but the comparisons
are with R-fibers. This theorem deliberately does not claim comparability of
fibers in the intersection output. -/
theorem simultaneous_stable_loss {A B I : Type*} (S R : Finset A)
    (F : Finset I) (f : I → A → B) (hRS : R ⊆ S) :
    S.card - (R.filter (fun x => ∀ i ∈ F,
      (S.filter (fun y => f i y = f i x)).card ≤
        2*(R.filter (fun y => f i y = f i x)).card)).card ≤
      (F.card+1)*(S.card-R.card) := by
  classical
  let p := fun i x => (S.filter (fun y => f i y = f i x)).card ≤
    2*(R.filter (fun y => f i y = f i x)).card
  have hbad (i) : (R.filter (fun x => ¬ p i x)).card ≤ S.card-R.card := by
    have h := stableFibers_loss S R (f i) hRS
    have hp : (stableFibers S R (f i)).card + (R.filter (fun x => ¬ p i x)).card = R.card :=
      Finset.card_filter_add_card_filter_not _
    have hc := Finset.card_le_card hRS
    omega
  have h : R.card - (R.filter (fun x => ∀ i ∈ F, p i x)).card ≤
      ∑ i ∈ F, (R.filter (fun x => ¬ p i x)).card := by
    simpa only using simultaneous_filter_loss R F p
  have hs : (∑ i ∈ F, (R.filter (fun x => ¬ p i x)).card) ≤ F.card*(S.card-R.card) := by
    calc
      _ ≤ ∑ _i ∈ F, (S.card-R.card) := Finset.sum_le_sum fun i _ => hbad i
      _ = _ := by simp
  have hQR := Finset.card_le_card (Finset.filter_subset (fun x => ∀ i ∈ F, p i x) R)
  have hRS' := Finset.card_le_card hRS
  change S.card - (R.filter (fun x => ∀ i ∈ F, p i x)).card ≤ (F.card+1)*(S.card-R.card)
  have he : S.card - (R.filter (fun x => ∀ i ∈ F, p i x)).card =
      (S.card-R.card) + (R.card-(R.filter (fun x => ∀ i ∈ F, p i x)).card) := by omega
  rw [he]
  simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using
    Nat.add_le_add_left (h.trans hs) (S.card-R.card)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.stableFibers_loss
#print axioms KakeyaTwoScale.stableFibers_fiber_eq
#print axioms KakeyaTwoScale.stableFibers_comparable
#print axioms KakeyaTwoScale.stablePopularRounds_loss
#print axioms KakeyaTwoScale.stablePopularRounds_original_fiber
#print axioms KakeyaTwoScale.simultaneous_filter_loss
#print axioms KakeyaTwoScale.simultaneous_stable_loss
