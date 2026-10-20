module
public import KakeyaTwoScale.FiberStability
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

/-- Original mass of the fibers still occupied by Q. -/
def occupiedFiberMass {A B : Type*} [DecidableEq B]
    (S Q : Finset A) (f : A → B) : ℕ :=
  ∑ y ∈ Q.image f, (S.filter (fun x => f x = y)).card

theorem occupiedFiberMass_self {A B : Type*} [DecidableEq B]
    (S : Finset A) (f : A → B) : occupiedFiberMass S S f = S.card := by
  unfold occupiedFiberMass
  simpa using Finset.sum_fiberwise_of_maps_to
    (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩ : ∀ x ∈ S, f x ∈ S.image f) (fun _ => (1:ℕ))

theorem occupiedFiberMass_mono {A B : Type*} [DecidableEq B]
    (S P Q : Finset A) (f : A → B) (hPQ : P ⊆ Q) :
    occupiedFiberMass S P f ≤ occupiedFiberMass S Q f := by
  exact Finset.sum_le_sum_of_subset (Finset.image_subset_image hPQ)

theorem occupiedFiberMass_lower {A B : Type*} [DecidableEq B]
    (S Q : Finset A) (f : A → B) (hQS : Q ⊆ S) :
    Q.card ≤ occupiedFiberMass S Q f := by
  rw [← occupiedFiberMass_self Q f]
  exact Finset.sum_le_sum fun y _ => Finset.card_le_card (Finset.filter_subset_filter _ hQS)

/-- Deleting one complete current fiber removes its full original mass from
the occupied-fiber potential. -/
theorem occupiedFiberMass_remove {A B : Type*} [DecidableEq B]
    (S Q : Finset A) (f : A → B) {x : A} (hx : x ∈ Q) :
    occupiedFiberMass S (Q.filter (fun y => f y ≠ f x)) f +
      (S.filter (fun y => f y = f x)).card = occupiedFiberMass S Q f := by
  have he : (Q.filter (fun y => f y ≠ f x)).image f = (Q.image f).erase (f x) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨z,⟨hz,hn⟩,rfl⟩
      exact ⟨hn,⟨z,hz,rfl⟩⟩
    · rintro ⟨hn,z,hz,rfl⟩
      exact ⟨z,⟨hz,hn⟩,rfl⟩
  unfold occupiedFiberMass
  rw [he]
  exact Finset.sum_erase_add _ _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)

/-- Simultaneous FINAL-fiber comparability, constructed by minimizing a
finite occupied-fiber potential. No comparability premise is assumed.
The loss is at most twice the initial deletion; the fiber factor is 2|F|. -/
theorem exists_simultaneous_final_fibers {A B I : Type*}
    [DecidableEq A] [DecidableEq B] [DecidableEq I]
    (S R : Finset A) (F : Finset I) (f : I → A → B) (hRS : R ⊆ S) :
    ∃ Q ⊆ R, S.card-Q.card ≤ 2*(S.card-R.card) ∧
      ∀ i ∈ F, ∀ x ∈ Q, (S.filter (fun y => f i y = f i x)).card ≤
        2*F.card*(Q.filter (fun y => f i y = f i x)).card := by
  by_cases hF : F = ∅
  · refine ⟨R, Finset.Subset.refl _, ?_, ?_⟩
    · omega
    · simp [hF]
  have ht : 0 < F.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hF)
  let mass := fun Q : Finset A => ∑ i ∈ F, occupiedFiberMass S Q (f i)
  let cost := fun Q : Finset A => 2*F.card*(R.card-Q.card)+mass Q
  obtain ⟨Q,hQ,hmin⟩ := Finset.exists_min_image R.powerset cost
    ⟨R,Finset.mem_powerset.mpr (Finset.Subset.refl _)⟩
  have hQR : Q ⊆ R := Finset.mem_powerset.mp hQ
  have hQS := hQR.trans hRS
  have hcQR := Finset.card_le_card hQR
  have hcRS := Finset.card_le_card hRS
  have hcQS := Finset.card_le_card hQS
  have hbudget : 2*F.card*(R.card-Q.card)+F.card*Q.card ≤ F.card*S.card := by
    have hlo : F.card*Q.card ≤ mass Q := by
      calc
        _ = ∑ _i ∈ F, Q.card := by simp
        _ ≤ _ := Finset.sum_le_sum fun i _ => occupiedFiberMass_lower S Q (f i) hQS
    have hup : mass R ≤ F.card*S.card := by
      calc
        _ ≤ ∑ _i ∈ F, S.card := Finset.sum_le_sum fun i _ =>
          (occupiedFiberMass_mono S R S (f i) hRS).trans_eq (occupiedFiberMass_self S (f i))
        _ = _ := by simp
    have hm := hmin R (Finset.mem_powerset.mpr (Finset.Subset.refl _))
    dsimp [cost] at hm
    simp only [Nat.sub_self, Nat.mul_zero, zero_add] at hm
    omega
  have hloss : S.card-Q.card ≤ 2*(S.card-R.card) := by
    have h1 : F.card*(R.card-Q.card)+F.card*Q.card = F.card*R.card := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hcQR]
    have h2 : F.card*(S.card-R.card)+F.card*R.card = F.card*S.card := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hcRS]
    have h3 : F.card*(S.card-Q.card)+F.card*Q.card = F.card*S.card := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hcQS]
    nlinarith
  refine ⟨Q,hQR,hloss,?_⟩
  intro i hi x hx
  let P := Q.filter (fun y => f i y ≠ f i x)
  have hPQ : P ⊆ Q := Finset.filter_subset _ _
  have hPR := hPQ.trans hQR
  have hp : P.card + (Q.filter (fun y => f i y = f i x)).card = Q.card := by
    simpa [P, Nat.add_comm] using Finset.card_filter_add_card_filter_not
      (s := Q) (p := fun y => f i y = f i x)
  have hd : R.card-P.card = (R.card-Q.card)+(Q.filter (fun y => f i y = f i x)).card := by
    omega
  have hm : mass P + (S.filter (fun y => f i y = f i x)).card ≤ mass Q := by
    have hother : (∑ j ∈ F.erase i, occupiedFiberMass S P (f j)) ≤
        ∑ j ∈ F.erase i, occupiedFiberMass S Q (f j) :=
      Finset.sum_le_sum fun j _ => occupiedFiberMass_mono S P Q (f j) hPQ
    have he := occupiedFiberMass_remove S Q (f i) hx
    change occupiedFiberMass S P (f i) + _ = _ at he
    have hpSum := Finset.sum_erase_add F (fun j => occupiedFiberMass S P (f j)) hi
    have hqSum := Finset.sum_erase_add F (fun j => occupiedFiberMass S Q (f j)) hi
    dsimp [mass]
    omega
  have hcost := hmin P (Finset.mem_powerset.mpr hPR)
  dsimp [cost] at hcost
  rw [hd, Nat.mul_add] at hcost
  omega

/-- Complete finite refinement construction from an initial subset: strong
popularity followed by simultaneous FINAL-fiber stabilization. The initial
loss and every popularity round remain explicit in the bound. -/
theorem exists_popular_stable_refinement {A B D I J : Type*}
    [DecidableEq A] [DecidableEq D] [DecidableEq J]
    (S R₀ : Finset A) (T : I → Finset B) (f : I → A → B)
    (is : List I) (d : ℕ) (F : Finset J) (g : J → A → D)
    (hR₀ : R₀ ⊆ S) (hf : ∀ i ∈ is, ∀ x ∈ R₀, f i x ∈ T i) :
    ∃ Q ⊆ popularRounds T f d is R₀,
      d*(S.card-Q.card) ≤ 2*d*(S.card-R₀.card)+2*is.length*R₀.card ∧
      (∀ j ∈ F, ∀ x ∈ Q, (S.filter (fun y => g j y = g j x)).card ≤
        2*F.card*(Q.filter (fun y => g j y = g j x)).card) ∧
      (∀ i ∈ is, ∀ x ∈ Q, Q.card ≤ d*(T i).card*(S.filter (fun y => f i y = f i x)).card) := by
  let R := popularRounds T f d is R₀
  have hRR₀ : R ⊆ R₀ := popularRounds_subset T f d is R₀
  obtain ⟨Q,hQR,hloss,hfib⟩ := exists_simultaneous_final_fibers S R F g (hRR₀.trans hR₀)
  refine ⟨Q,hQR,?_,hfib,?_⟩
  · have hpop := popularRounds_loss T f d is R₀ hf
    have h1 := Finset.card_le_card hRR₀
    have h2 := Finset.card_le_card hR₀
    have he : S.card-R.card = (S.card-R₀.card)+(R₀.card-R.card) := by omega
    rw [he] at hloss
    have hm := Nat.mul_le_mul_left d hloss
    change d*(R₀.card-R.card) ≤ is.length*R₀.card at hpop
    nlinarith
  · intro i hi x hx
    have hp := popularRounds_original_fiber T f d is R₀ (hQR hx) i hi
    have hsub : R₀.filter (fun y => f i y = f i x) ⊆ S.filter (fun y => f i y = f i x) :=
      Finset.filter_subset_filter _ hR₀
    exact (Finset.card_le_card hQR).trans
      (hp.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)))

end KakeyaTwoScale
#print axioms KakeyaTwoScale.occupiedFiberMass_self
#print axioms KakeyaTwoScale.occupiedFiberMass_mono
#print axioms KakeyaTwoScale.occupiedFiberMass_lower
#print axioms KakeyaTwoScale.occupiedFiberMass_remove
#print axioms KakeyaTwoScale.exists_simultaneous_final_fibers
#print axioms KakeyaTwoScale.exists_popular_stable_refinement
