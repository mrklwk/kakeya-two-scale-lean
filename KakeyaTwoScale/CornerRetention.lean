module
public import KakeyaTwoScale.CornerFibers

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Actual corners built from independently selected wings at each center. -/
def wingCorners {A B D : Type*} (S : Finset A) (left : A → Finset B)
    (right : A → Finset D) : Finset (Σ _ : A, B × D) :=
  S.sigma fun j => (left j).product (right j)

def wingEdges {A B : Type*} (S : Finset A) (wing : A → Finset B) : Finset (Σ _ : A, B) :=
  S.sigma wing

theorem wingCorners_card {A B D : Type*} (S : Finset A) (left : A → Finset B)
    (right : A → Finset D) :
    (wingCorners S left right).card = ∑ j ∈ S, (left j).card * (right j).card := by
  simp [wingCorners, Finset.card_sigma, Finset.card_product]

/-- Exact accounting for deletion of left edges while independently refining
right edges. The loss is weighted by the actual surviving opposite wing. -/
theorem wingCorners_delete_identity {A B D : Type*} (S : Finset A)
    (left : A → Finset B) (right : A → Finset D) (keep : A → B → Prop) [∀ j, DecidablePred (keep j)] :
    (wingCorners S left right).card =
      (wingCorners S (fun j => (left j).filter (keep j)) right).card +
      ∑ j ∈ S, ((left j).filter (fun i => ¬ keep j i)).card * (right j).card := by
  rw [wingCorners_card, wingCorners_card, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Nat.add_mul, Finset.card_filter_add_card_filter_not]

/-- Each deleted left edge costs at most R corners. No independence of the
left deletion and the chosen right refinement is required. -/
theorem wingCorners_delete_bound {A B D : Type*} (S : Finset A)
    (left : A → Finset B) (right : A → Finset D) (keep : A → B → Prop) [∀ j, DecidablePred (keep j)]
    (R : ℕ) (hR : ∀ j ∈ S, (right j).card ≤ R) :
    (wingCorners S left right).card ≤
      (wingCorners S (fun j => (left j).filter (keep j)) right).card +
      R * (wingEdges S (fun j => (left j).filter (fun i => ¬ keep j i))).card := by
  rw [wingCorners_delete_identity S left right keep]
  apply Nat.add_le_add_left
  simp only [wingEdges, Finset.card_sigma]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  calc
    _ ≤ ((left j).filter (fun i => ¬ keep j i)).card * R := Nat.mul_le_mul_left _ (hR j hj)
    _ = _ := Nat.mul_comm _ _

/-- Retention from balanced left wings and any selected right-edge family.
This keeps the error additive, so a later choice of refinement scale must
actually dominate it before a positive retained fraction can be claimed. -/
theorem wingCorners_retention {A B D : Type*} (S : Finset A)
    (left : A → Finset B) (right : A → Finset D) (keep : A → B → Prop) [∀ j, DecidablePred (keep j)]
    (l R : ℕ) (hl : ∀ j ∈ S, l ≤ (left j).card)
    (hR : ∀ j ∈ S, (right j).card ≤ R) :
    l * (wingEdges S right).card ≤
      (wingCorners S (fun j => (left j).filter (keep j)) right).card +
      R * (wingEdges S (fun j => (left j).filter (fun i => ¬ keep j i))).card := by
  apply le_trans _ (wingCorners_delete_bound S left right keep R hR)
  simp only [wingEdges, Finset.card_sigma, wingCorners_card, Finset.mul_sum]
  exact Finset.sum_le_sum fun j hj => Nat.mul_le_mul_right _ (hl j hj)

/-- A division-free quantitative fraction bound. If the right refinement
retains 1/a of its reference edge mass and the left-edge error uses at most
half the corresponding corner budget, the corners retain the stated mass. -/
theorem wingCorners_retention_fraction {A B D : Type*} (S : Finset A)
    (left : A → Finset B) (right : A → Finset D) (keep : A → B → Prop) [∀ j, DecidablePred (keep j)]
    (l R a E : ℕ) (hl : ∀ j ∈ S, l ≤ (left j).card)
    (hR : ∀ j ∈ S, (right j).card ≤ R)
    (hretain : E ≤ a * (wingEdges S right).card)
    (herror : 2*a*R*(wingEdges S (fun j => (left j).filter (fun i => ¬ keep j i))).card ≤ l*E) :
    l*E ≤ 2*a*(wingCorners S (fun j => (left j).filter (keep j)) right).card := by
  have h := wingCorners_retention S left right keep l R hl hR
  have h1 := Nat.mul_le_mul_left l hretain
  have h2 := Nat.mul_le_mul_left a h
  nlinarith

/-- The abstract wing construction embeds directly into the actual rational
corner set when its selected edges satisfy the two projection equations. -/
theorem wingCorners_subset_arithmetic (G S : Finset ArithmeticPoint)
    (left right : ArithmeticPoint → Finset ArithmeticPoint) (r s : ℚ)
    (hS : S ⊆ G)
    (hl : ∀ j ∈ S, ∀ i ∈ left j, i ∈ G ∧ arithmeticProjection r i = arithmeticProjection r j)
    (hr : ∀ j ∈ S, ∀ k ∈ right j, k ∈ G ∧ arithmeticProjection s k = arithmeticProjection s j) :
    wingCorners S left right ⊆ arithmeticCorners G r s := by
  intro c hc
  obtain ⟨hj, hc⟩ := Finset.mem_sigma.mp hc
  obtain ⟨hi,hk⟩ := Finset.mem_product.mp hc
  have hi' := hl c.1 hj c.2.1 hi
  have hk' := hr c.1 hj c.2.2 hk
  exact (mem_arithmeticCorners G r s c).mpr
    ⟨hS hj, hi'.1, hi'.2, hk'.1, hk'.2⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.wingCorners_card
#print axioms KakeyaTwoScale.wingCorners_delete_identity
#print axioms KakeyaTwoScale.wingCorners_delete_bound
#print axioms KakeyaTwoScale.wingCorners_retention
#print axioms KakeyaTwoScale.wingCorners_retention_fraction
#print axioms KakeyaTwoScale.wingCorners_subset_arithmetic
