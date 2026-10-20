module
public import KakeyaTwoScale.ProjectionPopularity
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Finset.Prod

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- A corner consists of a middle point and two wings with the specified
projection coincidences. It is an actual finite set of triples. -/
def projectionCorners {A B D : Type*} (S : Finset A) (f : A → B) (g : A → D) :
    Finset (Σ _ : A, A × A) :=
  S.sigma fun j => (S.filter (fun i => f i = f j)).product (S.filter (fun k => g k = g j))

theorem projectionCorners_card {A B D : Type*} (S : Finset A) (f : A → B) (g : A → D) :
    (projectionCorners S f g).card =
      ∑ j ∈ S, (S.filter (fun i => f i = f j)).card * (S.filter (fun k => g k = g j)).card := by
  simp [projectionCorners, Finset.card_sigma, Finset.card_product]

/-- The corner lower bound used in Katz--Tao, proved by two actual popularity
refinements. The constant 32 is explicit; no uniformity premise is assumed. -/
theorem projectionCorners_lower {A B D : Type*} (S : Finset A) (T : Finset B) (U : Finset D)
    (f : A → B) (g : A → D) (hf : ∀ j ∈ S, f j ∈ T) (hg : ∀ j ∈ S, g j ∈ U) :
    S.card^3 ≤ 32*T.card*U.card*(projectionCorners S f g).card := by
  let P := projectionPopular S T f
  let Q := projectionPopular P U g
  have hPS : P ⊆ S := Finset.filter_subset _ _
  have hQP : Q ⊆ P := Finset.filter_subset _ _
  have hQS : Q ⊆ S := hQP.trans hPS
  have hP : S.card ≤ 2*P.card := projectionPopular_half S T f hf
  have hQ : P.card ≤ 2*Q.card := projectionPopular_half P U g (fun j hj => hg j (hPS hj))
  have hret : S.card ≤ 4*Q.card := by omega
  have hfiber (j) (hj : j ∈ Q) :
      S.card^2 ≤ 8*T.card*U.card*
        ((S.filter (fun i => f i = f j)).card * (S.filter (fun k => g k = g j)).card) := by
    have h1 := projectionPopular_fiber_lower S T f (hQP hj)
    have h2 := projectionPopular_fiber_lower P U g hj
    have hsub : P.filter (fun k => g k = g j) ⊆ S.filter (fun k => g k = g j) :=
      Finset.filter_subset_filter _ hPS
    have h3 : S.card ≤ 4*U.card*(S.filter (fun k => g k = g j)).card := by
      have hh := Finset.card_le_card hsub
      have hmul := Nat.mul_le_mul_left (2*U.card) hh
      nlinarith
    have hm := Nat.mul_le_mul h1 h3
    nlinarith
  have hsum : Q.card*S.card^2 ≤ 8*T.card*U.card*(projectionCorners S f g).card := by
    calc
      _ = ∑ _j ∈ Q, S.card^2 := by simp
      _ ≤ ∑ j ∈ Q, 8*T.card*U.card*
          ((S.filter (fun i => f i = f j)).card * (S.filter (fun k => g k = g j)).card) :=
        Finset.sum_le_sum hfiber
      _ = 8*T.card*U.card*(∑ j ∈ Q,
          (S.filter (fun i => f i = f j)).card * (S.filter (fun k => g k = g j)).card) :=
        (Finset.mul_sum ..).symm
      _ ≤ _ := by
        rw [projectionCorners_card]
        exact Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset hQS)
  calc
    S.card^3 = S.card*S.card^2 := by ring
    _ ≤ (4*Q.card)*S.card^2 := Nat.mul_le_mul_right _ hret
    _ = 4*(Q.card*S.card^2) := by ring
    _ ≤ 4*(8*T.card*U.card*(projectionCorners S f g).card) := Nat.mul_le_mul_left 4 hsum
    _ = _ := by ring
end KakeyaTwoScale
#print axioms KakeyaTwoScale.projectionCorners_card
#print axioms KakeyaTwoScale.projectionCorners_lower
