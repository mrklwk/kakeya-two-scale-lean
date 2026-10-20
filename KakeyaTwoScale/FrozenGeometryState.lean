module
public import KakeyaTwoScale.SharedChildInvariants
public import KakeyaTwoScale.GrainRecordPartition

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Concrete geometry at one normalization stage. Records and grains may
change type on a successor; original tuples and original tube IDs do not.
There is deliberately no successor oracle or analytic HRZ estimate here. -/
structure FrozenGeometryState (n k : ℕ) (T C O : Type) where
  Piece : Type
  Grain : Type
  tuples : Finset T
  parent : T → Fin k → Piece
  grain : C → Grain
  origin : Fin k → Piece → Grain
  original : Fin k → Piece → O
  base : Fin k → Piece → EuclideanSpace ℝ (Fin n)
  axis : Fin k → Piece → EuclideanSpace ℝ (Fin n)
  height : Fin k → ℕ
  ballCenter : Grain → EuclideanSpace ℝ (Fin n)
  ballRadius : ℝ

namespace FrozenGeometryState

variable {n k : ℕ} {T C O : Type}

def length (S : FrozenGeometryState n k T C O) (δ : ℝ) (j : Fin k) : ℝ := δ*2^(S.height j)

def records (S : FrozenGeometryState n k T C O) (j : Fin k) : Finset S.Piece := by
  classical
  exact S.tuples.image (fun y => S.parent y j)

def grains (S : FrozenGeometryState n k T C O) (cube : T → C) : Finset S.Grain := by
  classical
  exact S.tuples.image (S.grain ∘ cube)

def count (S : FrozenGeometryState n k T C O) (j : Fin k) : ℕ := (S.records j).card

def geometry (S : FrozenGeometryState n k T C O) (δ : ℝ) (j : Fin k) (t : S.Piece) :
    Set (EuclideanSpace ℝ (Fin n)) := flatCylinder (S.base j t) (S.axis j t) (S.length δ j) δ

/-- Every obligation here is direct finite geometry or identity, rather than
an unnamed analytic estimate. Ancestral neighborhood constraints can be carried
as explicit containment predicates when the stage is instantiated. -/
def Valid (S : FrozenGeometryState n k T C O) (Y₀ : Finset T) (cube : T → C)
    (tube : T → Fin k → O) (Q : C → Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) : Prop :=
  S.tuples ⊆ Y₀ ∧
  (∀ j t, ‖S.axis j t‖=1) ∧
  (∀ y ∈ S.tuples, ∀ j, S.original j (S.parent y j)=tube y j) ∧
  (∀ y ∈ S.tuples, ∀ j, S.origin j (S.parent y j)=S.grain (cube y)) ∧
  (∀ y ∈ S.tuples, ∀ j, (Q (cube y) ∩ S.geometry δ j (S.parent y j)).Nonempty) ∧
  (∀ j o, PairwiseDisjoint {t | t ∈ S.records j ∧ S.original j t=o} (S.geometry δ j)) ∧
  (∀ y ∈ S.tuples, Q (cube y) ⊆ ball (S.ballCenter (S.grain (cube y))) S.ballRadius ∧
    ∀ j, S.geometry δ j (S.parent y j) ⊆ ball (S.ballCenter (S.grain (cube y))) S.ballRadius)

/-- Active-family success is a test on actual finite cardinalities. Height
zero exempts a family from lower normalization, never from geometry/counting. -/
def LowerNormalized (S : FrozenGeometryState n k T C O) (cube : T → C)
    (beta : Fin k → ℝ) (q : ℝ) : Prop :=
  ∀ j, 0 < S.height j → 2*beta j*((S.grains cube).card:ℝ)^q ≤ S.count j

end FrozenGeometryState
end KakeyaTwoScale
