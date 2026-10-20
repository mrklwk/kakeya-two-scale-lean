module
public import KakeyaTwoScale.AlgebraicStageSeed
public import KakeyaTwoScale.AlgebraicAxisIntervals

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

def polynomialGrainZeroSet {n m : ℕ} {G : Type}
    (f : G → Fin m → MvPolynomial (Fin n) ℝ) (g : G) :
    Set (EuclideanSpace ℝ (Fin n)) := {z | ∀ j, MvPolynomial.eval (fun i => z i) (f g j)=0}

def algebraicAxisCoverBudget (n D : ℕ) : ℕ := (2*(max (2*D) 4)+1)^(n+2)

/-- The algebraic stage seed now takes polynomial equations, not interval
covers. All covers and their uniform complexity are constructed internally.
Incoming physical-family and cube hypotheses remain explicit. -/
theorem exists_polynomial_algebraic_stage_seed {n k A J B m D : ℕ} {T C O P G : Type}
    [DecidableEq T] [DecidableEq C] (hk : 0 < k)
    (Y : Finset T) (cube : T → C) (tube : T → Fin k → O)
    (Q : C → Set (EuclideanSpace ℝ (Fin n))) (cubes : Finset C)
    (center : C → EuclideanSpace ℝ (Fin n))
    (parent : T → Fin k → P) (grain : C → G) (origin : Fin k → P → G)
    (original : Fin k → P → O) (b u : Fin k → P → EuclideanSpace ℝ (Fin n))
    (L : Fin k → P → ℝ) (f : G → Fin m → MvPolynomial (Fin n) ℝ)
    (hf : ∀ g j, (f g j).totalDegree ≤ D) {δ p R : ℝ}
    (hradius : 0 ≤ (R+1)*δ)
    (hδ : 0 < δ) (hp : 0 < p) (hp1 : p ≤ 1) (hne : Y.Nonempty)
    (hcubes : ∀ y ∈ Y, cube y ∈ cubes) (hbound : (Y.card:ℝ) ≤ (2:ℝ)^B)
    (hu : ∀ j t, ‖u j t‖=1)
    (horiginal : ∀ y ∈ Y, ∀ j, original j (parent y j)=tube y j)
    (horigin : ∀ y ∈ Y, ∀ j, origin j (parent y j)=grain (cube y))
    (hinc : ∀ y ∈ Y, ∀ j, (Q (cube y) ∩
      flatCylinder (b j (parent y j)) (u j (parent y j)) (L j (parent y j)) δ).Nonempty)
    (hdis : ∀ j o, PairwiseDisjoint
      {t | t ∈ Y.image (fun y => parent y j) ∧ original j t=o}
      (fun t => flatCylinder (b j t) (u j t) (L j t) δ))
    (hlen : ∀ j t, δ ≤ L j t ∧ L j t ≤ δ*2^J)
    (hQ : ∀ q ∈ cubes, ∀ x ∈ Q q, dist x (center q) ≤ (A:ℝ)*δ)
    (hgood : ∀ y ∈ Y, Q (cube y) ⊆ thickening (R*δ) (polynomialGrainZeroSet f (grain (cube y))))
 :
    ∃ (V : FrozenGeometryState n k T C O) (lift : V.Grain → G),
      V.Valid Y cube tube Q δ ∧ V.Balanced cube cubes p ∧ V.tuples.Nonempty ∧
      (∀ j, V.height j ≤ J) ∧
      V.ballRadius ≤ (A+n+5:ℝ)*δ*(∑ j, (2:ℝ)^(V.height j)) ∧
      tupleCubeMass Y cube cubes p /
        ((((J+1)^k * (3^k*(2*(A+n+5)+1)^n) * (B+1)^(k+1):ℕ):ℝ)) ≤
        tupleCubeMass V.tuples cube cubes p ∧
      (∀ j, (V.count j:ℝ) ≤ 2*algebraicAxisCoverBudget n D*((Y.image (fun y => parent y j)).card:ℝ)) ∧
      (∀ y ∈ V.tuples, lift (V.grain (cube y))=grain (cube y)) ∧
      (∀ y ∈ V.tuples, ∀ j, V.geometry δ j (V.parent y j) ⊆
        flatCylinder (b j (parent y j)) (u j (parent y j)) (L j (parent y j)) δ ∩
          thickening ((R+3)*δ) (polynomialGrainZeroSet f (grain (cube y)))) ∧
      (∀ y ∈ V.tuples, ∀ j, V.axis j (V.parent y j)=u j (parent y j)) := by
  classical
  have hex (j : Fin k) (t : P) := exists_algebraic_axis_intervals
    (f (origin j t)) (hf (origin j t)) (b j t) (u j t) hradius
    (lt_of_lt_of_le hδ (hlen j t).1)
  choose S hcard hS hequiv using hex
  have hsafe : ∀ j t a, a ∈ S j t → ∀ s ∈ Icc a.1 a.2,
      ∃ z ∈ polynomialGrainZeroSet f (origin j t),
        dist (b j t+s • u j t) z ≤ (R+1)*δ := by
    intro j t a ha s hs
    exact ((hequiv j t s).mpr ⟨a,ha,hs⟩).2
  have hcover : ∀ j t s, s ∈ Ioo (0:ℝ) (L j t) →
      (∃ z ∈ polynomialGrainZeroSet f (origin j t),
        dist (b j t+s • u j t) z ≤ (R+1)*δ) →
        ∃ a ∈ S j t, s ∈ Icc a.1 a.2 := by
    intro j t s hs hz
    exact (hequiv j t s).mp ⟨⟨hs.1.le,hs.2.le⟩,hz⟩
  exact exists_algebraic_stage_seed (K := algebraicAxisCoverBudget n D)
    hk Y cube tube Q cubes center parent grain origin original b u L
    (polynomialGrainZeroSet f) S hδ hp hp1 hne hcubes hbound hu horiginal horigin
    hinc hdis hlen hQ hgood hcard hS hsafe hcover

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_polynomial_algebraic_stage_seed
