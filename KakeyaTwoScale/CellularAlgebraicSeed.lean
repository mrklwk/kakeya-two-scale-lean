module
public import KakeyaTwoScale.CellularPhysicalIteration

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace CellularPhysicalFamily

/-- Construct the shared physical family along the supplied actual cube routes,
then construct its polynomial algebraic leaf pieces and balanced seed. No
intermediate physical family or leaf axis representation is assumed. -/
theorem exists_iterated_algebraic_seed {n k s D A J B m E : ℕ} {T C O G : Type}
    [DecidableEq T] [DecidableEq C]
    (hk : 0 < k) (W : CellularPhysicalFamily n k T O G)
    (Y : Finset T) (cube : T → C) (tube : T → Fin k → O)
    (Q : C → Set (EuclideanSpace ℝ (Fin n))) (cubes : Finset C)
    (route : ℕ → C → G) (p : ℕ → G → Fin s → MvPolynomial (Fin n) ℝ)
    (owner : ℕ → C → Fin s → Bool) (merge : ℕ → G × (Fin s → Bool) → G)
    {δ R alpha : ℝ} (hδ : 0 < δ)
    (hv : W.Valid Y cube tube Q (route 0) δ (δ*2^J))
    (hY : ∀ y ∈ Y, cube y ∈ cubes) (hQ : ∀ q ∈ cubes, IsPreconnected (Q q))
    (d : ℕ)
    (hroute : ∀ i < d, ∀ q ∈ cubes, route (i+1) q=merge i (route i q,owner i q))
    (hdeg : ∀ i < d, ∀ g, (∏ j, p i g j).totalDegree ≤ D)
    (hcell : ∀ i < d, ∀ q ∈ cubes, Q q ⊆ polynomialSignCell (p i (route i q)) (owner i q))
    (hwall : ∀ i < d, ∀ q ∈ cubes, ∀ x ∈ Q q,
      x ∉ cthickening (2*δ) (ambientPolynomialZeroSet (∏ j, p i (route i q) j)))
    (center : C → EuclideanSpace ℝ (Fin n))
    (f : G → Fin m → MvPolynomial (Fin n) ℝ) (hf : ∀ g i, (f g i).totalDegree ≤ E)
    (hradius : 0 ≤ (R+1)*δ) (hp : 0 < alpha) (hp1 : alpha ≤ 1) (hne : Y.Nonempty)
    (hbound : (Y.card:ℝ) ≤ (2:ℝ)^B)
    (hdiam : ∀ q ∈ cubes, ∀ x ∈ Q q, dist x (center q) ≤ (A:ℝ)*δ)
    (hgood : ∀ y ∈ Y, Q (cube y) ⊆ thickening (R*δ) (polynomialGrainZeroSet f (route d (cube y)))) :
    ∃ (V : FrozenGeometryState n k T C O) (lift : V.Grain → G),
      V.Valid Y cube tube Q δ ∧ V.Balanced cube cubes alpha ∧ V.tuples.Nonempty ∧
      (∀ j, V.height j ≤ J) ∧
      V.ballRadius ≤ (A+n+5:ℝ)*δ*(∑ j, (2:ℝ)^(V.height j)) ∧
      tupleCubeMass Y cube cubes alpha /
        ((((J+1)^k * (3^k*(2*(A+n+5)+1)^n) * (B+1)^(k+1):ℕ):ℝ)) ≤
        tupleCubeMass V.tuples cube cubes alpha ∧
      (∀ j, (V.count j:ℝ) ≤ 2*algebraicAxisCoverBudget n E *
        (((D+1:ℕ):ℝ)^d*((W.records Y j).card:ℝ))) ∧
      (∀ y ∈ V.tuples, lift (V.grain (cube y))=route d (cube y)) ∧
      (∀ y ∈ V.tuples, ∀ j, V.geometry δ j (V.parent y j) ⊆
        W.geometry δ (W.parent y j) ∩ thickening ((R+3)*δ) (polynomialGrainZeroSet f (route d (cube y)))) ∧
      (∀ y ∈ V.tuples, ∀ j, V.axis j (V.parent y j)=W.axis (W.parent y j)) := by
  classical
  have hmax : δ ≤ δ*2^J := le_mul_of_one_le_right hδ.le (one_le_pow₀ (by norm_num))
  obtain ⟨U,hu,hgeom,haxis,hcount⟩ := exists_iterated_cellular_family W Y cube tube Q cubes
    route p owner merge hδ hmax hv hY hQ d hroute hdeg hcell hwall
  obtain ⟨V,lift,hv',hb,hne',hh,hr,hm,hc,hl,hg,ha⟩ := exists_polynomial_algebraic_stage_seed
    hk Y cube tube Q cubes center U.parent (route d) (fun _ => U.node)
    (fun _ => U.original) (fun _ => U.base) (fun _ => U.axis) (fun _ => U.length)
    f hf hradius hδ hp hp1 hne hY hbound (fun _ => hu.1) hu.2.2.1 hu.2.2.2.1
    hu.2.2.2.2.1 hu.2.2.2.2.2 (fun _ => hu.2.1) hdiam hgood
  refine ⟨V,lift,hv',hb,hne',hh,hr,hm,?_,hl,?_,?_⟩
  · intro j
    exact (hc j).trans (mul_le_mul_of_nonneg_left (hcount j) (by positivity))
  · intro y hy j
    exact (hg y hy j).trans (Set.inter_subset_inter_left _ (hgeom y (hv'.1 hy) j))
  · intro y hy j
    exact (ha y hy j).trans (haxis y (hv'.1 hy) j)

end CellularPhysicalFamily
end KakeyaTwoScale
#print axioms KakeyaTwoScale.CellularPhysicalFamily.exists_iterated_algebraic_seed
