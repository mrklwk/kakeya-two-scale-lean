module
public import KakeyaTwoScale.CellularPhysicalFamily
public import KakeyaTwoScale.BufferedAlgebraicSeed

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace CellularPhysicalFamily

/-- Genuine finite recursion of the constructed physical successor. Inputs
are the actual routed cube geometry of each node, not successor families.
All tuples in Y survive every prescribed cellular edge. -/
theorem exists_iterated_cellular_family {n k s D : ℕ} {T C O G : Type}
    [DecidableEq T] [DecidableEq C]
    (W : CellularPhysicalFamily n k T O G)
    (Y : Finset T) (cube : T → C) (tube : T → Fin k → O)
    (Q : C → Set (EuclideanSpace ℝ (Fin n))) (cubes : Finset C)
    (route : ℕ → C → G) (p : ℕ → G → Fin s → MvPolynomial (Fin n) ℝ)
    (owner : ℕ → C → Fin s → Bool) (merge : ℕ → G × (Fin s → Bool) → G)
    {δ maxLength : ℝ} (hδ : 0 < δ) (hmax : δ ≤ maxLength)
    (hv : W.Valid Y cube tube Q (route 0) δ maxLength)
    (hY : ∀ y ∈ Y, cube y ∈ cubes) (hQ : ∀ q ∈ cubes, IsPreconnected (Q q))
    (d : ℕ)
    (hroute : ∀ i < d, ∀ q ∈ cubes, route (i+1) q=merge i (route i q,owner i q))
    (hdeg : ∀ i < d, ∀ g, (∏ j, p i g j).totalDegree ≤ D)
    (hcell : ∀ i < d, ∀ q ∈ cubes, Q q ⊆ polynomialSignCell (p i (route i q)) (owner i q))
    (hwall : ∀ i < d, ∀ q ∈ cubes, ∀ x ∈ Q q,
      x ∉ cthickening (2*δ) (ambientPolynomialZeroSet (∏ j, p i (route i q) j))) :
    ∃ V : CellularPhysicalFamily n k T O G,
      V.Valid Y cube tube Q (route d) δ maxLength ∧
      (∀ y ∈ Y, ∀ j, V.geometry δ (V.parent y j) ⊆ W.geometry δ (W.parent y j)) ∧
      (∀ y ∈ Y, ∀ j, V.axis (V.parent y j)=W.axis (W.parent y j)) ∧
      (∀ j, ((V.records Y j).card:ℝ) ≤ ((D+1:ℕ):ℝ)^d*((W.records Y j).card:ℝ)) := by
  induction d with
  | zero =>
      exact ⟨W,hv,fun _ _ _ => Set.Subset.rfl,fun _ _ _ => rfl,by simp⟩
  | succ d ih =>
      obtain ⟨V,hv',hgeom,haxis,hcount⟩ := ih
        (fun i hi => hroute i (Nat.lt_succ_of_lt hi))
        (fun i hi => hdeg i (Nat.lt_succ_of_lt hi))
        (fun i hi => hcell i (Nat.lt_succ_of_lt hi))
        (fun i hi => hwall i (Nat.lt_succ_of_lt hi))
      obtain ⟨U,hu,hugeom,huaxis,hucount⟩ := exists_cut_successor V Y cube tube Q cubes
        (route d) (route (d+1)) (p d) (owner d) (merge d) hδ hmax hv' hY
        (hroute d (Nat.lt_succ_self d)) (hdeg d (Nat.lt_succ_self d)) hQ
        (hcell d (Nat.lt_succ_self d)) (hwall d (Nat.lt_succ_self d))
      refine ⟨U,hu,fun y hy j => (hugeom y hy j).trans (hgeom y hy j),
        fun y hy j => (huaxis y hy j).trans (haxis y hy j),?_⟩
      intro j
      calc
        _ ≤ (D+1:ℕ)*((V.records Y j).card:ℝ) := hucount j
        _ ≤ (D+1:ℕ)*(((D+1:ℕ):ℝ)^d*((W.records Y j).card:ℝ)) :=
          mul_le_mul_of_nonneg_left (hcount j) (by positivity)
        _ = ((D+1:ℕ):ℝ)^(d+1)*((W.records Y j).card:ℝ) := by rw [pow_succ]; ring

end CellularPhysicalFamily
end KakeyaTwoScale
#print axioms KakeyaTwoScale.CellularPhysicalFamily.exists_iterated_cellular_family
