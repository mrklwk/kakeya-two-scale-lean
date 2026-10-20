module
public import KakeyaTwoScale.FrozenGeometryCut
public import KakeyaTwoScale.FrozenNormalizedReset

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
namespace KakeyaTwoScale
namespace FrozenGeometryState

/-- A complete geometric cut followed by actual grain balancing, on a single
common tuple relation. The normalized count reset is DERIVED from old-origin
fibers, not included as a state axiom or successor assumption. -/
theorem exists_balanced_cut {n k A B : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    (S : FrozenGeometryState n k T C O) (Y₀ : Finset T) (cube : T → C)
    (tube : T → Fin k → O) (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (cubes : Finset C) (center : C → EuclideanSpace ℝ (Fin n))
    {δ r p q : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hδr : δ ≤ r)
    (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hv : S.Valid Y₀ cube tube Q δ) (hb : S.Balanced cube cubes p)
    (hne : S.tuples.Nonempty) (hcubes : ∀ y ∈ S.tuples, cube y ∈ cubes)
    (hbound : (S.tuples.card:ℝ) ≤ (2:ℝ)^B)
    (H : Fin k → ℕ) (hH : ∀ j, H j ≤ S.height j)
    (hHr : ∀ j, δ*2^(H j) ≤ 2*r)
    (hQ : ∀ c ∈ cubes, ∀ x ∈ Q c, dist x (center c) ≤ (A:ℝ)*r) :
    ∃ S' : FrozenGeometryState n k T C O,
      S'.Valid Y₀ cube tube Q δ ∧ S'.Balanced cube cubes p ∧ S'.tuples.Nonempty ∧
      S'.tuples ⊆ S.tuples ∧ S'.height=H ∧ S'.ballRadius=(A+n+5:ℝ)*r ∧
      tupleCubeMass S.tuples cube cubes p /
        ((3^k*(2*(A+n+5)+1)^n*(B+1)^(k+1):ℕ):ℝ) ≤ tupleCubeMass S'.tuples cube cubes p ∧
      (∀ j, (S'.count j:ℝ) ≤ 2*(S.length δ j/(δ*2^(H j)))*S.count j*
        (((S'.grains cube).card:ℝ)/(S.grains cube).card)^q) ∧
      (∀ y ∈ S'.tuples, ∀ j, S'.geometry δ j (S'.parent y j) ⊆ S.geometry δ j (S.parent y j)) ∧
      (∀ y ∈ S'.tuples, ∀ j, S'.axis j (S'.parent y j)=S.axis j (S.parent y j)) ∧
      (∃ lift : S'.Grain → S.Grain, ∀ y ∈ S'.tuples, lift (S'.grain (cube y))=S.grain (cube y)) := by
  classical
  obtain ⟨U,lift,hUv,hUS,hUH,hUr,hUlift,hUmass,hUcount,hUfiber,hUgeom,hUaxis⟩ :=
    exists_geometric_cut S Y₀ cube tube Q cubes center hδ hr hδr hp hp1 hv hne hcubes H hH hHr hQ
  have hUne : U.tuples.Nonempty := by
    obtain ⟨y,hy⟩ := hne
    have hm := tuple_mass_one_le S.tuples cube cubes hp.le hy (hcubes y hy)
    have hd : (0:ℝ) < ((3^k*(2*(A+n+5)+1)^n:ℕ):ℝ) := by positivity
    have hh := (div_pos (by linarith : 0 < tupleCubeMass S.tuples cube cubes p) hd).trans_le hUmass
    exact Finset.card_pos.mp (by exact_mod_cast hh.trans_le (tuple_mass_le_card U.tuples cube cubes hp hp1))
  obtain ⟨V,forget,hVv,hVb,hVne,hVU,hVH,hVr,hVlift,hVmass,hVcount,hVfiber,hVgeom,hVaxis⟩ :=
    exists_balanced_state U Y₀ cube tube Q cubes hp hp1 hUv hUne
      (fun y hy => hcubes y (hUS hy))
      ((show (U.tuples.card:ℝ) ≤ S.tuples.card by exact_mod_cast Finset.card_le_card hUS).trans hbound)
  refine ⟨V,hVv,hVb,hVne,hVU.trans hUS,hVH.trans hUH,hVr.trans hUr,?_,?_,?_,?_,?_⟩
  · have hh := (div_le_div_of_nonneg_right hUmass (by positivity :
        (0:ℝ) ≤ (((B+1)^(k+1):ℕ):ℝ))).trans hVmass
    simpa only [div_div,Nat.cast_mul] using hh
  · intro j
    apply actual_normalized_reset S V cube cubes (lift ∘ forget) hb hne hq hq1 hVv.2.2.2.1
      (show 0 ≤ S.length δ j/(δ*2^(H j)) by dsimp [length]; positivity) j
    · exact (show (V.count j:ℝ) ≤ U.count j by exact_mod_cast hVcount j).trans (hUcount j)
    · intro g
      have hh := hVfiber S.Grain lift g j
      exact (show (grainRecordCount V.tuples cube ((lift ∘ forget) ∘ V.grain) (fun y => V.parent y j) g:ℝ) ≤
          grainRecordCount U.tuples cube (lift ∘ U.grain) (fun y => U.parent y j) g by exact_mod_cast hh).trans (hUfiber g j)
  · intro y hy j
    rw [hVgeom y hy j]
    exact hUgeom y (hVU hy) j

  · intro y hy j
    exact (hVaxis y hy j).trans (hUaxis y (hVU hy) j)

  · exact ⟨lift ∘ forget,fun y hy => (congrArg lift (hVlift y hy)).trans (hUlift y (hVU hy))⟩

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.exists_balanced_cut
