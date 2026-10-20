module
public import KakeyaTwoScale.GridBroadIntegral
public import KakeyaTwoScale.FiniteNarrowMass

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale
open Classical
variable {J : Type*}

def finiteFamilyIndex (G : Finset J) (a : Fin G.card) : J :=
  (G.equivFin.symm a).val

theorem finiteFamilyIndex_filter_card (G : Finset J) (P : J → Prop) :
    (Finset.univ.filter (fun a : Fin G.card => P (finiteFamilyIndex G a))).card =
      (G.filter P).card := by
  apply Finset.card_bij (fun a _ => finiteFamilyIndex G a)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨(G.equivFin.symm a).property,(Finset.mem_filter.mp ha).2⟩
  · intro a ha b hb he
    apply G.equivFin.symm.injective
    exact Subtype.ext he
  · intro j hj
    refine ⟨G.equivFin ⟨j,(Finset.mem_filter.mp hj).1⟩,?_,?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,by simpa [finiteFamilyIndex] using (Finset.mem_filter.mp hj).2⟩
    · simp [finiteFamilyIndex]

theorem finiteFamilyIndex_incident_card {X : Type*} (G : Finset J) (T : J → Set X) (x : X) :
    (incidentPattern (fun a => T (finiteFamilyIndex G a)) x).card =
      (finiteIncidentPattern G T x).card :=
  finiteFamilyIndex_filter_card G (fun j => x ∈ T j)

theorem finiteFamilyIndex_cap_card {X : Type*} (G : Finset J) (T : J → Set X)
    (x : X) (P : J → Prop) :
    ((incidentPattern (fun a => T (finiteFamilyIndex G a)) x).filter
      (fun a => P (finiteFamilyIndex G a))).card =
      ((finiteIncidentPattern G T x).filter P).card := by
  classical
  convert finiteFamilyIndex_filter_card G (fun j => x ∈ T j ∧ P j) using 1 <;>
    simp only [incidentPattern,finiteIncidentPattern,Finset.filter_filter]
  all_goals
    congr 1
    ext a
    simp

theorem finiteFamilyIndex_gridMultiplicity {n : ℕ} (G : Finset J)
    (b v : J → Fin n → ℝ) (d : ℝ) :
    gridMultiplicity Finset.univ (b ∘ finiteFamilyIndex G) (v ∘ finiteFamilyIndex G) d =
      gridMultiplicity G b v d := by
  funext x
  simp only [gridMultiplicity,membershipCount_eq_card,Function.comp_apply]
  congr 1
  convert finiteFamilyIndex_filter_card G (fun j => x ∈ gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) using 1

theorem finiteFamilyIndex_broadRegion [Countable J] {n : ℕ} (G : Finset J)
    (b v : J → Fin n → ℝ) (u : J → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) (d r : ℝ) :
    gridBroadRegion (b ∘ finiteFamilyIndex G) (v ∘ finiteFamilyIndex G)
      (u ∘ finiteFamilyIndex G) k d r = finiteGridBroadRegion G b v u k d r := by
  ext x
  change (¬ ∃ H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))),
    Module.finrank ℝ H = k ∧ _) ↔ (¬ ∃ H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))),
    Module.finrank ℝ H = k ∧ _)
  apply not_congr
  apply exists_congr
  intro H
  simp only [Function.comp_apply]
  have hcard := finiteFamilyIndex_incident_card G
    (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) x
  have hcap := finiteFamilyIndex_cap_card G
    (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) x
    (fun j => planeAngle H (u j) ≤ r)
  simp only [incidentPattern,finiteIncidentPattern,Finset.filter_filter] at hcard hcap ⊢
  rw [hcard,hcap]


/-- The integrated broad estimate on the literal finite family, with only
an explicit norm upper bound on its canonical finite reindexing. -/
theorem finite_grid_broad_integral_of_norm_bound [Countable J] {n k : ℕ}
    (G : Finset J) (b v : J → Fin n → ℝ) (i : Fin (n+1)) (d rho D B A : ℝ)
    (hd : 0 < d) (hrho : 0 < rho) (hD : 4*(n+2:ℝ)+1 ≤ D)
    (hB : 1 < B) (hA : 0 ≤ A) (hk : 1 ≤ k) (hkn : k ≤ n+1)
    (hnorm : eLpNorm (multilinearKakeyaFunction k
      (fun a => graphUnitDirection i (v (finiteFamilyIndex G a)))
      (fun a => euclideanTube (euclideanUnsplit i (0,b (finiteFamilyIndex G a)))
        (euclideanUnsplit i (1,v (finiteFamilyIndex G a))) (D*d)) B)
      (ENNReal.ofReal (B/(B-1))) volume ≤ ENNReal.ofReal A) :
    let S := finiteGridBroadRegion G b v (fun j => graphUnitDirection i (v j)) (k-1) d rho
    Integrable (gridMultiplicity G b v d) (volume.restrict S) ∧
      (∫ x in S, gridMultiplicity G b v d x) ≤
        A*(volume.real S)^(1/B)/(broadCoefficient (k-1) B*rho^(((k:ℝ)-1)/B)) := by
  have h := grid_broad_integral_of_norm_bound
    (b ∘ finiteFamilyIndex G) (v ∘ finiteFamilyIndex G) i d rho D B A
    hd hrho hD hB hA hk hkn hnorm
  rw [finiteFamilyIndex_gridMultiplicity] at h
  have hs := finiteFamilyIndex_broadRegion G b v (fun j => graphUnitDirection i (v j)) (k-1) d rho
  change gridBroadRegion (b ∘ finiteFamilyIndex G) (v ∘ finiteFamilyIndex G)
    (fun j => graphUnitDirection i ((v ∘ finiteFamilyIndex G) j)) (k-1) d rho = _ at hs
  simpa only [hs] using h

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finiteFamilyIndex_filter_card
#print axioms KakeyaTwoScale.finiteFamilyIndex_broadRegion
#print axioms KakeyaTwoScale.finite_grid_broad_integral_of_norm_bound
