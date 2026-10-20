module
public import KakeyaTwoScale.RetainedParentGeometry

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- The exact retained-parent brush assembly. A per-parent cell cap and thin
plane concentration, after arbitrary prior measurable narrowing, supply all
remaining geometric hypotheses. The actual safe/long portions, represented
parent family, weights and original high set are constructed and retained. -/
theorem retained_parent_brush (n k : ℕ) (R eta C : ℝ) (shift : ℕ)
    (hR : 0 ≤ R) (heta : 0 < eta) (hC : 0 ≤ C)
    (hD : 4*(n+2:ℝ)+1 ≤ (2:ℝ)^shift) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, shift+1 ≤ q →
      ∀ {X : Type*} [DecidableEq X] (G : Finset X) (b v : X → Fin n → ℝ)
        (level : ℕ) (d : ℝ) (hd : 0 < d) (_hdr : d ≤ dyadicRadius q),
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖v j‖ ≤ R) →
      (∀ j ∈ G, ∀ l ∈ G, j ≠ l → d ≤ dist (v j) (v l)) →
      let r := dyadicRadius q
      let F := RoundedParentLevel.fixed G b v level (d^n) r (pow_pos hd n) (Real.exp_pos _)
      ∀ (I : X → Set ℝ) (M bound : ℝ), 0 ≤ M → 0 < bound →
      (∀ j ∈ F.children, MeasurableSet (I j)) →
      (∀ j ∈ F.children, I j ⊆ Set.Icc (0:ℝ) 1) →
      ∀ (t : ℝ) (x : Fin n → ℝ) (i : Fin (n+1))
        (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1)))), Module.finrank ℝ H=k+1 →
      (∀ p ∈ F.parents, ((F.children.filter (fun j => t ∈ I j ∧
        gridIndex d (segmentPoint (b j) (v j) t)=gridIndex d x ∧ F.assign j=p)).card:ℝ) ≤ bound) →
      (∀ j ∈ F.children, t ∈ I j → gridIndex d (segmentPoint (b j) (v j) t)=gridIndex d x →
        planeAngle H (graphUnitDirection i (v j)) ≤ C*r) →
      let J := F.longPortions volume (fun j => safeRetainedHeights F.parents
        (RoundedParentLevel.parentBase r) (RoundedParentLevel.parentSlope r)
        (b j) (v j) F.weight r M (I j)) eta
      let A := F.children.filter (fun j => t ∈ J j ∧
        gridIndex d (segmentPoint (b j) (v j) t)=gridIndex d x)
      c*r^n*(r^(k+1))^theta*M*(F.weight*(A.card:ℝ)/bound) ≤
        (q:ℝ)*volume.real (⋃ j ∈ F.parents, euclideanTube
          (euclideanUnsplit i (0,RoundedParentLevel.parentBase r j))
          (euclideanUnsplit i (1,RoundedParentLevel.parentSlope r j)) ((2:ℝ)^shift*r)) := by
  let C' := (Real.pi/2)*(C+2*(n+2:ℝ))
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  obtain ⟨c,hc,hbrush⟩ := rounded_parent_weighted_brush n k R eta C' shift hR heta hC' hD
  refine ⟨c,hc,?_⟩
  intro q hq X _ G b v level d hd hdr hb hv hsep
  dsimp only
  let r := dyadicRadius q
  let F := RoundedParentLevel.fixed G b v level (d^n) r (pow_pos hd n) (Real.exp_pos _)
  intro I M bound hM hbound hI hunit t x i H hdim hcap hplane
  let J := F.longPortions volume (fun j => safeRetainedHeights F.parents
    (RoundedParentLevel.parentBase r) (RoundedParentLevel.parentSlope r)
    (b j) (v j) F.weight r M (I j)) eta
  let A := F.children.filter (fun j => t ∈ J j ∧
    gridIndex d (segmentPoint (b j) (v j) t)=gridIndex d x)
  let parents := A.image F.assign
  have hbr (j) (_hj : j ∈ F.children) : RoundedParentLevel.parentBase r (F.assign j)=gridRound r (b j) := rfl
  have hvr (j) (_hj : j ∈ F.children) : RoundedParentLevel.parentSlope r (F.assign j)=gridRound r (v j) := rfl
  have hg := retained_cell_parent_geometry F b v (RoundedParentLevel.parentBase r)
    (RoundedParentLevel.parentSlope r) I d r M eta bound C hd hdr heta.le hbound hI hunit
    hbr hvr t x i H hcap hplane
  change parents ⊆ F.parents ∧ F.weight*(A.card:ℝ)/bound ≤ F.weight*parents.card ∧ _ at hg
  obtain ⟨hPs,hweight,hpoint,hangle,hcapture⟩ := hg
  have hh := hbrush q hq G b v level d hd hdr hb hv hsep parents hPs i H (t,x) M
    hdim hM hpoint hangle hcapture
  have hfactor : 0 ≤ c*r^n*(r^(k+1))^theta*M := by
    have hr : 0 < r := Real.exp_pos _
    positivity
  exact (mul_le_mul_of_nonneg_left hweight hfactor).trans hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.retained_parent_brush
