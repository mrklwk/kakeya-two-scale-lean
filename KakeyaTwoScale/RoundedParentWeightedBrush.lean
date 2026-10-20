module
public import KakeyaTwoScale.GraphParentWeightedBrush
public import KakeyaTwoScale.EnlargedParentCaps

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

theorem gridRound_norm_le {n : ℕ} (v : Fin n → ℝ) (R r : ℝ)
    (hv : ‖v‖ ≤ R) (hr : 0 < r) (hrone : r ≤ 1) : ‖gridRound r v‖ ≤ R+1 := by
  have hn := norm_le_norm_add_norm_sub v (gridRound r v)
  have hd := dist_gridRound_le hr v
  rw [dist_eq_norm] at hd
  linarith

/-- The weighted brush for the actual immutable dyadic parent level. Angular
caps, unit directions, geometric bounds and horizontal-to-Euclidean capture
conversion are all derived from the original bounded, separated graph family. -/
theorem rounded_parent_weighted_brush (n k : ℕ) (R eta C : ℝ) (shift : ℕ)
    (hR : 0 ≤ R) (heta : 0 < eta) (hC : 0 ≤ C)
    (hD : 4*(n+2:ℝ)+1 ≤ (2:ℝ)^shift) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, shift+1 ≤ q →
      ∀ {J : Type*} [DecidableEq J] (G : Finset J) (b v : J → Fin n → ℝ)
        (level : ℕ) (d : ℝ) (hd : 0 < d) (_hdr : d ≤ dyadicRadius q),
      (∀ j ∈ G, ‖b j‖ ≤ R) → (∀ j ∈ G, ‖v j‖ ≤ R) →
      (∀ j ∈ G, ∀ l ∈ G, j ≠ l → d ≤ dist (v j) (v l)) →
      let F := RoundedParentLevel.fixed G b v level (d^n) (dyadicRadius q)
        (pow_pos hd n) (Real.exp_pos _)
      ∀ S : Finset (RoundedParentLevel.Parent n), S ⊆ F.parents →
      ∀ (i : Fin (n+1)) (H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))))
        (p : ℝ × (Fin n → ℝ)) (M : ℝ),
      Module.finrank ℝ H=k+1 → 0 ≤ M →
      (∀ j ∈ S, p ∈ horizontalTube (RoundedParentLevel.parentBase (dyadicRadius q) j)
        (RoundedParentLevel.parentSlope (dyadicRadius q) j) (4*dyadicRadius q)) →
      (∀ j ∈ S, planeAngle H (graphUnitDirection i (RoundedParentLevel.parentSlope (dyadicRadius q) j)) ≤ C*dyadicRadius q) →
      (∀ j ∈ S, eta*(dyadicRadius q)^n ≤ volume.real
        (horizontalTube (RoundedParentLevel.parentBase (dyadicRadius q) j)
          (RoundedParentLevel.parentSlope (dyadicRadius q) j) (4*dyadicRadius q) ∩
          {x | M ≤ weightedOverlap F.parents (fun j => horizontalTube
            (RoundedParentLevel.parentBase (dyadicRadius q) j)
            (RoundedParentLevel.parentSlope (dyadicRadius q) j) (4*dyadicRadius q)) (fun _ => F.weight) x})) →
      c*(dyadicRadius q)^n*((dyadicRadius q)^(k+1))^theta*M*(F.weight*S.card) ≤
        (q:ℝ)*volume.real (⋃ j ∈ F.parents, euclideanTube
          (euclideanUnsplit i (0,RoundedParentLevel.parentBase (dyadicRadius q) j))
          (euclideanUnsplit i (1,RoundedParentLevel.parentSlope (dyadicRadius q) j))
          ((2:ℝ)^shift*dyadicRadius q)) := by
  let B := ((2:ℝ)^shift)^n*roundedParentCapConstant n R
  have hB : 0 < B := mul_pos (by positivity) (roundedParentCapConstant_pos n R hR)
  obtain ⟨c,hc,hbrush⟩ := graph_parent_weighted_brush n k (R+1) eta B C shift
    (by positivity) heta hB hC hD
  refine ⟨c,hc,?_⟩
  intro q hq J _ G b v level d hd hdr hb hv hsep
  dsimp only
  let F := RoundedParentLevel.fixed G b v level (d^n) (dyadicRadius q)
    (pow_pos hd n) (Real.exp_pos _)
  intro S hSG i H p M hdim hM hp ha hcapture
  have hr : 0 < dyadicRadius q := Real.exp_pos _
  have hrone : dyadicRadius q ≤ 1 := (dyadicRadius_le_half (by omega)).trans (by norm_num)
  have hsub : F.children ⊆ G := ParentLevel.selected_subset G (RoundedParentLevel.assign (dyadicRadius q) b v) level
  have hparent (j) (hj : j ∈ F.parents) : ∃ x ∈ F.children, F.assign x=j := Finset.mem_image.mp hj
  have hbP (j) (hj : j ∈ F.parents) : ‖RoundedParentLevel.parentBase (dyadicRadius q) j‖ ≤ R+1 := by
    obtain ⟨x,hx,rfl⟩ := hparent j hj
    exact gridRound_norm_le (b x) R (dyadicRadius q) (hb x (hsub hx)) hr hrone
  have hvP (j) (hj : j ∈ F.parents) : ‖RoundedParentLevel.parentSlope (dyadicRadius q) j‖ ≤ R+1 := by
    obtain ⟨x,hx,rfl⟩ := hparent j hj
    exact gridRound_norm_le (v x) R (dyadicRadius q) (hv x (hsub hx)) hr hrone
  have hcap (e : EuclideanSpace ℝ (Fin (n+1))) (he : ‖e‖=1) :=
    rounded_parent_enlarged_angular_cap G b v level d (dyadicRadius q) R ((2:ℝ)^shift)
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hd hdr hrone hR hv hsep i e he
  have hh := hbrush q hq F.parents S hSG
    (RoundedParentLevel.parentBase (dyadicRadius q)) (RoundedParentLevel.parentSlope (dyadicRadius q))
    (fun _ => F.weight) hbP hvP (fun _ _ => F.weight_pos.le) i hcap H p M hdim hM hp ha hcapture
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm (S.card:ℝ) F.weight] using hh

/-- Every represented rounded parent stays in a fixed rho-neighborhood of K,
using one original assigned child. No parent axis is extended. -/
theorem rounded_parent_capsule_union_near_set {n : ℕ} {J : Type*} [DecidableEq J]
    (G : Finset J) (b v : J → Fin n → ℝ) (level : ℕ)
    (d r A D : ℝ) (hd : 0 < d) (hr : 0 < r) (hdr : d ≤ r) (hA : 0 ≤ A)
    (i : Fin (n+1)) (K : Set (EuclideanSpace ℝ (Fin (n+1))))
    (hK : ∀ j ∈ G, ∀ t ∈ Set.Icc (0:ℝ) 1,
      euclideanUnsplit i (t,segmentPoint (b j) (v j) t) ∈ Metric.thickening (A*d) K) :
    let F := RoundedParentLevel.fixed G b v level (d^n) r (pow_pos hd n) hr
    (⋃ j ∈ F.parents, euclideanTube
      (euclideanUnsplit i (0,RoundedParentLevel.parentBase r j))
      (euclideanUnsplit i (1,RoundedParentLevel.parentSlope r j)) (D*r)) ⊆
      Metric.thickening ((D+2*(n+2:ℝ)+A)*r) K := by
  dsimp only
  let F := RoundedParentLevel.fixed G b v level (d^n) r (pow_pos hd n) hr
  intro x hx
  obtain ⟨p,hp,hx⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
  have hjs : j ∈ G := ParentLevel.selected_subset G (RoundedParentLevel.assign r b v) level hj
  exact rounded_parent_capsule_near_set_width i (b j) (v j) d r A D hr hdr hA K (hK j hjs) hx

end KakeyaTwoScale
#print axioms KakeyaTwoScale.gridRound_norm_le
#print axioms KakeyaTwoScale.rounded_parent_weighted_brush
#print axioms KakeyaTwoScale.rounded_parent_capsule_union_near_set
