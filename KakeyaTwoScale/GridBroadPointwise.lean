module
public import KakeyaTwoScale.BroadPointwise
public import KakeyaTwoScale.GraphParentCapsule
public import KakeyaTwoScale.NarrowSelectionMass

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

/-- An entire incident fine cell lies in the enlarged capsule around its
original finite graph segment, at the same height parameter. -/
theorem gridPortion_subset_graph_capsule {n : ℕ} (i : Fin (n+1))
    (b v : Fin n → ℝ) (d D : ℝ) (hd : 0 < d) (hD : 4*(n+2:ℝ)+1 ≤ D) :
    euclideanUnsplit i '' gridPortion b v d (Set.Icc (0:ℝ) 1) ⊆
      euclideanTube (euclideanUnsplit i (0,b)) (euclideanUnsplit i (1,v)) (D*d) := by
  rintro z ⟨x,hx,rfl⟩
  apply horizontal_parent_subset_capsule_width i b v d D hd hD
  refine ⟨x,⟨hx.1,?_⟩,rfl⟩
  have he : gridRound d x.2=gridRound d (segmentPoint b v x.1) := by
    unfold gridRound
    rw [hx.2]
  have ha := dist_gridRound_le hd x.2
  have hb := dist_gridRound_le hd (segmentPoint b v x.1)
  have ht := dist_triangle x.2 (gridRound d x.2) (segmentPoint b v x.1)
  rw [he,dist_comm (gridRound d (segmentPoint b v x.1))] at ht
  rw [he] at ha
  change dist x.2 (segmentPoint b v x.1) ≤ 4*d
  linarith

/-- The source broad locus controls actual full-family graph-capsule
multiplicity through constructed tuples. No cell-containment, tuple-count,
or wedge lower bound is assumed. -/
theorem grid_broad_multilinear_pointwise {n N k : ℕ}
    (b v : Fin N → Fin n → ℝ) (i : Fin (n+1)) (d rho D B : ℝ)
    (hd : 0 < d) (hrho : 0 < rho) (hD : 4*(n+2:ℝ)+1 ≤ D)
    (hB : 0 < B) (hk : 1 ≤ k) (hkn : k ≤ n+1)
    (x : ℝ × (Fin n → ℝ))
    (hx : x ∈ gridBroadRegion b v (fun j => graphUnitDirection i (v j)) (k-1) d rho) :
    broadCoefficient (k-1) B*rho^(((k:ℝ)-1)/B)*
        gridMultiplicity Finset.univ b v d x ≤
      multilinearKakeyaFunction k (fun j => graphUnitDirection i (v j))
        (fun j => euclideanTube (euclideanUnsplit i (0,b j))
          (euclideanUnsplit i (1,v j)) (D*d)) B (euclideanUnsplit i x) := by
  let G := incidentPattern (fun j => gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1)) x
  have hcard : gridMultiplicity Finset.univ b v d x=(G.card:ℝ) := by
    rw [gridMultiplicity,membershipCount_eq_card]
    rfl
  rw [hcard]
  apply broad_multilinear_pointwise_k G (fun j => graphUnitDirection i (v j))
    _ rho B hrho hB hk hkn (fun j _ => graphUnitDirection_norm i _) ?_ _ ?_
  · intro H hdim
    have hn : ¬ G.card ≤ 2*(G.filter (fun j => planeAngle H (graphUnitDirection i (v j)) ≤ rho)).card :=
      fun h => hx ⟨H,hdim,h⟩
    have hh : (2:ℝ)*((G.filter (fun j => planeAngle H (graphUnitDirection i (v j)) ≤ rho)).card:ℝ)<G.card := by
      exact_mod_cast Nat.lt_of_not_ge hn
    linarith
  · intro j hj
    have hh : x∈gridPortion (b j) (v j) d (Set.Icc (0:ℝ) 1) := (Finset.mem_filter.mp hj).2
    exact gridPortion_subset_graph_capsule i (b j) (v j) d D hd hD ⟨x,hh,rfl⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.gridPortion_subset_graph_capsule
#print axioms KakeyaTwoScale.grid_broad_multilinear_pointwise
