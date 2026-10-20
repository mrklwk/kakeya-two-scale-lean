module
public import KakeyaTwoScale.FiniteNarrowSelection

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
variable {J : Type*}

/-- Every later deletion inherits one common plane in each occupied cell.
The plane and its rank come from the actual original narrow pattern. -/
theorem finiteNarrowGrid_inherited_plane {n : ℕ} (G : Finset J) (b v : J → Fin n → ℝ)
    (u : J → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) (d r : ℝ)
    (I : J → Set ℝ) (hI : ∀ j∈G, I j ⊆ finiteNarrowGridHeights G b v u k d r j)
    (t : ℝ) (x : Fin n → ℝ)
    (hactive : ∃ j∈G, t∈I j ∧ gridIndex d x=gridIndex d (segmentPoint (b j) (v j) t)) :
    ∃ H : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))), Module.finrank ℝ H=k ∧
      ∀ j∈G, t∈I j → gridIndex d x=gridIndex d (segmentPoint (b j) (v j) t) →
        planeAngle H (u j)≤r := by
  let S := finiteIncidentPattern G (fun l => gridPortion (b l) (v l) d (Set.Icc (0:ℝ) 1)) (t,x)
  obtain ⟨j,hjG,hj,hcell⟩ := hactive
  have hjn := hI j hjG hj
  have he := finiteIncidentPattern_grid_cell G b v d t x (segmentPoint (b j) (v j) t) hcell
  have hn : finiteNarrowPattern u k r S := by
    have hh := hjn.2.1
    simpa only [←he] using hh
  refine ⟨finiteNarrowPatternPlane u k r S,(finiteNarrowPatternPlane_spec u k r S hn).1,?_⟩
  intro l hlG hl hc
  have hln := (hI l hlG hl).2.2
  have he' := finiteIncidentPattern_grid_cell G b v d t x (segmentPoint (b l) (v l) t) hc
  simpa only [←he'] using hln

end KakeyaTwoScale
#print axioms KakeyaTwoScale.finiteNarrowGrid_inherited_plane
