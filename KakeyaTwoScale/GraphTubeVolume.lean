module
public import KakeyaTwoScale.PortionGridVolume

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale
open Classical

theorem horizontalTube_finite {n : ℕ} (b v : Fin n → ℝ) (r : ℝ) :
    volume (horizontalTube b v r) ≠ ⊤ := by
  have hsub : horizontalTube b v r ⊆ Set.Icc (0:ℝ) 1 ×ˢ
      Metric.closedBall (0:Fin n → ℝ) (r+‖b‖+‖v‖) := by
    intro x hx
    refine ⟨hx.1,?_⟩
    change dist x.2 0 ≤ _
    have ht : |x.1| ≤ 1 := by rw [abs_of_nonneg hx.1.1]; exact hx.1.2
    have hv : ‖x.1 • v‖ ≤ ‖v‖ := by
      rw [norm_smul,Real.norm_eq_abs]
      nlinarith [norm_nonneg v]
    have ha : ‖segmentPoint b v x.1‖ ≤ ‖b‖+‖v‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl hv)
    have hh := dist_triangle x.2 (segmentPoint b v x.1) 0
    simp only [dist_zero_right] at hh ⊢
    linarith [hx.2]
  exact measure_ne_top_of_subset hsub
    (isCompact_Icc.prod (isCompact_closedBall _ _)).measure_ne_top

theorem horizontalTube_union_finite {n : ℕ} {J : Type*} (G : Finset J)
    (b v : J → Fin n → ℝ) (r : ℝ) :
    volume (⋃ j ∈ G, horizontalTube (b j) (v j) r) ≠ ⊤ := by
  exact measure_biUnion_ne_top G.finite_toSet (fun j _ => horizontalTube_finite (b j) (v j) r)

/-- Ordinary graph tubes with a common unit-height interval. Intercepts and
slopes are arbitrary real vectors, not lattice points. Slope separation is
in the horizontal sup metric; rotation/angular and Euclidean-cylinder
normalizations are separate obligations. -/
theorem separated_graph_tubes_volume (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ {J : Type*} (G : Finset J), G.Nonempty →
      ∀ b v : J → Fin n → ℝ,
      (∀ j ∈ G, ∀ k ∈ G, j ≠ k → r ≤ dist (v j) (v k)) →
      C*r^n*(G.card:ℝ)^a ≤ volume.real (⋃ j ∈ G, horizontalTube (b j) (v j) r) := by
  obtain ⟨C,hC,hvol⟩ := whole_lattice_segments_volume n
  refine ⟨C/(4:ℝ)^n,by positivity,?_⟩
  intro r hr J G hG b v hsep
  let d := r/4
  have hd : 0 < d := by dsimp [d]; positivity
  let e := fun j => (gridIndex d (b j),gridIndex d (v j))
  have hslope : Set.InjOn (fun j => gridIndex d (v j)) (↑G : Set J) := by
    intro j hj k hk he
    dsimp only at he
    by_contra hn
    have hh := gridCell_dist_le hd.le (mem_own_gridCell hd (v j))
      (show v k ∈ gridCell d (gridIndex d (v j)) by rw [he]; exact mem_own_gridCell hd _)
    have hh' := hsep j hj k hk hn
    dsimp [d] at hh
    linarith
  have he : Set.InjOn e (↑G : Set J) := by
    intro j hj k hk heq
    exact hslope hj hk (congrArg Prod.snd heq)
  have hEslope : Set.InjOn Prod.snd (↑(G.image e) : Set ((Fin n → ℤ) × (Fin n → ℤ))) := by
    intro p hp q hq heq
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hq
    have hjk := hslope hj hk heq
    rw [hjk]
  have hh := hvol d hd (G.image e) (hG.image e) 0 0
  rw [fiberCardPartition_of_injOn _ Prod.snd hEslope,Finset.card_image_of_injOn he] at hh
  have hsub : occupiedGridRegion (G.image e)
      (fun p => latticePoint d p.1+0) (fun p => latticePoint d p.2+0) d
      (fun _ => Set.Icc (0:ℝ) 1) ⊆ ⋃ j ∈ G, horizontalTube (b j) (v j) r := by
    intro x hx
    obtain ⟨p,hp,ht,hcell⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
    have hpoint : x.2 ∈ gridCell d (gridIndex d
        (segmentPoint (gridRound d (b j)) (gridRound d (v j)) x.1)) := by
      apply (mem_gridCell_iff hd _ _).mpr
      have hround (y : Fin n → ℝ) : latticePoint d (gridIndex d y)=gridRound d y := rfl
      simpa only [e,add_zero,hround] using hcell
    have hnear := gridCell_dist_le hd.le hpoint (mem_own_gridCell hd _)
    have haxis := segmentPoint_dist_le (gridRound d (b j)) (gridRound d (v j)) (b j) (v j)
      d x.1 ht (by simpa [dist_comm] using dist_gridRound_le hd (b j))
      (by simpa [dist_comm] using dist_gridRound_le hd (v j))
    apply Set.mem_iUnion₂.mpr
    refine ⟨j,hj,ht,?_⟩
    have htri := dist_triangle x.2
      (segmentPoint (gridRound d (b j)) (gridRound d (v j)) x.1) (segmentPoint (b j) (v j) x.1)
    dsimp [d] at hnear haxis
    change dist x.2 (segmentPoint (b j) (v j) x.1) ≤ r
    linarith
  have hmono := measureReal_mono hsub (horizontalTube_union_finite G b v r)
  have hfinal := hh.trans hmono
  convert hfinal using 1
  dsimp [d]
  rw [div_pow]
  ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.horizontalTube_finite
#print axioms KakeyaTwoScale.horizontalTube_union_finite
#print axioms KakeyaTwoScale.separated_graph_tubes_volume
