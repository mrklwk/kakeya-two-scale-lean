module
public import KakeyaTwoScale.WholeGridVolume

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Distinct slope fibers have mass one, including the empty family. -/
theorem fiberCardPartition_of_injOn {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (G : Finset X) (f : X → Y) (hf : Set.InjOn f (↑G : Set X)) (p : ℝ) :
    fiberCardPartition G f p = G.card := by
  have hsingle : ∀ y ∈ G.image f, (G.filter (fun x => f x=y)).card=1 := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    have he : G.filter (fun z => f z=f x)={x} := by
      ext z
      simp only [Finset.mem_filter,Finset.mem_singleton]
      exact ⟨fun h => hf h.1 hx h.2,fun h => by subst z; exact ⟨hx,rfl⟩⟩
    simp [he]
  unfold fiberCardPartition
  calc
    _ = ∑ _y ∈ G.image f, (1:ℝ) := Finset.sum_congr rfl (fun y hy => by simp [hsingle y hy])
    _ = (G.card:ℝ) := by simp [Finset.card_image_of_injOn hf]

/-- Source fixed-portion bound for translated lattice segments with distinct
slopes. The measurable portions are arbitrary; their lower length, actual
occupied volume, common progression, and rounding are all connected here.
The constant is uniform in scale, number of lines and both lattice offsets. -/
theorem lattice_portions_volume (n : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∀ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)), G.Nonempty →
      Set.InjOn Prod.snd (↑G : Set ((Fin n → ℤ) × (Fin n → ℤ))) →
      ∀ z w : Fin n → ℝ, ∀ I : ((Fin n → ℤ) × (Fin n → ℤ)) → Set ℝ,
      (∀ j ∈ G, MeasurableSet (I j)) →
      (∀ j ∈ G, I j ⊆ Set.Icc (0:ℝ) 1) →
      (∀ j ∈ G, lam ≤ volume.real (I j)) →
      C*r^n*(G.card:ℝ)^a ≤ volume.real (occupiedGridRegion G
        (fun p => latticePoint r p.1+z) (fun p => latticePoint r p.2+w) r I) := by
  obtain ⟨ell,hell,harith⟩ := arithmetic_grid_heights
  obtain ⟨c,hc,hprog⟩ := uniform_progression_heights ell hell (lam/2) (by positivity)
  obtain ⟨B,hB,hbound⟩ := harith n c hc
  have hB' : (0:ℝ) < B := by exact_mod_cast hB
  refine ⟨lam*c^a/(2*B),by positivity,?_⟩
  intro r hr G hG hinj z w I hm hs hsize
  let b := fun p : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint r p.1+z
  let v := fun p : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint r p.2+w
  let E := occupiedGridRegion G b v r I
  obtain ⟨A,hAm,hAs,hsizeA,hsmall⟩ := grid_small_sections G hG b v hr hlam I hm hs hsize
  obtain ⟨p,hpc,hsel⟩ := hprog G hG (fun j => I j ∩ A)
    (fun j hj => (hm j hj).inter hAm) (fun j hj => Set.inter_subset_left.trans (hs j hj)) hsizeA
  let S := G.filter (fun j => p ∈ progressionParameters ell (I j ∩ A))
  have hsel' : c*(G.card:ℝ) ≤ S.card := hsel
  have hSne : S.Nonempty := by
    apply Finset.card_pos.mp
    have hh : (0:ℝ) < S.card := (mul_pos hc (by exact_mod_cast hG.card_pos)).trans_le hsel'
    exact_mod_cast hh
  obtain ⟨j₀,hj₀⟩ := hSne
  have hmember (j) (hj : j ∈ S) : j ∈ G ∧ p ∈ progressionParameters ell (I j ∩ A) :=
    Finset.mem_filter.mp hj
  have hp1 : p.2 ≤ 1 :=
    (progressionParameters_subset_unit_square hell
      (Set.inter_subset_left.trans (hs j₀ (hmember j₀ hj₀).1)) (hmember j₀ hj₀).2).2.2
  obtain ⟨i,hi,hcount⟩ := hbound r p.1 p.2 hr hpc.le hp1 S z w
  rw [fiberCardPartition_of_injOn S Prod.snd (hinj.mono (Finset.filter_subset _ _))] at hcount
  let t := p.1+(i:ℝ)*p.2
  have ht (j) (hj : j ∈ S) : t ∈ I j ∩ A := (hmember j hj).2.2 ⟨i,hi⟩
  have hv := hsmall t (ht j₀ hj₀).2
  rw [occupiedGridRegion_section_real G b v hr I t] at hv
  have hsub : S ⊆ G.filter (fun j => t ∈ I j) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨(hmember j hj).1,(ht j hj).1⟩
  have hcard : ((S.image (fun j => gridIndex r (segmentPoint (b j) (v j) t))).card:ℝ) ≤
      (((G.filter (fun j => t ∈ I j)).image (fun j => gridIndex r (segmentPoint (b j) (v j) t))).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.image_subset_image hsub)
  have hlarge : c^a*(G.card:ℝ)^a ≤ (S.card:ℝ)^a := by
    rw [← Real.mul_rpow hc.le (Nat.cast_nonneg _)]
    exact Real.rpow_le_rpow (by positivity) hsel' (by norm_num [a])
  have hchain := hlarge.trans (hcount.trans (mul_le_mul_of_nonneg_left hcard hB'.le))
  have hh := mul_le_mul_of_nonneg_left hchain (pow_nonneg hr.le n)
  have hv' := mul_le_mul_of_nonneg_left hv hB'.le
  have hmain : r^n*(c^a*(G.card:ℝ)^a) ≤ (2*(B:ℝ)*volume.real E)/lam := by
    calc
      _ ≤ r^n*((B:ℝ)*(((G.filter (fun j => t ∈ I j)).image
          (fun j => gridIndex r (segmentPoint (b j) (v j) t))).card:ℝ)) := hh
      _ ≤ (B:ℝ)*(2*volume.real E/lam) := by convert hv' using 1; ring
      _ = _ := by ring
  have hmain' := (le_div_iff₀ hlam).mp hmain
  have hdiv : (r^n*(c^a*(G.card:ℝ)^a)*lam)/(2*(B:ℝ)) ≤ volume.real E :=
    (div_le_iff₀ (show 0 < 2*(B:ℝ) by positivity)).mpr (by nlinarith only [hmain'])
  convert hdiv using 1; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.fiberCardPartition_of_injOn
#print axioms KakeyaTwoScale.lattice_portions_volume
