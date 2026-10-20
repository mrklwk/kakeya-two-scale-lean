module
public import KakeyaTwoScale.ArithmeticGridHeights
public import KakeyaTwoScale.GridSectionSelection
public import KakeyaTwoScale.UniformProgressionHeights

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Single-set form of the proved simultaneous progression theorem. -/
theorem dense_set_progression (ell : ℕ) (hell : 2 ≤ ell) (lam : ℝ) (hlam : 0 < lam) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : Set ℝ, MeasurableSet A → A ⊆ Set.Icc (0:ℝ) 1 →
      lam ≤ volume.real A → ∃ p : ℝ × ℝ, c ≤ p.2 ∧ p.2 ≤ 1 ∧
        p ∈ progressionParameters ell A := by
  obtain ⟨c,hc,hsel⟩ := uniform_progression_heights ell hell lam hlam
  refine ⟨c,hc,?_⟩
  intro A hm hs hsize
  obtain ⟨p,hp,hcard⟩ := hsel ({()} : Finset Unit) (by simp) (fun _ => A)
    (fun _ _ => hm) (fun _ _ => hs) (fun _ _ => hsize)
  simp only [Finset.card_singleton,Nat.cast_one,mul_one] at hcard
  have hpos : 0 < (({()} : Finset Unit).filter
      (fun _ => p ∈ progressionParameters ell A)).card := by
    have hh : (0:ℝ) < (({()} : Finset Unit).filter
        (fun _ => p ∈ progressionParameters ell A)).card := by simpa using hc.trans_le hcard
    exact_mod_cast hh
  obtain ⟨_,hj⟩ := Finset.card_pos.mp hpos
  have hprog := (Finset.mem_filter.mp hj).2
  exact ⟨p,hp.le,(progressionParameters_subset_unit_square hell hs hprog).2.2,hprog⟩

/-- Source whole-segment arithmetic volume bound, proved for actual unions
of horizontal grid cells. The positive constant precedes the scale, graph,
and both lattice translations; no arithmetic, progression, packing, or
volume hypothesis remains. The geometry here uses the horizontal sup grid. -/
theorem whole_lattice_segments_volume (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∀ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)), G.Nonempty →
      ∀ z w : Fin n → ℝ,
      C*r^n*(fiberCardPartition G Prod.snd (theta/a))^a ≤
        volume.real (occupiedGridRegion G
          (fun p => latticePoint r p.1+z) (fun p => latticePoint r p.2+w) r
          (fun _ => Set.Icc (0:ℝ) 1)) := by
  obtain ⟨ell,hell,harith⟩ := arithmetic_grid_heights
  obtain ⟨c,hc,hprog⟩ := dense_set_progression ell hell (1/2) (by norm_num)
  obtain ⟨B,hB,hbound⟩ := harith n c hc
  have hB' : (0:ℝ) < B := by exact_mod_cast hB
  refine ⟨1/(2*B),by positivity,?_⟩
  intro r hr G hG z w
  let b := fun p : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint r p.1+z
  let v := fun p : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint r p.2+w
  let E := occupiedGridRegion G b v r (fun _ => Set.Icc (0:ℝ) 1)
  obtain ⟨A,hAm,hAs,hsize,hsmall⟩ := grid_small_sections G hG b v hr
    (by norm_num : (0:ℝ)<1) (fun _ => Set.Icc (0:ℝ) 1)
    (fun _ _ => measurableSet_Icc) (fun _ _ => Set.Subset.rfl)
    (fun _ _ => by simp)
  have hAsize : (1/2:ℝ) ≤ volume.real A := by
    obtain ⟨j,hj⟩ := hG
    simpa only [Set.inter_eq_right.mpr hAs] using hsize j hj
  obtain ⟨p,hcp,hp1,hp⟩ := hprog A hAm hAs hAsize
  obtain ⟨i,hi,hcount⟩ := hbound r p.1 p.2 hr hcp hp1 G z w
  have htA := hp.2 ⟨i,hi⟩
  have ht := hAs htA
  have hv := hsmall (p.1+(i:ℝ)*p.2) htA
  rw [occupiedGridRegion_section_real G b v hr] at hv
  simp only [ht,Finset.filter_true,div_one] at hv
  have hmul := mul_le_mul_of_nonneg_left hcount (pow_nonneg hr.le n)
  change r^n*(fiberCardPartition G Prod.snd (theta/a))^a ≤
    r^n*((B:ℝ)*(G.image (fun q => gridIndex r
      (segmentPoint (b q) (v q) (p.1+(i:ℝ)*p.2)))).card) at hmul
  have hV : r^n*(fiberCardPartition G Prod.snd (theta/a))^a ≤ 2*(B:ℝ)*volume.real E := by
    have hh := mul_le_mul_of_nonneg_left hv hB'.le
    dsimp [E] at ⊢
    nlinarith only [hmul,hh]
  have hdivide : (r^n*(fiberCardPartition G Prod.snd (theta/a))^a)/(2*(B:ℝ)) ≤ volume.real E :=
    (div_le_iff₀ (show 0 < 2*(B:ℝ) by positivity)).mpr (by nlinarith only [hV])
  convert hdivide using 1; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.dense_set_progression
#print axioms KakeyaTwoScale.whole_lattice_segments_volume
