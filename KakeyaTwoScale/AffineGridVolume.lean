module
public import KakeyaTwoScale.PortionGridVolume
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- The coordinate change for an independently affine-translated horizontal grid. -/
def gridShear {n : ℕ} (xi zeta : Fin n → ℝ) (p : ℝ × (Fin n → ℝ)) : ℝ × (Fin n → ℝ) :=
  (p.1,p.2-(xi+p.1 • zeta))

theorem measurable_gridShear {n : ℕ} (xi zeta : Fin n → ℝ) : Measurable (gridShear xi zeta) := by
  exact measurable_fst.prodMk (continuous_snd.sub
    (continuous_const.add (continuous_fst.smul continuous_const))).measurable

/-- Fubini proves preservation of genuine product volume under the time-dependent
translation. The grid-membership identity alone would not imply this result. -/
theorem volume_gridShear_preimage {n : ℕ} (xi zeta : Fin n → ℝ)
    (E : Set (ℝ × (Fin n → ℝ))) (hE : MeasurableSet E) :
    volume (gridShear xi zeta ⁻¹' E)=volume E := by
  rw [Measure.volume_eq_prod,Measure.prod_apply (hE.preimage (measurable_gridShear xi zeta)),
    Measure.prod_apply hE]
  apply lintegral_congr
  intro t
  have he : (fun x => (t,x)) ⁻¹' (gridShear xi zeta ⁻¹' E) =
      (fun x : Fin n → ℝ => x+(-(xi+t • zeta))) ⁻¹' ((fun x => (t,x)) ⁻¹' E) := by
    ext x; simp [gridShear,sub_eq_add_neg]
  rw [he,measure_preimage_add_right]

/-- Actual region using cubes of the independent moving grid xi+t*zeta+rZ^n. -/
def affineOccupiedGridRegion {n : ℕ} {J : Type*} (G : Finset J)
    (b v : J → Fin n → ℝ) (r : ℝ) (I : J → Set ℝ) (xi zeta : Fin n → ℝ) :
    Set (ℝ × (Fin n → ℝ)) :=
  ⋃ j ∈ G, {p | p.1 ∈ I j ∧ gridIndex r (p.2-(xi+p.1 • zeta)) =
    gridIndex r (segmentPoint (b j) (v j) p.1-(xi+p.1 • zeta))}

theorem affineOccupiedGridRegion_eq {n : ℕ} {J : Type*} (G : Finset J)
    (b v : J → Fin n → ℝ) (r : ℝ) (I : J → Set ℝ) (xi zeta : Fin n → ℝ) :
    affineOccupiedGridRegion G b v r I xi zeta = gridShear xi zeta ⁻¹'
      occupiedGridRegion G (fun j => b j-xi) (fun j => v j-zeta) r I := by
  have he (j) (t : ℝ) : segmentPoint (b j) (v j) t-(xi+t • zeta) =
      segmentPoint (b j-xi) (v j-zeta) t := by
    unfold segmentPoint; rw [smul_sub]; abel
  ext p
  simp only [affineOccupiedGridRegion,Set.mem_iUnion,Set.mem_ofPred_eq,occupiedGridRegion,
    Set.mem_preimage,gridShear,he]

theorem affineOccupiedGridRegion_volume {n : ℕ} {J : Type*} (G : Finset J)
    (b v : J → Fin n → ℝ) (r : ℝ) (I : J → Set ℝ) (xi zeta : Fin n → ℝ)
    (hm : ∀ j ∈ G, MeasurableSet (I j)) :
    volume (affineOccupiedGridRegion G b v r I xi zeta) =
      volume (occupiedGridRegion G (fun j => b j-xi) (fun j => v j-zeta) r I) := by
  rw [affineOccupiedGridRegion_eq,volume_gridShear_preimage xi zeta _
    (measurableSet_occupiedGridRegion _ _ _ _ _ hm)]

/-- Whole-segment volume with independent lattice offsets and moving grid. -/
theorem whole_lattice_segments_affine_volume (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∀ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)), G.Nonempty →
      ∀ z w xi zeta : Fin n → ℝ,
      C*r^n*(fiberCardPartition G Prod.snd (theta/a))^a ≤
        volume.real (affineOccupiedGridRegion G
          (fun p => latticePoint r p.1+z) (fun p => latticePoint r p.2+w) r
          (fun _ => Set.Icc (0:ℝ) 1) xi zeta) := by
  obtain ⟨C,hC,hvol⟩ := whole_lattice_segments_volume n
  refine ⟨C,hC,?_⟩
  intro r hr G hG z w xi zeta
  rw [Measure.real,affineOccupiedGridRegion_volume _ _ _ _ _ _ _ (fun _ _ => measurableSet_Icc)]
  simpa only [add_sub_assoc,Measure.real] using hvol r hr G hG (z-xi) (w-zeta)

/-- Fixed-portion volume with the source's independently translated grids. -/
theorem lattice_portions_affine_volume (n : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∀ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)), G.Nonempty →
      Set.InjOn Prod.snd (↑G : Set ((Fin n → ℤ) × (Fin n → ℤ))) →
      ∀ z w xi zeta : Fin n → ℝ, ∀ I : ((Fin n → ℤ) × (Fin n → ℤ)) → Set ℝ,
      (∀ j ∈ G, MeasurableSet (I j)) →
      (∀ j ∈ G, I j ⊆ Set.Icc (0:ℝ) 1) →
      (∀ j ∈ G, lam ≤ volume.real (I j)) →
      C*r^n*(G.card:ℝ)^a ≤ volume.real (affineOccupiedGridRegion G
        (fun p => latticePoint r p.1+z) (fun p => latticePoint r p.2+w) r I xi zeta) := by
  obtain ⟨C,hC,hvol⟩ := lattice_portions_volume n lam hlam
  refine ⟨C,hC,?_⟩
  intro r hr G hG hinj z w xi zeta I hm hs hsize
  rw [Measure.real,affineOccupiedGridRegion_volume _ _ _ _ _ _ _ hm]
  simpa only [add_sub_assoc,Measure.real] using hvol r hr G hG hinj (z-xi) (w-zeta) I hm hs hsize

end KakeyaTwoScale
#print axioms KakeyaTwoScale.measurable_gridShear
#print axioms KakeyaTwoScale.volume_gridShear_preimage
#print axioms KakeyaTwoScale.affineOccupiedGridRegion_eq
#print axioms KakeyaTwoScale.affineOccupiedGridRegion_volume
#print axioms KakeyaTwoScale.whole_lattice_segments_affine_volume
#print axioms KakeyaTwoScale.lattice_portions_affine_volume
