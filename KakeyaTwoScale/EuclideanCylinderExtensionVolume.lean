module
public import KakeyaTwoScale.FlatCylinderCentralGeometry
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

open Set MeasureTheory
open OAI.Release061 OAI.Release061.SignElimination
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

theorem segmentExtension_preimage_linearEquiv
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (e : V≃ₗ[ℝ]W) (T : ℝ) (E : Set W) :
    segmentExtension T (e ⁻¹' E)=e ⁻¹' segmentExtension T E := by
  ext x
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨e v,?_⟩
    intro t ht
    simpa only [mem_preimage,map_add,map_smul] using hv t ht
  · rintro ⟨v,hv⟩
    refine ⟨e.symm v,?_⟩
    intro t ht
    simpa only [mem_preimage,map_add,map_smul,LinearEquiv.apply_symm_apply] using hv t ht

/-- All centrally enlarged actual flat cylinders contained in a set. -/
def flatCylinderFatUnion {d : ℕ} (a : ℝ) (E : Set (EuclideanSpace ℝ (Fin d))) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∃ b u L r, 0<L ∧ 0<r ∧ flatCylinder b u L r⊆E ∧
    x∈flatCylinder (b+((1-a)*L/2) • u) u (a*L) (a*r)}

theorem flatCylinderFatUnion_subset_extension {d : ℕ} (a : ℝ) (ha : 0<a)
    (E : Set (EuclideanSpace ℝ (Fin d))) :
    flatCylinderFatUnion a E ⊆ segmentExtension ((a+1)/2) E := by
  rintro x ⟨b,u,L,r,_hL,_hr,hsub,hx⟩
  apply centralDilation_subset_segmentExtension a (b+(L/2) • u) (flatCylinder b u L r) E
    (flatCylinder_convex b u L r) (flatCylinder_central_symmetry b u L r) hsub
  rwa [flatCylinder_central_dilation b u L r a ha]

/-- A proved volume bound for the actual union of enlarged flat cylinders.
The fixed sign family controls the constant, before any coefficient values or scale. -/
theorem uniform_flatCylinderFatUnion_volume {π : Type*} (d : ℕ)
    (S : Set ((π→ℝ) × (Fin d→ℝ)))
    (hS : PolynomialSignSet (fun z => Sum.elim z.1 z.2) S) :
    ∃ C : ℝ, 0<C ∧ ∃ M : ℕ, ∀ (p : π→ℝ) (a : ℝ), 0<a →
      volume (flatCylinderFatUnion a {x : EuclideanSpace ℝ (Fin d) | (p,WithLp.ofLp x)∈S}) ≤
        (ENNReal.ofReal (C*(max 1 |(a+1)/2|)^d)*M)*
          volume {x : EuclideanSpace ℝ (Fin d) | (p,WithLp.ofLp x)∈S} := by
  obtain ⟨C,hC,M,h⟩ := uniform_segment_extension_volume d S hS
  refine ⟨C,hC,M,?_⟩
  intro p a ha
  let E : Set (Fin d→ℝ) := {x | (p,x)∈S}
  have hvol (K : Set (Fin d→ℝ)) :
      volume (WithLp.ofLp ⁻¹' K : Set (EuclideanSpace ℝ (Fin d)))=volume K :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).measure_preimage_equiv K
  have hext := segmentExtension_preimage_linearEquiv
    (WithLp.linearEquiv 2 ℝ (Fin d→ℝ)) ((a+1)/2) E
  change segmentExtension ((a+1)/2) (WithLp.ofLp ⁻¹' E)=
    WithLp.ofLp ⁻¹' segmentExtension ((a+1)/2) E at hext
  calc
    _ ≤ volume (segmentExtension ((a+1)/2) (WithLp.ofLp ⁻¹' E)) :=
      measure_mono (flatCylinderFatUnion_subset_extension a ha _)
    _ = volume (segmentExtension ((a+1)/2) E) := by rw [hext,hvol]
    _ ≤ _ := by
      have hvE : volume {x : EuclideanSpace ℝ (Fin d) | (p,WithLp.ofLp x)∈S}=volume E := hvol E
      rw [hvE]
      exact h p ((a+1)/2)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.segmentExtension_preimage_linearEquiv
#print axioms KakeyaTwoScale.flatCylinderFatUnion_subset_extension
#print axioms KakeyaTwoScale.uniform_flatCylinderFatUnion_volume
