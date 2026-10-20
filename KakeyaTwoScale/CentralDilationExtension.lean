module
public import KakeyaTwoScale.UniversalSegmentExtension

@[expose] public section

open Set MeasureTheory
open OAI.Release061 OAI.Release061.SignElimination
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

/-- Central dilation, with both axial and transverse lengths scaled together. -/
def centralDilation {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a : ℝ) (o : E) (K : Set E) : Set E :=
  (fun y => o+a • (y-o)) '' K

/-- A convex, centrally symmetric body lies in the segment-extension universe
of any set containing it. This applies to the whole dilate, including off-axis points. -/
theorem centralDilation_subset_segmentExtension {V : Type*} [AddCommGroup V] [Module ℝ V]
    (a : ℝ) (o : V) (K E : Set V)
    (hconv : Convex ℝ K) (hsymm : ∀ y∈K, (2:ℝ) • o-y∈K) (hKE : K⊆E) :
    centralDilation a o K ⊆ segmentExtension ((a+1)/2) E := by
  rintro x ⟨y,hy,rfl⟩
  refine ⟨(2:ℝ) • (y-o),?_⟩
  intro t ht
  have hm := hconv (hsymm y hy) hy (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
  apply hKE
  convert hm using 1
  module

/-- Uniform volume of a union of central dilates of all convex symmetric bodies
contained in a semialgebraic set. No finiteness or disjointness of the family is required. -/
theorem uniform_central_dilation_union_volume {π : Type*} (n : ℕ)
    (S : Set ((π→ℝ) × (Fin n→ℝ)))
    (hS : PolynomialSignSet (fun z => Sum.elim z.1 z.2) S) :
    ∃ C : ℝ, 0<C ∧ ∃ M : ℕ, ∀ (p : π→ℝ) (a : ℝ),
      volume {x | ∃ (o : Fin n→ℝ) (K : Set (Fin n→ℝ)),
        Convex ℝ K ∧ (∀ y∈K, (2:ℝ) • o-y∈K) ∧ K⊆{x | (p,x)∈S} ∧
        x∈centralDilation a o K} ≤
      (ENNReal.ofReal (C*(max 1 |(a+1)/2|)^n)*M)*volume {x | (p,x)∈S} := by
  obtain ⟨C,hC,M,h⟩ := uniform_segment_extension_volume n S hS
  refine ⟨C,hC,M,?_⟩
  intro p a
  apply le_trans (measure_mono ?_) (h p ((a+1)/2))
  rintro x ⟨o,K,hconv,hsymm,hKE,hx⟩
  exact centralDilation_subset_segmentExtension a o K _ hconv hsymm hKE hx

end KakeyaTwoScale
#print axioms KakeyaTwoScale.centralDilation_subset_segmentExtension
#print axioms KakeyaTwoScale.uniform_central_dilation_union_volume
