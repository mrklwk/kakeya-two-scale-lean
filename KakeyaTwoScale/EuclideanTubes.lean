module
public import KakeyaTwoScale.GraphTubeVolume
public import KakeyaTwoScale.DirectionAngle
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

open MeasureTheory Metric
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- The source tube: the open Euclidean r-neighborhood of an affine unit
segment when `norm u = 1`. The definition itself allows arbitrary u. -/
def euclideanTube {d : ℕ} (b u : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∃ t ∈ Set.Icc (0:ℝ) 1, dist x (b+t • u) < r}

theorem euclideanTube_eq_thickening {d : ℕ} (b u : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    euclideanTube b u r = thickening r ((fun t : ℝ => b+t • u) '' Set.Icc (0:ℝ) 1) := by
  ext x
  rw [mem_thickening_iff]
  constructor
  · rintro ⟨t,ht,hx⟩; exact ⟨b+t • u,⟨t,ht,rfl⟩,hx⟩
  · rintro ⟨y,⟨t,ht,rfl⟩,hx⟩; exact ⟨t,ht,hx⟩

theorem isOpen_euclideanTube {d : ℕ} (b u : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    IsOpen (euclideanTube b u r) := by
  rw [euclideanTube_eq_thickening]; exact isOpen_thickening

theorem euclideanTube_finite {d : ℕ} (b u : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    volume (euclideanTube b u r) ≠ ⊤ := by
  have hs : euclideanTube b u r ⊆ closedBall 0 (‖b‖+‖u‖+r) := by
    intro x hx
    obtain ⟨t,ht,hx⟩ := hx
    have hn : ‖b+t • u‖ ≤ ‖b‖+‖u‖ := by
      have hh := norm_add_le b (t • u)
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1] at hh
      nlinarith [norm_nonneg u,ht.2]
    have hh := dist_triangle x (b+t • u) 0
    simp only [dist_zero_right] at hh
    change dist x 0 ≤ _
    rw [dist_zero_right]
    linarith
  exact measure_ne_top_of_subset hs (isCompact_closedBall _ _).measure_ne_top

theorem euclideanTube_union_finite {d : ℕ} {J : Type*} (G : Finset J)
    (b u : J → EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    volume (⋃ j ∈ G, euclideanTube (b j) (u j) r) ≠ ⊤ :=
  measure_biUnion_ne_top G.finite_toSet (fun j _ => euclideanTube_finite (b j) (u j) r)

/-- Reversing the direction also moves the base point to the other endpoint. -/
theorem euclideanTube_reverse {d : ℕ} (b u : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    euclideanTube (b+u) (-u) r = euclideanTube b u r := by
  ext x
  constructor
  · rintro ⟨t,ht,hx⟩
    refine ⟨1-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,?_⟩
    have he : (b+u)+t • (-u)=b+(1-t) • u := by module
    rwa [he] at hx
  · rintro ⟨t,ht,hx⟩
    refine ⟨1-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,?_⟩
    have he : (b+u)+(1-t) • (-u)=b+t • u := by module
    rwa [he]

/-- Projective angular separation in an explicit sign-invariant form.
For unit directions this is exactly separation by min(angle(u,v),angle(u,-v)). -/
def ProjectiveSeparated {X J : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (G : Finset J) (u : J → X) (r : ℝ) : Prop :=
  ∀ j ∈ G, ∀ k ∈ G, j ≠ k →
    r ≤ InnerProductGeometry.angle (u j) (u k) ∧
    r ≤ InnerProductGeometry.angle (u j) (-u k)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.euclideanTube_eq_thickening
#print axioms KakeyaTwoScale.isOpen_euclideanTube
#print axioms KakeyaTwoScale.euclideanTube_finite
#print axioms KakeyaTwoScale.euclideanTube_union_finite
#print axioms KakeyaTwoScale.euclideanTube_reverse
