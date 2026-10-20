module
public import KakeyaTwoScale.TubeSliceVolume

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale

/-- The already closed ordinary estimate supplies a uniform positive volume
for one actual unit capsule in a fixed bounded region. -/
theorem euclideanTube_volume_lower (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r →
      ∀ b u : EuclideanSpace ℝ (Fin (n+1)), ‖b‖ ≤ R → ‖u‖=1 →
      c*r^n ≤ volume.real (euclideanTube b u r) := by
  obtain ⟨c,hc,h⟩ := source_separated_euclidean_tubes_volume n R hR
  refine ⟨c,hc,?_⟩
  intro r hr b u hb hu
  have hh := h r hr ({()} : Finset Unit) (Finset.singleton_nonempty ())
    (fun _ => b) (fun _ => u) (fun _ _ => hb) (fun _ _ => hu)
    (by intro j hj k hk hne; exact False.elim (hne (Subsingleton.elim j k)))
  have hset : (⋃ j ∈ ({()} : Finset Unit), euclideanTube b u r)=euclideanTube b u r := by
    ext x
    constructor
    · intro hx; obtain ⟨j,hj,hx⟩ := Set.mem_iUnion₂.mp hx; exact hx
    · intro hx; exact Set.mem_iUnion₂.mpr ⟨(),by simp,hx⟩
  rw [hset] at hh
  simpa using hh

/-- Removing a fixed-radius ball retains actual captured volume. All constants
precede the width, tube, captured set and ball center. E need not be an axis set
or even measurable for this outer-volume inequality. -/
theorem euclideanTube_retained_capture (n : ℕ) (R lam : ℝ)
    (hR : 0 ≤ R) (hlam : 0 < lam) :
    ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧ ∀ r : ℝ, 0 < r →
      ∀ b u p : EuclideanSpace ℝ (Fin (n+1)), ‖b‖ ≤ R → ‖u‖=1 →
      ∀ E : Set (EuclideanSpace ℝ (Fin (n+1))),
      lam*volume.real (euclideanTube b u r) ≤ volume.real (euclideanTube b u r ∩ E) →
      c*r^n ≤ volume.real ((euclideanTube b u r ∩ E) \ Metric.ball p delta) := by
  obtain ⟨c0,hc0,hvol⟩ := euclideanTube_volume_lower n R hR
  let A : ℝ := (2*(n+3:ℝ))^n
  have hA : 0 < A := by dsimp [A]; positivity
  let delta := lam*c0/(4*A)
  refine ⟨delta,lam*c0/2,by dsimp [delta]; positivity,by positivity,?_⟩
  intro r hr b u p hb hu E hcap
  have hfinite := euclideanTube_finite b u r
  have hsplit := measureReal_inter_add_sdiff (μ:=volume)
    (s:=euclideanTube b u r ∩ E) (t:=Metric.ball p delta) (Metric.isOpen_ball.measurableSet)
    (measure_ne_top_of_subset Set.inter_subset_left hfinite)
  have hsub : (euclideanTube b u r ∩ E) ∩ Metric.ball p delta ⊆
      euclideanTube b u r ∩ Metric.ball p delta := fun _ hx => ⟨hx.1.1,hx.2⟩
  have hsmall := (measureReal_mono hsub
    (measure_ne_top_of_subset Set.inter_subset_left hfinite)).trans
    (euclideanTube_inter_ball_volume b u p hr (by dsimp [delta]; positivity) hu)
  have he : 2*delta*(2*(n+3:ℝ))^n=lam*c0/2 := by
    change 2*(lam*c0/(4*A))*A=lam*c0/2
    field_simp; ring
  rw [he] at hsmall
  have hlower := mul_le_mul_of_nonneg_left (hvol r hr b u hb hu) hlam.le
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.euclideanTube_volume_lower
#print axioms KakeyaTwoScale.euclideanTube_retained_capture
