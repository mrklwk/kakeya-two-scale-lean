module
public import KakeyaTwoScale.PolynomialPathSum

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

def coordinateOpenBox (N : ℕ) (r : ℝ) : Set (Fin N → ℝ) := univ.pi (fun _ => Ioo (-r) r)

theorem coordinateOpenBox_measurable (N : ℕ) (r : ℝ) : MeasurableSet (coordinateOpenBox N r) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)

def weightedCoordinateArea {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (A : DisjointChartAtlas n {x | MvPolynomial.eval x P=0}) (α b : ℝ) : ℝ≥0∞ :=
  ∑ j : Fin (n+1),
    (ENNReal.ofReal (2*α))^(j.val+1) * (ENNReal.ofReal (2*b))^(n+1-j.val) *
    (A.restrict (coordinateEuclideanBall (n+1) 1) (coordinateEuclideanBall_open _ _).measurableSet).directionalArea (Pi.single j 1)

theorem polynomialPathSum_subset_box_bound {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (A : DisjointChartAtlas n {x | MvPolynomial.eval x P=0}) (α b : ℝ)
    (S : Set (Fin (n+1) → ℝ)) (hS : S ⊆ coordinateOpenBox (n+1) α) :
    (∫⁻ x in S, ∫⁻ z in coordinateOpenBox (n+1) b, polynomialPathSum P (x,z)) ≤ weightedCoordinateArea P A α b := by
  have he (r : ℝ) : (volume : Measure (Fin (n+1) → ℝ)).restrict (coordinateOpenBox (n+1) r) =
      Measure.pi (fun _ => intervalVolume r) := Measure.restrict_pi_pi _ _
  have h := polynomialPathSum_box_bound P A α b
  rw [← he α,← he b,lintegral_prod _ (measurable_polynomialPathSum P).aemeasurable] at h
  exact (lintegral_mono_set hS).trans h

/-- Full geometric/integral assembly before scalar normalization. Neither a
crossing estimate nor a product-volume factor is left as a hypothesis. -/
theorem bisection_weighted_area_assembly {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (A : DisjointChartAtlas n {x | MvPolynomial.eval x P=0})
    (α b : ℝ) (hα : 0 ≤ α) (hb : 0 ≤ b) (hsmall : α^2+(n+1:ℕ)*b^2 < 1)
    (S T : Set (Fin (n+1) → ℝ)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hs : ∀ x ∈ S, x ∈ coordinateEuclideanBall (n+1) α ∧ 0 < MvPolynomial.eval x P)
    (ht : ∀ y ∈ T, y ∈ coordinateEuclideanBall (n+1) α ∧ MvPolynomial.eval y P < 0) :
    volume S * volume T * volume (coordinateOpenBox (n+1) b) ≤
      (volume T + volume S) * weightedCoordinateArea P A α b := by
  let Z := coordinateOpenBox (n+1) b
  have hZ : MeasurableSet Z := coordinateOpenBox_measurable _ _
  have hl : volume S * volume T * volume Z ≤
      ∫⁻ x in S, ∫⁻ y in T, ∫⁻ z in Z, polynomialPathSum P (x,z)+polynomialPathSum P (y,z) := by
    calc
      _ = ∫⁻ _x in S, ∫⁻ _y in T, ∫⁻ _z in Z, (1:ℝ≥0∞) := by simp [mul_comm,mul_left_comm]
      _ ≤ _ := by
        apply setLIntegral_mono' hS
        intro x hx
        apply setLIntegral_mono' hT
        intro y hy
        apply setLIntegral_mono' hZ
        intro z hz
        apply central_hub_count_lower (fun v => MvPolynomial.eval v.ofLp P)
          (P.continuous_eval.comp (PiLp.continuous_ofLp 2 _)) α b hα hb hsmall
        · exact le_of_lt (by simpa [coordinateEuclideanBall] using (hs x hx).1)
        · exact le_of_lt (by simpa [coordinateEuclideanBall] using (ht y hy).1)
        · intro i
          exact (abs_lt.mpr (hz i (mem_univ i))).le
        · exact (hs x hx).2
        · exact (ht y hy).2
  have hsep := two_path_integral_separation (volume.restrict S) (volume.restrict T)
    (volume.restrict Z) (polynomialPathSum P) (measurable_polynomialPathSum P)
  simp only [Measure.restrict_apply_univ] at hsep
  rw [hsep] at hl
  have hSB : S ⊆ coordinateOpenBox (n+1) α := fun x hx => coordinateEuclideanBall_subset_box _ _ (hs x hx).1
  have hTB : T ⊆ coordinateOpenBox (n+1) α := fun x hx => coordinateEuclideanBall_subset_box _ _ (ht x hx).1
  calc
    _ ≤ _ := hl
    _ ≤ volume T * weightedCoordinateArea P A α b + volume S * weightedCoordinateArea P A α b :=
      add_le_add (mul_le_mul le_rfl (polynomialPathSum_subset_box_bound P A α b S hSB) zero_le zero_le)
        (mul_le_mul le_rfl (polynomialPathSum_subset_box_bound P A α b T hTB) zero_le zero_le)
    _ = _ := (add_mul _ _ _).symm

end KakeyaTwoScale
#print axioms KakeyaTwoScale.polynomialPathSum_subset_box_bound
#print axioms KakeyaTwoScale.bisection_weighted_area_assembly
