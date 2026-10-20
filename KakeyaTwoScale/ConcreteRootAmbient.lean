module
public import KakeyaTwoScale.ConcreteRootCardinality
public import KakeyaTwoScale.AmbientBufferedStageInput
public import KakeyaTwoScale.PartitionDegreeBudget
public import KakeyaTwoScale.DirectionAngle

@[expose] public section

open Set Metric MeasureTheory
noncomputable section
namespace KakeyaTwoScale

theorem projective_separation_half_chord {n : ℕ}
    (u v : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (δ : ℝ) (hs : δ ≤ Real.arccos |inner ℝ u v|) : δ/2 ≤ dist u v := by
  have ha := ((source_angle_separation_iff u v hu hv δ).mp hs).1
  have hb := (unit_direction_angle_bounds u v hu hv).2
  have hc : Real.pi/2 * dist u v ≤ 2*dist u v :=
    mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) dist_nonneg
  linarith

/-- An actual root input, including its scale calendar, constructed entirely
from literal incidence and source projective angular separation. -/
def concreteRootAmbient {n k N q t : ℕ} (hn : 0<n) (hk : 0<k) (hq : 1≤q) (ht : 2≤t)
    (Y : Finset (RootTuple n k (Fin N))) (a : Fin n → ℤ)
    (b u : Fin N → EuclideanSpace ℝ (Fin n)) (hu : ∀ o, ‖u o‖=1)
    (hsep : ∀ o p, o≠p → ((2:ℝ)^q)⁻¹ ≤ Real.arccos |inner ℝ (u o) (u p)|)
    (hinc : ∀ y ∈ Y, ∀ j, (rootGridCube ((2:ℝ)^q)⁻¹ y.1 ∩
      flatCylinder (b (y.2 j)) (u (y.2 j)) 1 ((2:ℝ)^q)⁻¹).Nonempty)
    (hne : (coarseRootTuples Y ((2:ℝ)^q)⁻¹ a).Nonempty)
    (alpha : ℝ) (hp : 0<alpha) (hp1 : alpha≤1) :
    AmbientBufferedStageData n 0 k (n+1) (((4*k+3)*n)*q) q 0 (n*t)
      (RootTuple n k (Fin N)) (Fin n → ℤ) (Fin N) := by
  classical
  let Z := coarseRootTuples Y ((2:ℝ)^q)⁻¹ a
  refine {
    W := concreteRootState Y q a b u
    Y₀ := Z
    cube := Prod.fst
    tube := Prod.snd
    cubes := Z.image Prod.fst
    Q := rootGridCube ((2:ℝ)^q)⁻¹
    P := fun _ i => Fin.elim0 i
    D := partitionBoxDegree n
    alpha := alpha
    δ := ((2:ℝ)^q)⁻¹
    K := 1
    center := latticeCenter ((2:ℝ)^q)⁻¹
    dimension_pos := hn
    families_pos := hk
    exponent_pos := hp
    exponent_le_one := hp1
    width_pos := by positivity
    capture_nonneg := by norm_num
    valid := concreteRootState_valid Y q a b u hu hinc
    balanced := concreteRootState_balanced Y q a b u hne _ alpha
    nonempty := hne
    support := fun y hy => Finset.mem_image_of_mem _ hy
    cardinal_bound := coarseRootTuples_card_bound hq Y a u hu (fun o p hop =>
      projective_separation_half_chord (u o) (u p) (hu o) (hu p) _ (hsep o p hop))
    height_bound := fun _ => le_rfl
    degree := fun _ _ i => Fin.elim0 i
    regular := ?_
    capture := ?_
    partition_dimension := fun j _ => partitionBoxDegree_dimension n hn j
    partition_size := by nlinarith
    «measurable» := fun z _ => rootGridCube_measurable _ z
    finite_volume := ?_
    positive_volume := ?_
    preconnected := fun z _ => rootGridCube_preconnected _ z
    cube_radius := ?_
  }
  · intro g hg x hx
    exact Subsingleton.elim _ _
  · intro y hy j x hx
    have he : {x : EuclideanSpace ℝ (Fin (n+0)) |
        rectangularPolynomialMap (fun i : Fin 0 => Fin.elim0 i) x=0} = Set.univ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [he, one_mul]
    exact self_subset_thickening (by positivity) Set.univ (Set.mem_univ _)
  · intro z hz
    rw [rootGridCube_volume]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  · intro z hz
    change 0 < (volume (rootGridCube ((2:ℝ)^q)⁻¹ z)).toReal
    rw [rootGridCube_volume, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
    positivity
  · intro z hz x hx
    simpa using rootGridCube_radius (by positivity) z x hx

end KakeyaTwoScale
#print axioms KakeyaTwoScale.projective_separation_half_chord
#print axioms KakeyaTwoScale.concreteRootAmbient
