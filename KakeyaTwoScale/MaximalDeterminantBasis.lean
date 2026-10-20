module
public import KakeyaTwoScale.CoordinateBallVolume
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact

@[expose] public section

open Set Matrix
noncomputable section
namespace KakeyaTwoScale

/-- A compact body with a Euclidean inner ball has an actual maximum-determinant
basis in it. Its coordinate functionals are bounded by one on the whole body. -/
theorem exists_maximal_determinant_basis {N : ℕ}
    (K : Set (Fin N → ℝ)) (hK : IsCompact K) (ρ : ℝ) (hρ : 0 < ρ)
    (hinner : coordinateEuclideanBall N ρ ⊆ K) :
    ∃ b : Module.Basis (Fin N) ℝ (Fin N → ℝ),
      (∀ i, b i ∈ K) ∧ ∀ x ∈ K, ∀ i, |b.repr x i| ≤ 1 := by
  classical
  let e := Pi.basisFun ℝ (Fin N)
  let w : Fin N → Fin N → ℝ := fun i => (ρ/2) • Pi.single i 1
  have hw (i) : w i ∈ K := by
    apply hinner
    change (WithLp.toLp 2 (w i) : EuclideanSpace ℝ (Fin N)) ∈ Metric.ball 0 ρ
    rw [mem_ball_zero_iff]
    have he : (WithLp.toLp 2 (w i) : EuclideanSpace ℝ (Fin N)) =
        EuclideanSpace.single i (ρ/2) := by ext j; simp [w,Pi.single_apply]
    rw [he,PiLp.norm_single,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < ρ/2)]
    linarith
  have hwd : e.det w ≠ 0 := by
    rw [Pi.basisFun_det_apply]
    have he : Matrix.of w = Matrix.diagonal (fun _ : Fin N => ρ/2) := by
      ext i j
      simp [w,Matrix.diagonal,Pi.single_apply,eq_comm]
    rw [he,Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => ne_of_gt (by positivity))
  have hcompact : IsCompact (univ.pi (fun _ : Fin N => K)) := isCompact_univ_pi (fun _ => hK)
  have hcont : Continuous (fun v : Fin N → Fin N → ℝ => |e.det v|) := by
    simp only [e,Pi.basisFun_det_apply]
    exact (show Continuous (fun v : Fin N → Fin N → ℝ => Matrix.of v) from by fun_prop).matrix_det.abs
  obtain ⟨v,hv,hmax⟩ := hcompact.exists_isMaxOn ⟨w,fun i _ => hw i⟩ hcont.continuousOn
  have hd : e.det v ≠ 0 := by
    have hh := hmax (show w ∈ univ.pi (fun _ : Fin N => K) from fun i _ => hw i)
    exact abs_pos.mp (lt_of_lt_of_le (abs_pos.mpr hwd) hh)
  obtain ⟨hli,hspan⟩ := e.is_basis_iff_det.mpr (isUnit_iff_ne_zero.mpr hd)
  let b := Module.Basis.mk hli hspan.ge
  refine ⟨b,fun i => by simpa [b,Module.Basis.coe_mk] using hv i (mem_univ i),?_⟩
  intro x hx i
  have hu : Function.update v i x ∈ univ.pi (fun _ : Fin N => K) := by
    intro j _
    by_cases hji : j=i
    · simpa [hji] using hx
    · simpa [hji] using hv j (mem_univ j)
  have hh : |e.det (Function.update v i x)| ≤ |e.det v| := hmax hu
  have he := congrArg (fun f : (Fin N → ℝ) →ₗ[ℝ] ℝ => f x)
    (e.det_smul_mk_coord_eq_det_update hli hspan.ge i)
  change e.det v * b.repr x i = e.det (Function.update v i x) at he
  rw [← he,abs_mul] at hh
  have hpos := abs_pos.mpr hd
  by_contra! hbad
  have ht := mul_pos hpos (sub_pos.mpr hbad)
  nlinarith

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_maximal_determinant_basis
