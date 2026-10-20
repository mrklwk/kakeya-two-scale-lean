module
public import KakeyaTwoScale.InflatedPrescribedVisibility

@[expose] public section

open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

def unitTubeAreaConstant (n : ℕ) : ℝ :=
  (2:ℝ)^(n+1)*volume.real (closedBall (0 : Fin n → ℝ) (1+((n+1:ℕ):ℝ)))

/-- A finite selected set of incident cubes satisfies the same actual averaged
tube budget; its cardinality never enters the constant. -/
theorem prescribedCubeSeminorm_tube_budget {n D J : ℕ}
    (z : Fin J → Fin (n+1) → ℤ) (hz : Function.Injective z)
    (ε : ℝ) (hε : 0 < ε) (c : FullCoefficientSphere (n+1) D)
    (I : Finset (Fin J)) (b : Fin (n+1) → ℝ)
    (u : EuclideanSpace ℝ (Fin (n+1))) (hu : ‖u‖=1)
    (hinc : ∀j∈I, (visibilityCube (fun a => (z j a:ℝ)) ∩
      infiniteLineTube b (WithLp.ofLp u) 1).Nonempty) :
    (∑j∈I, prescribedCubeSeminorm n D J (fun j a => (z j a:ℝ)) ε c j u)  ≤ 
      unitTubeAreaConstant n*(D:ℝ) := by
  let zr : Fin J → Fin (n+1) → ℝ := fun j a => (z j a:ℝ)
  have hz' : Function.Injective (fun j : I => z j.val) := by
    intro i j h
    exact Subtype.ext (hz h)
  have hh := mollified_lattice_tube_budget (fullDegreeFinMonomial (n+1) D)
    (fullDegreeFinMonomial_injective (n+1) D) (fullDegreeFinMonomial_degree (n+1) D)
    (fun j : I => z j.val) hz' (cubeFamilyRadius zr) (cubeFamilyRadius_nonneg zr)
    (fun j => cubeFamilyRadius_bound zr j.val) b u hu 1 (by norm_num)
    (fun j => hinc j.val j.property) ε hε c
  have he (j : I) : mollifiedCoefficientArea (fullDegreeFinMonomial (n+1) D)
      (fullDegreeFinMonomial_injective (n+1) D) (visibilityCube (zr j.val)) measurableSet_closedBall
      (cubeFamilyRadius zr) (cubeFamilyRadius_nonneg zr) (cubeFamilyRadius_bound zr j.val) ε c u =
      prescribedCubeSeminorm n D J zr ε c j.val u := by
    exact (mollifiedAreaSeminorm_apply _ _ _ _ _ _ _ _ _ _ _ _).symm
  change (∑j : I, mollifiedCoefficientArea _ _ (visibilityCube (zr j.val)) _ _ _ _ ε c u) ≤ _ at hh
  simp_rw [he] at hh
  rw [Finset.sum_coe_sort I (fun j => prescribedCubeSeminorm n D J zr ε c j u)] at hh
  simpa only [zr,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofNat,ENNReal.toReal_natCast,unitTubeAreaConstant,Measure.real,mul_assoc,mul_comm,mul_left_comm]
    using hh

/-- Actual visibility factors with constants before all lattice cubes and
normalized prescriptions. Both wedge control and tube budgets are constructed
from the same mollified polynomial; no geometric certificate is assumed. -/
theorem actual_multilinear_factors (n k : ℕ) (hk : k ≤ n+1) :
    ∃A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀(J : ℕ) (z : Fin J → Fin (n+1) → ℤ),
      Function.Injective z → ∀m : Fin J → ℝ, (∀j, 0  ≤  m j) → (∑j, m j)=1 →
      ∃S : Fin J → EuclideanSpace ℝ (Fin (n+1)) → ℝ,
        (∀j v, 0 ≤ S j v) ∧
        (∀j (v : Fin k → EuclideanSpace ℝ (Fin (n+1))),
          tupleWedgeVolume v*m j ≤ A*∏i, S j (v i)) ∧
        (∀(I : Finset (Fin J)) (b : Fin (n+1) → ℝ)
          (u : EuclideanSpace ℝ (Fin (n+1))), ‖u‖=1 →
          (∀j∈I, (visibilityCube (fun a => (z j a:ℝ)) ∩ infiniteLineTube b (WithLp.ofLp u) 1).Nonempty) →
          (∑j∈I, S j u) ≤ B) := by
  classical
  obtain ⟨Cdeg,hCdeg,hpres⟩ := inflated_prescribed_visibility n
  let U := localCubeAreaConstant n*Cdeg
  let F := (2*((n+1:ℕ):ℝ)^2)^(n+1)
  let V := volume.real (coordinateEuclideanBall (n+1) 1)
  have hU : 0 ≤ U := mul_nonneg measureReal_nonneg hCdeg.le
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hV : 0 < V := ENNReal.toReal_pos
    (coordinateEuclideanBall_positive _ _ (by norm_num)).ne' (coordinateEuclideanBall_finite _ _).ne
  refine ⟨F*U^(n+1-k)/V,unitTubeAreaConstant n*Cdeg,by positivity,
    mul_nonneg (mul_nonneg (by positivity) measureReal_nonneg) hCdeg.le,?_⟩
  intro J z hz m hm hsum
  let zr : Fin J → Fin (n+1) → ℝ := fun j a => (z j a:ℝ)
  obtain ⟨D,lam,ε,c,hlam,hD,hε,hε2,hvol,hlower⟩ := hpres J zr m hm hsum
  let p := prescribedCubeSeminorm n D J zr ε c
  let S := fun j v => if 0 < m j then p j v/lam else 0
  have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hp (j v) : 0 ≤ p j v := apply_nonneg _ _
  have hS (j v) : 0 ≤ S j v := by dsimp [S]; split_ifs  <;> positivity
  have hC : 0 ≤ localCubeAreaConstant n*(D:ℝ) := mul_nonneg measureReal_nonneg (Nat.cast_nonneg D)
  have hupper : localCubeAreaConstant n*(D:ℝ) ≤ U*lam := by
    have hh := mul_le_mul_of_nonneg_left hD (show 0 ≤ localCubeAreaConstant n from measureReal_nonneg)
    dsimp [U]
    nlinarith only [hh]
  refine ⟨S,hS,?_,?_⟩
  · intro j v
    by_cases hj : 0 < m j
    · have hw := visibility_wedge_bound (by omega : 0 < n+1) hk (p j)
        (prescribedCubeSeminorm_continuous n D J zr ε hε hε2 c j)
        (localCubeAreaConstant n*(D:ℝ)) hC
        (prescribedCubeSeminorm_upper n D J zr ε hε c j) (hlower j hj) v
      have he : (∏i, p j (v i))=lam^k*(∏i, S j (v i)) := by
        simp only [S,ite_eq_left hj,Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
        field_simp
      exact visibility_wedge_inflation_cancel hk _ V _ F _ U lam (m j) _ _ hV measureReal_nonneg hF hC hU hlam0
        (hm j) (Finset.prod_nonneg (fun i _ => hp j (v i))) (Finset.prod_nonneg (fun i _ => hS j (v i)))
        hw (hvol j) hupper he
    · have hm0 : m j=0 := le_antisymm (le_of_not_gt hj) (hm j)
      rw [hm0,mul_zero]
      exact mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => hS j (v i)))
  · intro I b u hu hinc
    have hh := prescribedCubeSeminorm_tube_budget z hz ε hε c I b u hu hinc
    have he : (∑j∈I, S j u) ≤ (∑j∈I, p j u)/lam := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro j _
      dsimp [S]
      split_ifs
      · exact le_rfl
      · exact div_nonneg (hp j u) hlam0.le
    apply he.trans
    apply (div_le_iff₀ hlam0).mpr
    have hconst : 0 ≤ unitTubeAreaConstant n := mul_nonneg (by positivity) measureReal_nonneg
    have hd := mul_le_mul_of_nonneg_left hD hconst
    change (∑j∈I, p j u) ≤ _ at hh
    nlinarith only [hh,hd]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.prescribedCubeSeminorm_tube_budget
#print axioms KakeyaTwoScale.actual_multilinear_factors
