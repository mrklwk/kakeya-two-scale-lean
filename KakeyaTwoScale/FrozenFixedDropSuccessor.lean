module
public import KakeyaTwoScale.FrozenBalancedCut
public import KakeyaTwoScale.FrozenScaleArithmetic

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
namespace KakeyaTwoScale
namespace FrozenGeometryState

/-- Construct one full fixed-drop normalization round for a deficient active
family. All families share the selected relation, and the actual normalized
upper reset is proved after geometry and balancing. -/
theorem exists_fixed_drop_successor {n k A B d : ℕ} {T C O : Type}
    [DecidableEq T] [DecidableEq C]
    (S : FrozenGeometryState n k T C O) (Y₀ : Finset T) (cube : T → C)
    (tube : T → Fin k → O) (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (cubes : Finset C) (center : C → EuclideanSpace ℝ (Fin n))
    {δ p q : ℝ} (hδ : 0 < δ) (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hv : S.Valid Y₀ cube tube Q δ) (hb : S.Balanced cube cubes p)
    (hne : S.tuples.Nonempty) (hcubes : ∀ y ∈ S.tuples, cube y ∈ cubes)
    (hbound : (S.tuples.card:ℝ) ≤ (2:ℝ)^B)
    (hQ : ∀ c ∈ cubes, ∀ x ∈ Q c, dist x (center c) ≤ (A:ℝ)*δ)
    (beta : Fin k → ℝ) (i : Fin k) (hi : 0 < S.height i)
    (hdef : S.normalizedCount cube q i < 2*beta i) :
    ∃ V : FrozenGeometryState n k T C O,
      V.Valid Y₀ cube tube Q δ ∧ V.Balanced cube cubes p ∧ V.tuples.Nonempty ∧
      V.tuples ⊆ S.tuples ∧ V.height=dropFamilyHeight d S.height i ∧
      frozenHeightPotential d V.height+d ≤ frozenHeightPotential d S.height ∧
      V.ballRadius=(A+n+5:ℝ)*δ*(∑ j, (2:ℝ)^(V.height j)) ∧
      tupleCubeMass S.tuples cube cubes p /
        ((3^k*(2*(A+n+5)+1)^n*(B+1)^(k+1):ℕ):ℝ) ≤ tupleCubeMass V.tuples cube cubes p ∧
      (∀ j, V.normalizedCount cube q j ≤ 2*S.normalizedCount cube q j ∨
        V.normalizedCount cube q j ≤ 2*(beta j*(2:ℝ)^(d+1))) ∧
      (∀ y ∈ V.tuples, ∀ j, V.geometry δ j (V.parent y j) ⊆ S.geometry δ j (S.parent y j)) ∧
      (∀ y ∈ V.tuples, ∀ j, V.axis j (V.parent y j)=S.axis j (S.parent y j)) ∧
      (∃ lift : V.Grain → S.Grain, ∀ y ∈ V.tuples, lift (V.grain (cube y))=S.grain (cube y)) := by
  classical
  let H := dropFamilyHeight d S.height i
  let r := δ*(∑ j, (2:ℝ)^(H j))
  have hsum (j : Fin k) : (2:ℝ)^(H j) ≤ ∑ t, (2:ℝ)^(H t) :=
    Finset.single_le_sum (f:=fun t : Fin k => (2:ℝ)^(H t)) (fun t _ => by positivity) (Finset.mem_univ j)
  have hs : 1 ≤ ∑ j, (2:ℝ)^(H j) := (one_le_pow₀ (by norm_num)).trans (hsum i)
  have hδr : δ ≤ r := by dsimp [r]; nlinarith
  have hr : 0 < r := hδ.trans_le hδr
  have hHr (j : Fin k) : δ*2^(H j) ≤ 2*r := by
    have hh := mul_le_mul_of_nonneg_left (hsum j) hδ.le
    dsimp [r] at *
    linarith
  have hQr : ∀ c ∈ cubes, ∀ x ∈ Q c, dist x (center c) ≤ (A:ℝ)*r := by
    intro c hc x hx
    exact (hQ c hc x hx).trans (mul_le_mul_of_nonneg_left hδr (Nat.cast_nonneg _))
  obtain ⟨V,hVv,hVb,hVne,hVS,hVH,hVr,hVmass,hVcount,hVgeom,hVaxis,hVancestry⟩ :=
    exists_balanced_cut S Y₀ cube tube Q cubes center hδ hr hδr hp hp1 hq hq1 hv hb hne hcubes hbound
      H (fun j => fixed_drop_height_mono S.height i j) hHr hQr
  refine ⟨V,hVv,hVb,hVne,hVS,hVH,?_,?_,hVmass,?_,hVgeom,hVaxis,hVancestry⟩
  · rw [hVH]
    exact fixed_drop_potential S.height i hi
  · rw [hVr,hVH]
    dsimp [r]
    ring
  · intro j
    have hh : (0:ℝ) < (S.grains cube).card := by exact_mod_cast Finset.card_pos.mpr (hne.image _)
    have hh' : (0:ℝ) < (V.grains cube).card := by exact_mod_cast Finset.card_pos.mpr (hVne.image _)
    have hreset := normalized_ratio_reset hh hh' (hVcount j)
    change V.normalizedCount cube q j ≤ (2*(S.length δ j/(δ*2^(H j))))*S.normalizedCount cube q j at hreset
    by_cases hji : j=i
    · subst j
      right
      have hratio : S.length δ i/(δ*2^(H i)) ≤ (2:ℝ)^d := by
        simpa [length,H,dropFamilyHeight] using fixed_drop_ratio_le hδ (S.height i) d
      have hnonneg : 0 ≤ S.normalizedCount cube q i := by unfold normalizedCount; positivity
      have hh := mul_le_mul_of_nonneg_right hratio hnonneg
      have hpw : 0 < (2:ℝ)^d := by positivity
      rw [pow_succ]
      nlinarith
    · left
      have he : S.length δ j/(δ*2^(H j))=1 := by
        dsimp [length,H,dropFamilyHeight]
        rw [ite_eq_right hji,div_self (by positivity)]
      simpa only [he,mul_one] using hreset

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.exists_fixed_drop_successor
