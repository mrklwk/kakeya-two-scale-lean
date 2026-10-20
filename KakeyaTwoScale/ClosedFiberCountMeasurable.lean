module
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.SetTheory.Cardinal.Embedding
public import Mathlib.Topology.Instances.ENNReal.ENatENNReal

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KakeyaTwoScale

private theorem nat_le_fiber_encard_iff {X : Type*} (f : X × ℝ → ℝ) (y : X) (m : ℕ) :
    (m : ℕ∞) ≤ ({t : ℝ | f (y,t)=0} : Set ℝ).encard ↔
      ∃ t : Fin m → ℝ, Function.Injective t ∧ ∀ i, f (y,t i)=0 := by
  classical
  constructor
  · intro h
    obtain ⟨e,_⟩ := Fin.Embedding.exists_embedding_disjoint_range_of_add_le_ENat_card
      (s := (∅ : Set ↥({t : ℝ | f (y,t)=0} : Set ℝ))) (n := m)
      (by simpa only [Set.ncard_empty, Nat.cast_zero, zero_add, Set.encard] using h)
    exact ⟨fun i => (e i).val, fun i j hij => e.injective (Subtype.ext hij), fun i => (e i).property⟩
  · rintro ⟨t,ht,hz⟩
    let e : Fin m → ↥({t : ℝ | f (y,t)=0} : Set ℝ) := fun i => ⟨t i,hz i⟩
    have he : Function.Injective e := fun i j hij => ht (congrArg Subtype.val hij)
    simpa only [Set.encard, ENat.card_eq_coe_fintype_card, Fintype.card_fin] using
      ENat.card_le_card_of_injective he

private def closedRootWitness {n m : ℕ} (f : (Fin n → ℝ) × ℝ → ℝ)
    (R : ℕ) (l : Fin m → Fin m → ℕ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
  Metric.closedBall 0 R ∩ {z | (∀ i, f (z.1,z.2 i)=0) ∧
    ∀ i j, i≠j → 1/((l i j : ℝ)+1) ≤ dist (z.2 i) (z.2 j)}

private theorem closedRootWitness_compact {n m : ℕ}
    (f : (Fin n → ℝ) × ℝ → ℝ) (hf : Continuous f)
    (R : ℕ) (l : Fin m → Fin m → ℕ) :
    IsCompact (closedRootWitness f R l) := by
  apply (isCompact_closedBall (0 : (Fin n → ℝ) × (Fin m → ℝ)) R).inter_right
  have hz : IsClosed (⋂ i : Fin m,
      {z : (Fin n → ℝ) × (Fin m → ℝ) | f (z.1,z.2 i)=0}) :=
    isClosed_iInter fun i => isClosed_eq
      (hf.comp (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))) continuous_const
  have hd : IsClosed (⋂ i : Fin m, ⋂ j : Fin m, ⋂ (_ : i≠j),
      {z : (Fin n → ℝ) × (Fin m → ℝ) |
        1/((l i j : ℝ)+1) ≤ dist (z.2 i) (z.2 j)}) :=
    isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le continuous_const (((continuous_apply i).comp continuous_snd).dist
          ((continuous_apply j).comp continuous_snd))
  convert hz.inter hd using 1
  ext z
  simp

/-- Every finite superlevel of the exact number of real zeros in a continuous
fiber is Borel. Infinite fibers are retained, not discarded. -/
theorem measurableSet_continuous_fiber_count_ge {n : ℕ}
    (f : (Fin n → ℝ) × ℝ → ℝ) (hf : Continuous f) (m : ℕ) :
    MeasurableSet {y | (m : ℕ∞) ≤ ({t : ℝ | f (y,t)=0} : Set ℝ).encard} := by
  classical
  have he : {y | (m : ℕ∞) ≤ ({t : ℝ | f (y,t)=0} : Set ℝ).encard} =
      ⋃ R : ℕ, ⋃ l : Fin m → Fin m → ℕ, Prod.fst '' closedRootWitness f R l := by
    ext y
    simp only [mem_ofPred_eq, mem_iUnion, mem_image]
    rw [nat_le_fiber_encard_iff]
    constructor
    · rintro ⟨t,ht,hz⟩
      have hs : ∀ i j : Fin m, ∃ l : ℕ, i≠j →
          1/((l : ℝ)+1) ≤ dist (t i) (t j) := by
        intro i j
        by_cases hij : i=j
        · exact ⟨0,fun h => (h hij).elim⟩
        · obtain ⟨l,hl⟩ := exists_nat_one_div_lt (dist_pos.mpr (fun h => hij (ht h)))
          exact ⟨l,fun _ => hl.le⟩
      choose l hl using hs
      obtain ⟨R,hR⟩ := exists_nat_gt ‖(y,t)‖
      refine ⟨R,l,(y,t),?_,rfl⟩
      exact ⟨by simpa [Metric.mem_closedBall,dist_zero_right] using hR.le, hz, hl⟩
    · rintro ⟨R,l,z,hz,hzy⟩
      subst y
      refine ⟨z.2,?_,hz.2.1⟩
      intro i j hij
      by_contra hne
      have hh := hz.2.2 i j hne
      rw [hij,dist_self] at hh
      have hp : 0 < 1/((l i j : ℝ)+1) := by positivity
      exact (not_le_of_gt hp) hh
  rw [he]
  exact MeasurableSet.iUnion fun R => MeasurableSet.iUnion fun l =>
    ((closedRootWitness_compact f hf R l).image continuous_fst).measurableSet

/-- The exact extended-natural number of real zeros in each continuous fiber
is a Borel measurable function. No polynomial or finite-fiber premise is used. -/
theorem measurable_continuous_fiber_encard {n : ℕ}
    (f : (Fin n → ℝ) × ℝ → ℝ) (hf : Continuous f) :
    Measurable (fun y => ({t : ℝ | f (y,t)=0} : Set ℝ).encard) := by
  apply ENat.measurable_iff.mpr
  intro m
  have he : {y | ({t : ℝ | f (y,t)=0} : Set ℝ).encard = (m : ℕ∞)} =
      {y | (m : ℕ∞) ≤ ({t : ℝ | f (y,t)=0} : Set ℝ).encard} \
      {y | ((m+1 : ℕ) : ℕ∞) ≤ ({t : ℝ | f (y,t)=0} : Set ℝ).encard} := by
    ext y
    simp only [mem_ofPred_eq, mem_sdiff]
    generalize ({t : ℝ | f (y,t)=0} : Set ℝ).encard = a
    cases a with
    | top => simp
    | coe a => simp only [ENat.natCast_inj, ENat.natCast_le_natCast]; omega
  change MeasurableSet {y | ({t : ℝ | f (y,t)=0} : Set ℝ).encard = (m : ℕ∞)}
  rw [he]
  exact (measurableSet_continuous_fiber_count_ge f hf m).diff
    (measurableSet_continuous_fiber_count_ge f hf (m+1))

/-- The same exact fiber count in ENNReal, suitable for crossing integrals. -/
theorem measurable_continuous_fiber_count {n : ℕ}
    (f : (Fin n → ℝ) × ℝ → ℝ) (hf : Continuous f) :
    Measurable (fun y => (({t : ℝ | f (y,t)=0} : Set ℝ).encard).toENNReal) :=
  (measurable_of_countable ENat.toENNReal).comp (measurable_continuous_fiber_encard f hf)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.measurableSet_continuous_fiber_count_ge
#print axioms KakeyaTwoScale.measurable_continuous_fiber_encard
#print axioms KakeyaTwoScale.measurable_continuous_fiber_count

