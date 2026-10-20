module
public import KakeyaTwoScale.KakeyaGraphExtraction
public import KakeyaTwoScale.GlobalParentMass

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical

abbrev dyadicLatticeBase (n q : ℕ) (j : RoundedParentLevel.Parent n) : Fin n → ℝ :=
  latticePoint (dyadicRadius (20*q)) j.1

abbrev dyadicLatticeSlope (n q : ℕ) (j : RoundedParentLevel.Parent n) : Fin n → ℝ :=
  latticePoint (dyadicRadius (20*q)) j.2

/-- The actual original-capacity selected rounded family at the source scales. -/
def dyadicRoundedFamily (n : ℕ) (G : Finset (RoundedParentLevel.Parent n)) (level q : ℕ) :=
  RoundedParentLevel.fixed G (dyadicLatticeBase n q) (dyadicLatticeSlope n q) level
    ((dyadicRadius (20*q))^n) (dyadicRadius q) (pow_pos (Real.exp_pos _) n) (Real.exp_pos _)

/-- A package of constructed finite data; existence below follows from actual
unit segments in K. The family and every parent retain their literal geometry. -/
structure KakeyaScaleData (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin (n+1))))
    (R : ℝ) (q : ℕ) (cU : ℝ) where
  G : Finset (RoundedParentLevel.Parent n)
  level : ℕ
  s : ℝ
  trueBase : RoundedParentLevel.Parent n → Fin n → ℝ
  slope_injective : Set.InjOn Prod.snd (↑G : Set (RoundedParentLevel.Parent n))
  card_bound : G.card ≤ 2^((20*n)*q+n)
  level_bound : level ≤ (20*n)*q+n
  trueBase_bound : ∀ j ∈ G, ‖trueBase j‖ ≤ R
  base_bound : ∀ j ∈ G, ‖dyadicLatticeBase n q j‖ ≤ R+1
  slope_bound : ∀ j ∈ G, ‖dyadicLatticeSlope n q j‖ ≤ 1
  base_rounding : ∀ j ∈ G,
    dyadicLatticeBase n q j=gridRound (dyadicRadius (20*q)) (trueBase j)
  axis_containment : ∀ j ∈ G, ∀ t ∈ Set.Icc (0:ℝ) 1,
    euclideanUnsplit 0 (heightAffine s (tubeChartLength n)
      (t,segmentPoint (trueBase j) (dyadicLatticeSlope n q j) t)) ∈ K
  selected_nonempty : (dyadicRoundedFamily n G level q).children.Nonempty
  retained_mass : cU/((q:ℝ)+1) ≤
    (dyadicRadius (20*q))^n*((dyadicRoundedFamily n G level q).children.card:ℝ)

/-- Uniform selected mass and every geometric field are derived, for all q,
from genuine unit segments and one fixed positional bound. -/
theorem exists_kakeya_scale_data (n : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (K : Set (EuclideanSpace ℝ (Fin (n+1)))) (hK : ContainsUnitSegments K)
    (hbound : ∀ x ∈ K, ‖x‖ ≤ R) :
    ∃ cU : ℝ, 0 < cU ∧ ∀ q : ℕ, Nonempty (KakeyaScaleData n K R q cU) := by
  obtain ⟨c,hc,hextract⟩ := kakeya_lattice_extraction n R hR
  refine ⟨c/(20*n+n+1:ℕ),by positivity,?_⟩
  intro q
  have hd : 0 < dyadicRadius (20*q) := Real.exp_pos _
  have hr : 0 < dyadicRadius q := Real.exp_pos _
  have hdone : dyadicRadius (20*q) ≤ 1 := by
    unfold dyadicRadius
    apply Real.exp_le_one_iff.mpr
    have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) (Nat.cast_nonneg _)
  obtain ⟨G,hG,hinj,hmass,hupper,s,b₀,hgeometry⟩ :=
    hextract K hK hbound (dyadicRadius (20*q)) hd hdone
  have hcard := dyadic_lattice_card_bound n q G.card hupper
  obtain ⟨level,hlevel,hret,hne⟩ := ParentLevel.exists_fixed_level_uniform_mass G
    (RoundedParentLevel.assign (dyadicRadius q) (dyadicLatticeBase n q) (dyadicLatticeSlope n q))
    ((dyadicRadius (20*q))^n) ((dyadicRadius q)^n) c (pow_pos hd n) (pow_pos hr n) hc
    (20*n) n q hcard hmass
  exact ⟨{
    G := G
    level := level
    s := s
    trueBase := b₀
    slope_injective := hinj
    card_bound := hcard
    level_bound := hlevel
    trueBase_bound := fun j hj => (hgeometry j hj).1
    base_bound := fun j hj => (hgeometry j hj).2.1
    slope_bound := fun j hj => (hgeometry j hj).2.2.1
    base_rounding := fun j hj => (hgeometry j hj).2.2.2.1
    axis_containment := fun j hj => (hgeometry j hj).2.2.2.2
    selected_nonempty := hne
    retained_mass := hret }⟩

/-- Boundedness supplies the fixed positional radius; no radius witness or
finite-scale geometric data need be supplied by the caller. -/
theorem bounded_kakeya_scale_data (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin (n+1)))) (hK : ContainsUnitSegments K)
    (hbounded : Bornology.IsBounded K) :
    ∃ R cU : ℝ, 0 < R ∧ 0 < cU ∧
      ∀ q : ℕ, Nonempty (KakeyaScaleData n K R q cU) := by
  obtain ⟨R,hR,hbound⟩ := hbounded.exists_pos_norm_le
  obtain ⟨cU,hcU,hdata⟩ := exists_kakeya_scale_data n R hR.le K hK hbound
  exact ⟨R,cU,hR,hcU,hdata⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_kakeya_scale_data

#print axioms KakeyaTwoScale.bounded_kakeya_scale_data
