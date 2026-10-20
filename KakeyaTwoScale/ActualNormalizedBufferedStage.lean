module
public import KakeyaTwoScale.ActualSynchronizedBufferedSeed
public import KakeyaTwoScale.FrozenPhysicalAccounting
public import KakeyaTwoScale.FrozenParentAxialBudgets

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

namespace ActualSynchronizedBufferedSeed
variable {b c k A B Lh J s depth : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
  {I : BufferedStageInput b c k A B Lh J s depth T C O}

def loss (S : ActualSynchronizedBufferedSeed I) : ℝ :=
  bufferedForestLoss S.orientations.card s depth * bufferedSeedLoss (b+c) k A Lh B *
    (((depth+1)*(Lh+1)^k:ℕ):ℝ) * (((B+1)^(k+1):ℕ):ℝ)

def crossing (S : ActualSynchronizedBufferedSeed I) : ℝ :=
  2*algebraicAxisCoverBudget (b+c) (max J (max (2*c*(J-1)) (b*(∑ i ∈ Finset.range s, I.D i)))) *
    ((b*(∑ i ∈ Finset.range s, I.D i)+1:ℕ):ℝ)^S.cellular_depth

def capFactor (S : ActualSynchronizedBufferedSeed I) : ℝ := 2*((2:ℝ)/2^s)^S.cellular_depth

def normalizationUpper (S : ActualSynchronizedBufferedSeed I) (U : ℝ) : ℝ :=
  (S.crossing*U)*(S.capFactor/(1/S.loss))^(1/(b:ℝ))

theorem loss_pos (S : ActualSynchronizedBufferedSeed I) : 0 < S.loss := by
  have hcard : (0:ℝ) < S.orientations.card := by
    exact_mod_cast Finset.card_pos.mpr S.orientations_nonempty
  dsimp [loss,bufferedForestLoss,bufferedSeedLoss]
  positivity

theorem capFactor_pos (S : ActualSynchronizedBufferedSeed I) : 0 < S.capFactor := by
  dsimp [capFactor]
  positivity

theorem crossing_nonneg (S : ActualSynchronizedBufferedSeed I) : 0 ≤ S.crossing := by
  dsimp [crossing]
  positivity

end ActualSynchronizedBufferedSeed

/-- A fully constructed normalized dimension transition. The seed is an
output of the actual polynomial construction; normalization is executed from
it. The seed-grain map is retained so all polynomial flags survive. -/
structure ActualNormalizedBufferedStage {b c k A B Lh J s depth : ℕ} {T C O : Type}
    [DecidableEq T] [DecidableEq C]
    (I : BufferedStageInput b c k A B Lh J s depth T C O)
    (N : Fin k → ℝ) (P U : ℝ) (a : ℕ) where
  seed : ActualSynchronizedBufferedSeed I
  rounds : ℕ
  state : FrozenGeometryState (b+c) k T C O
  seedGrain : state.Grain → seed.state.Grain
  valid : state.Valid I.Y₀ I.cube I.tube (fun q => physicalCoordinateCube (I.Q q)) I.δ
  balanced : state.Balanced I.cube I.cubes I.alpha
  nonempty : state.tuples.Nonempty
  subset_seed : state.tuples ⊆ seed.state.tuples
  grain_ancestry : ∀ y ∈ state.tuples, seedGrain (state.grain (I.cube y))=seed.state.grain (I.cube y)
  rounds_bound : rounds*a ≤ frozenHeightPotential a seed.state.height
  heights : ∀ j, state.height j ≤ I.W.height j
  radius : state.ballRadius ≤ (A+(b+c)+5:ℝ)*I.δ*(∑ j, (2:ℝ)^(state.height j))
  mass : tupleCubeMass I.W.tuples I.cube I.cubes I.alpha /
      (seed.loss * (((3^k*(2*(A+(b+c)+5)+1)^(b+c)*(B+1)^(k+1):ℕ):ℝ)^rounds)) ≤
    tupleCubeMass state.tuples I.cube I.cubes I.alpha
  upper : ∀ g ∈ state.grains I.cube, ∀ j,
    (grainRecordCount state.tuples I.cube state.grain (fun y => state.parent y j) g:ℝ) ≤
      ((2:ℝ)^(rounds+1)*max (seed.normalizationUpper U) ((2:ℝ)^(a+1))) *
      (N j * (P * (((state.grains I.cube).card:ℝ)/(I.W.grains I.cube).card)^(1/(b:ℝ))) /
        (state.grains I.cube).card)
  lower : ∀ g ∈ state.grains I.cube, ∀ j, 0 < state.height j →
    N j * (P * (((state.grains I.cube).card:ℝ)/(I.W.grains I.cube).card)^(1/(b:ℝ))) /
      (state.grains I.cube).card ≤
        (grainRecordCount state.tuples I.cube state.grain (fun y => state.parent y j) g:ℝ)
  geometry_seed : ∀ y ∈ state.tuples, ∀ j,
    state.geometry I.δ j (state.parent y j) ⊆ seed.state.geometry I.δ j (seed.state.parent y j)
  axes_seed : ∀ y ∈ state.tuples, ∀ j,
    state.axis j (state.parent y j)=seed.state.axis j (seed.state.parent y j)

namespace BufferedStageInput
variable {b c k A B Lh J s depth : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]

/-- Execute the actual synchronized polynomial seed and the terminating
floor-compatible normalization. Only an incoming upper count certificate is
supplied. Lower bounds are asserted exactly for positive-height families. -/
theorem exists_actual_normalized_stage (I : BufferedStageInput b c k A B Lh J s depth T C O)
    (N : Fin k → ℝ) (P U : ℝ) (a : ℕ) (ha : 0 < a)
    (hN : ∀ j, 0 ≤ N j) (hP : 0 ≤ P) (hU : 0 ≤ U)
    (hcount : ∀ j, (I.W.count j:ℝ) ≤ U*(N j*P)) :
    Nonempty (ActualNormalizedBufferedStage I N P U a) := by
  classical
  obtain ⟨S⟩ := I.exists_actual_synchronized_seed
  let q : ℝ := 1/(b:ℝ)
  let h : ℝ := (I.W.grains I.cube).card
  let beta : Fin k → ℝ := fun j => N j*P/h^q
  have hh : 0 < h := by
    dsimp [h,FrozenGeometryState.grains]
    exact_mod_cast Finset.card_pos.mpr (I.nonempty.image (I.W.grain ∘ I.cube))
  have hbR : (0:ℝ) < b := by exact_mod_cast I.dimension_pos
  have hq : 0 ≤ q := (div_pos zero_lt_one hbR).le
  have hq1 : q ≤ 1 := by
    apply (div_le_iff₀ hbR).mpr
    have hb1 : 1 ≤ b := I.dimension_pos
    exact_mod_cast (by simpa using hb1 : 1 ≤ 1*b)
  have hbeta : ∀ j, 0 ≤ beta j := fun j => div_nonneg (mul_nonneg (hN j) hP) (Real.rpow_nonneg hh.le q)
  have hmass : 0 < tupleCubeMass I.W.tuples I.cube I.cubes I.alpha := by
    obtain ⟨y,hy⟩ := I.nonempty
    exact lt_of_lt_of_le (by norm_num) (tuple_mass_one_le _ _ _ I.exponent_pos.le hy (I.support y (I.valid.1 hy)))
  have hret : (1/S.loss)*tupleCubeMass I.W.tuples I.cube I.cubes I.alpha ≤
      tupleCubeMass S.state.tuples I.cube I.cubes I.alpha := by simpa [ActualSynchronizedBufferedSeed.loss,div_eq_mul_inv,mul_comm] using S.mass
  have hcap : ∀ g ∈ S.state.grains I.cube,
      tupleCubeMass (S.state.tuples.filter fun y => S.state.grain (I.cube y)=g) I.cube I.cubes I.alpha ≤
        S.capFactor*tupleCubeMass I.W.tuples I.cube I.cubes I.alpha /
          (((I.W.grains I.cube).card:ℝ)*1) := by
    intro g hg
    convert S.grain_mass_cap g hg using 1
    dsimp [ActualSynchronizedBufferedSeed.capFactor]
    ring
  have hct : ∀ j, (S.state.count j:ℝ) ≤ (S.crossing*U)*(N j*P)*(1:ℝ)^q := by
    intro j
    have hc : (S.state.count j:ℝ) ≤ S.crossing*(I.W.count j:ℝ) := by
      simpa only [ActualSynchronizedBufferedSeed.crossing,mul_assoc] using S.count j
    have hh := hc.trans (mul_le_mul_of_nonneg_left (hcount j) S.crossing_nonneg)
    simpa only [Real.one_rpow,mul_one,mul_assoc] using hh
  have hseed := FrozenGeometryState.actual_seed_normalized_count I.W S.state I.cube I.cubes N P
    I.exponent_pos hq (div_pos zero_lt_one S.loss_pos) S.capFactor_pos (by norm_num : (0:ℝ)<1)
    (mul_nonneg S.crossing_nonneg hU) hP hN I.nonempty S.nonempty hmass hret hcap hct
  obtain ⟨R,V,hv,hbal,hne,hVS,hlower,hR,hheight,hradius,hm,hcounts,hgeom,haxis,lift,hlift⟩ :=
    FrozenGeometryState.exists_frozen_normalization S.state I.Y₀ I.cube I.tube
      (fun q => physicalCoordinateCube (I.Q q)) I.cubes I.center I.width_pos I.exponent_pos
      I.exponent_le_one hq hq1 ha S.valid S.balanced S.nonempty I.support I.cardinal_bound
      I.cube_radius beta hbeta (by simpa only [Nat.cast_add] using S.ball_radius.le)
  let h' : ℝ := (V.grains I.cube).card
  have hh' : 0 < h' := by
    dsimp [h',FrozenGeometryState.grains]
    exact_mod_cast Finset.card_pos.mpr (hne.image (V.grain ∘ I.cube))
  let normLoss : ℝ := ((3^k*(2*(A+(b+c)+5)+1)^(b+c)*(B+1)^(k+1):ℕ):ℝ)
  have hL : 0 < normLoss := by dsimp [normLoss]; positivity
  have ht (j) : beta j*h'^(q-1)=
      N j*(P*(h'/h)^q)/h' := dimension_stage_target_identity hh hh'
  have hupper (j) : (V.count j:ℝ) ≤
      ((2:ℝ)^R*max (S.normalizationUpper U) ((2:ℝ)^(a+1)))*beta j*h'^q := by
    have hs : S.state.normalizedCount I.cube q j ≤ S.normalizationUpper U*beta j := hseed j
    have hm' : max (S.state.normalizedCount I.cube q j) (beta j*(2:ℝ)^(a+1)) ≤
        max (S.normalizationUpper U) ((2:ℝ)^(a+1))*beta j := by
      apply max_le
      · exact hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hbeta j))
      · simpa only [mul_comm] using mul_le_mul_of_nonneg_right
          (le_max_right (S.normalizationUpper U) ((2:ℝ)^(a+1))) (hbeta j)
    have hc := (hcounts j).trans (mul_le_mul_of_nonneg_left hm' (by positivity))
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hh' q)).mp (by
      simpa only [FrozenGeometryState.normalizedCount,mul_assoc] using hc)
  have hgW : ∀ y ∈ V.tuples, ∀ j,
      V.geometry I.δ j (V.parent y j) ⊆ I.W.geometry I.δ j (I.W.parent y j) :=
    fun y hy j => (hgeom y hy j).trans (((S.geometry y (hVS hy) j).trans inter_subset_left))
  have haW : ∀ y ∈ V.tuples, ∀ j,
      V.axis j (V.parent y j)=I.W.axis j (I.W.parent y j) :=
    fun y hy j => (haxis y hy j).trans (S.axes y (hVS hy) j)
  have hheightW := (FrozenGeometryState.physical_transition_accounting I.W V I.Y₀ I.cube I.tube
    (fun q => physicalCoordinateCube (I.Q q)) I.δ I.width_pos I.valid hv hne
    (hVS.trans S.tuples_subset) hgW haW).1
  refine ⟨{
    seed := S
    rounds := R
    state := V
    seedGrain := lift
    valid := hv
    balanced := hbal
    nonempty := hne
    subset_seed := hVS
    grain_ancestry := hlift
    rounds_bound := hR
    heights := hheightW
    radius := by simpa only [Nat.cast_add] using hradius
    mass := ?_
    upper := ?_
    lower := ?_
    geometry_seed := hgeom
    axes_seed := haxis }⟩
  · have hhret := (div_le_div_of_nonneg_right S.mass (pow_nonneg hL.le R)).trans hm
    simpa only [ActualSynchronizedBufferedSeed.loss,div_div,normLoss] using hhret
  · intro g hg j
    have hc := (hbal g hg).2 j |>.2
    have hu := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hupper j) (by norm_num : (0:ℝ)≤2)) hh'.le
    have he : 2*(((2:ℝ)^R*max (S.normalizationUpper U) ((2:ℝ)^(a+1)))*beta j*h'^q)/h' =
        ((2:ℝ)^(R+1)*max (S.normalizationUpper U) ((2:ℝ)^(a+1)))*(N j*(P*(h'/h)^q)/h') := by
      rw [← ht j,Real.rpow_sub hh',Real.rpow_one,pow_succ]
      ring
    exact hc.trans (hu.trans_eq he)
  · intro g hg j hj
    rw [← ht j]
    exact FrozenGeometryState.active_grain_lower_count V I.cube I.cubes beta hne hbal hlower hg j hj

end BufferedStageInput
end KakeyaTwoScale
#print axioms KakeyaTwoScale.BufferedStageInput.exists_actual_normalized_stage
