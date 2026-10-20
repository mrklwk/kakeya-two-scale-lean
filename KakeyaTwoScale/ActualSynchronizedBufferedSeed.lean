module
public import KakeyaTwoScale.BufferedStageInput
public import KakeyaTwoScale.SynchronizedSeedBalance

@[expose] public section

open Set Metric MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

/-- Actual synchronization of all incoming varieties followed by global
whole-grain balancing. Every new equation system and physical record is
constructed from the raw input, with its original-variety ancestry retained. -/
structure ActualSynchronizedBufferedSeed {b c k A B Lh J s depth : ℕ} {T C O : Type}
    [DecidableEq T] [DecidableEq C]
    (I : BufferedStageInput b c k A B Lh J s depth T C O) where
  orientations : Finset (EuclideanSpace ℝ (Fin b ⊕ Fin c) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin c))
  orientations_canonical : orientations = bufferedStageOrientations b c
  orientations_nonempty : orientations.Nonempty
  cellular_depth : ℕ
  cellular_depth_le : cellular_depth ≤ depth
  state : FrozenGeometryState (b+c) k T C O
  oldGrain : state.Grain → I.W.Grain
  equations : state.Grain → Fin (c+1) → MvPolynomial (Fin (b+c)) ℝ
  tuples_subset : state.tuples ⊆ I.W.tuples
  valid : state.Valid I.Y₀ I.cube I.tube (fun q => physicalCoordinateCube (I.Q q)) I.δ
  balanced : state.Balanced I.cube I.cubes I.alpha
  nonempty : state.tuples.Nonempty
  heights : ∀ j, state.height j ≤ Lh
  ball_radius : state.ballRadius = (A+(b+c)+5:ℝ)*I.δ*(∑ j, (2:ℝ)^(state.height j))
  ancestry : ∀ y ∈ state.tuples, oldGrain (state.grain (I.cube y))=I.W.grain (I.cube y)
  mass : tupleCubeMass I.W.tuples I.cube I.cubes I.alpha /
      (bufferedForestLoss orientations.card s depth * bufferedSeedLoss (b+c) k A Lh B *
        (((depth+1)*(Lh+1)^k:ℕ):ℝ) * (((B+1)^(k+1):ℕ):ℝ)) ≤
    tupleCubeMass state.tuples I.cube I.cubes I.alpha
  count : ∀ j, (state.count j:ℝ) ≤
    2*algebraicAxisCoverBudget (b+c) (max J (max (2*c*(J-1)) (b*(∑ i ∈ Finset.range s, I.D i)))) *
      (((b*(∑ i ∈ Finset.range s, I.D i)+1:ℕ):ℝ)^cellular_depth*(I.W.count j:ℝ))
  grain_mass_cap : ∀ g ∈ state.grains I.cube,
    tupleCubeMass (state.tuples.filter fun y => state.grain (I.cube y)=g) I.cube I.cubes I.alpha ≤
      ((2:ℝ)/2^s)^cellular_depth *
        (2*tupleCubeMass I.W.tuples I.cube I.cubes I.alpha/(I.W.grains I.cube).card)
  degrees : ∀ g i, (equations g i).totalDegree ≤
    max J (max (2*c*(J-1)) (b*(∑ i ∈ Finset.range s, I.D i)))
  regular : ∀ y ∈ state.tuples, ∀ x, rectangularPolynomialMap (equations (state.grain (I.cube y))) x=0 →
    (fderiv ℝ (rectangularPolynomialMap (equations (state.grain (I.cube y)))) x).range=⊤
  old_equations : ∀ y ∈ state.tuples, ∀ i,
    equations (state.grain (I.cube y)) i.succ =
      MvPolynomial.rename finSumFinEquiv (I.P (oldGrain (state.grain (I.cube y))) i)
  geometry : ∀ y ∈ state.tuples, ∀ j, state.geometry I.δ j (state.parent y j) ⊆
    I.W.geometry I.δ j (I.W.parent y j) ∩
      thickening ((I.R+3)*I.δ) (polynomialGrainZeroSet equations (state.grain (I.cube y)))
  axes : ∀ y ∈ state.tuples, ∀ j, state.axis j (state.parent y j)=I.W.axis j (I.W.parent y j)

namespace BufferedStageInput
variable {b c k A B Lh J s depth : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]

/-- Construct a simultaneous seed for distinct actual incoming varieties.
Finite selection, tagged physical union and global balancing are all executed
inside this theorem; no proposed stage transition is an input. -/
theorem exists_actual_synchronized_seed (I : BufferedStageInput b c k A B Lh J s depth T C O) :
    Nonempty (ActualSynchronizedBufferedSeed I) := by
  classical
  obtain ⟨S,hScanonical,hS,hseeds⟩ := I.local_seeds
  let G := {g // g ∈ I.W.grains I.cube}
  have hG : (I.W.grains I.cube).Nonempty := I.nonempty.image _
  let : Nonempty G := ⟨⟨hG.choose,hG.choose_spec⟩⟩
  let seed (g : G) := Classical.choice (hseeds g.val g.property)
  let L (g : G) := (seed g).state
  let owner (q : C) : G := if h : I.W.grain q ∈ I.W.grains I.cube then ⟨I.W.grain q,h⟩ else Classical.choice inferInstance
  have hlocal (g : G) {y : T} (hy : y ∈ (L g).tuples) : y ∈ I.W.grainTuples I.cube g := (seed g).valid.1 hy
  have hsub (g : G) : (L g).tuples ⊆ I.W.tuples := fun _ hy => I.W.grainTuples_subset I.cube g (hlocal g hy)
  have hown (g : G) (y : T) (hy : y ∈ (L g).tuples) : owner (I.cube y)=g := by
    have hg : I.W.grain (I.cube y)=g := (Finset.mem_filter.mp (hlocal g hy)).2
    apply Subtype.ext
    simp only [owner]
    rw [dite_eq_left (hg ▸ g.property)]
    exact hg
  have hroot (g : G) : I.W.grainCubes I.cube g ⊆ I.cubes := by
    intro q hq
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
    exact I.support y (I.valid.1 (I.W.grainTuples_subset I.cube g hy))
  have hsupport (g : G) (y : T) (hy : y ∈ (L g).tuples) : I.cube y ∈ I.W.grainCubes I.cube g :=
    Finset.mem_image_of_mem _ (hlocal g hy)
  have hmass (g : G) : tupleCubeMass (L g).tuples I.cube (I.W.grainCubes I.cube g) I.alpha =
      tupleCubeMass (L g).tuples I.cube I.cubes I.alpha :=
    tupleCubeMass_eq_of_support _ _ _ _ (hroot g) (hsupport g) I.exponent_pos
  have hmasspos (g : G) : 0 < tupleCubeMass (L g).tuples I.cube I.cubes I.alpha := by
    obtain ⟨y,hy⟩ := (seed g).nonempty
    exact lt_of_lt_of_le (by norm_num) (tuple_mass_one_le _ _ _ I.exponent_pos.le hy
      (hroot g (hsupport g y hy)))
  obtain ⟨bin,K,hK,hbin,hbinmass⟩ := FrozenGeometryState.exists_synchronized_seed_bin
    L (fun g => (seed g).cellular_depth) (fun g => (seed g).cellular_depth_le)
    (fun g => (seed g).heights) (fun g => tupleCubeMass (L g).tuples I.cube I.cubes I.alpha) hmasspos
  let H := {g // g ∈ K}
  let : Nonempty H := ⟨⟨hK.choose,hK.choose_spec⟩⟩
  let Lsel (i : H) := L i.val
  let selectedOwner := FrozenGeometryState.selectedSeedOwner K hK owner
  let height := fun j => (bin.2 j).val
  let radius := (A+(b+c)+5:ℝ)*I.δ*(∑ j, (2:ℝ)^(height j))
  have hh (i : H) : (Lsel i).height=height := funext (hbin i.val |>.mp i.property).2
  have hd (i : H) : (seed i.val).cellular_depth=bin.1.val := (hbin i.val |>.mp i.property).1
  have hv (i : H) : (Lsel i).Valid I.Y₀ I.cube I.tube (fun q => physicalCoordinateCube (I.Q q)) I.δ :=
    ⟨(hsub i.val).trans I.valid.1,(seed i.val).valid.2⟩
  have hold (i : H) (y : T) (hy : y ∈ (Lsel i).tuples) : I.W.grain (I.cube y)=i.val.val :=
    (Finset.mem_filter.mp (hlocal i.val hy)).2
  have hgeom (i : H) (y : T) (hy : y ∈ (Lsel i).tuples) (j : Fin k) :
      (Lsel i).geometry I.δ j ((Lsel i).parent y j) ⊆ I.W.geometry I.δ j (I.W.parent y j) :=
    ((seed i.val).geometry y hy j).trans inter_subset_left
  have hrad (i : H) : (Lsel i).ballRadius ≤ radius := by
    have h := (seed i.val).ball_radius
    change (Lsel i).ballRadius ≤ (A+(b+c)+5:ℝ)*I.δ*(∑ j, (2:ℝ)^((Lsel i).height j)) at h
    rwa [hh i] at h
  obtain ⟨V,lift,hvV,hbV,hnV,hmem,hhV,hrV,hl,hmV,hcount,hgeometry,haxes⟩ :=
    FrozenGeometryState.exists_balanced_synchronized_union (B:=B) Lsel selectedOwner I.cube height radius I.δ I.alpha
      I.Y₀ I.tube (fun q => physicalCoordinateCube (I.Q q)) I.cubes I.W I.valid
      (fun i : H => i.val.val) (fun _ _ h => Subtype.ext (Subtype.ext h)) hv
      (fun i => (seed i.val).nonempty)
      (FrozenGeometryState.selectedSeedOwner_local L owner I.cube hown K hK)
      (fun i => hsub i.val) hold hgeom hh hrad I.exponent_pos I.exponent_le_one I.support I.cardinal_bound
  let old (g : V.Grain) : I.W.Grain := (lift g).1.val.val
  let eqs (g : V.Grain) := (seed (lift g).1.val).equations ((seed (lift g).1.val).lift (lift g).2)
  have hVs : V.tuples ⊆ I.W.tuples := fun _ hy => hsub _ (hmem _ hy)
  have hmAll : tupleCubeMass I.W.tuples I.cube I.cubes I.alpha /
      (bufferedForestLoss S.card s depth * bufferedSeedLoss (b+c) k A Lh B) ≤
        ∑ g : G, tupleCubeMass (L g).tuples I.cube I.cubes I.alpha := by
    have hg := grain_subset_mass I.W.tuples I.cube I.cubes I.W.grain (I.W.grains I.cube) I.exponent_pos
    have he : I.W.tuples.filter (fun y => I.W.grain (I.cube y) ∈ I.W.grains I.cube)=I.W.tuples :=
      Finset.filter_eq_self.mpr (fun y hy => Finset.mem_image_of_mem _ hy)
    rw [he] at hg
    have hsum : (∑ g : G, tupleCubeMass (I.W.grainTuples I.cube g.val) I.cube I.cubes I.alpha) =
        tupleCubeMass I.W.tuples I.cube I.cubes I.alpha := by
      exact (Finset.sum_coe_sort (I.W.grains I.cube) (fun g => tupleCubeMass (I.W.grainTuples I.cube g) I.cube I.cubes I.alpha)).trans hg.symm
    rw [← hsum,Finset.sum_div]
    apply Finset.sum_le_sum
    intro g _
    have ht := (seed g).mass
    rw [hmass g,I.W.grainTuples_mass_on_support I.cube I.cubes g.val I.exponent_pos
      (fun y hy => I.support y (I.valid.1 hy))] at ht
    exact ht
  have hmTotal : tupleCubeMass I.W.tuples I.cube I.cubes I.alpha /
      (bufferedForestLoss S.card s depth * bufferedSeedLoss (b+c) k A Lh B *
        (((depth+1)*(Lh+1)^k:ℕ):ℝ) * (((B+1)^(k+1):ℕ):ℝ)) ≤
        tupleCubeMass V.tuples I.cube I.cubes I.alpha := by
    rw [← div_div,← div_div]
    apply (div_le_div_of_nonneg_right
      ((div_le_div_of_nonneg_right hmAll (by positivity)).trans hbinmass) (by positivity)).trans
    have he : (∑ i : H, tupleCubeMass (Lsel i).tuples I.cube I.cubes I.alpha) = ∑ i ∈ K, tupleCubeMass (L i).tuples I.cube I.cubes I.alpha :=
      Finset.sum_coe_sort K (fun i => tupleCubeMass (L i).tuples I.cube I.cubes I.alpha)
    rwa [he] at hmV
  refine ⟨{
    orientations := S
    orientations_canonical := hScanonical
    orientations_nonempty := hS
    cellular_depth := bin.1.val
    cellular_depth_le := Nat.le_of_lt_succ bin.1.isLt
    state := V
    oldGrain := old
    equations := eqs
    tuples_subset := hVs
    valid := hvV
    balanced := hbV
    nonempty := hnV
    heights := ?_
    ball_radius := ?_
    ancestry := ?_
    mass := hmTotal
    count := ?_
    grain_mass_cap := ?_
    degrees := ?_
    regular := ?_
    old_equations := ?_
    geometry := ?_
    axes := ?_ }⟩
  · intro j
    rw [hhV]
    exact Nat.le_of_lt_succ (bin.2 j).isLt
  · rw [hrV,hhV]
  · intro y hy
    dsimp only [old]
    rw [hl y hy]
    exact (hold _ y (hmem y hy)).symm
  · intro j
    have hc : (∑ i : H, ((I.W.localPhysical I.cube i.val.val I.δ).records (I.W.grainTuples I.cube i.val.val) j).card) ≤ I.W.count j := by
      simp_rw [I.W.localPhysical_count]
      have hsum := total_record_count_eq_grain_sum I.W.tuples I.cube I.W.grain (fun y => I.W.parent y j)
        (I.W.origin j) (fun y hy => I.valid.2.2.2.1 y hy j)
      have ht : (∑ g : G, grainRecordCount I.W.tuples I.cube I.W.grain (fun y => I.W.parent y j) g.val) = I.W.count j := by
        exact (Finset.sum_coe_sort (I.W.grains I.cube) (fun g => grainRecordCount I.W.tuples I.cube I.W.grain (fun y => I.W.parent y j) g)).trans hsum.symm
      calc
        _ = ∑ g ∈ K, grainRecordCount I.W.tuples I.cube I.W.grain (fun y => I.W.parent y j) g.val := Finset.sum_coe_sort _ _
        _ ≤ ∑ g : G, grainRecordCount I.W.tuples I.cube I.W.grain (fun y => I.W.parent y j) g.val :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ K)
        _ = _ := ht
    calc
      (V.count j:ℝ) ≤ ∑ i : H, ((Lsel i).count j:ℝ) := by exact_mod_cast hcount j
      _ ≤ ∑ i : H, 2*algebraicAxisCoverBudget (b+c) (max J (max (2*c*(J-1)) (b*(∑ l ∈ Finset.range s, I.D l)))) *
          (((b*(∑ l ∈ Finset.range s, I.D l)+1:ℕ):ℝ)^bin.1.val *
            (((I.W.localPhysical I.cube i.val.val I.δ).records (I.W.grainTuples I.cube i.val.val) j).card:ℝ)) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [hd i] using (seed i.val).count j
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        simp_rw [← Finset.mul_sum]
        gcongr
        exact_mod_cast hc
  · intro g hg
    apply FrozenGeometryState.synchronized_grain_mass_cap Lsel V selectedOwner I.cube I.cubes I.exponent_pos.le lift hmem hl
      (fun _ => ((2:ℝ)/2^s)^bin.1.val * (2*tupleCubeMass I.W.tuples I.cube I.cubes I.alpha/(I.W.grains I.cube).card)) ?_ g hg
    intro i t ht
    have hsupp : ∀ y ∈ (Lsel i).tuples.filter (fun y => (Lsel i).grain (I.cube y)=t), I.cube y ∈ I.W.grainCubes I.cube i.val.val :=
      fun y hy => hsupport i.val y (Finset.mem_filter.mp hy).1
    have hme := tupleCubeMass_eq_of_support _ _ _ _ (hroot i.val) hsupp I.exponent_pos
    rw [← hme]
    apply ((seed i.val).grain_mass_cap t ht).trans
    rw [hd i,I.W.grainTuples_mass_on_support I.cube I.cubes _ I.exponent_pos (fun y hy => I.support y (I.valid.1 hy))]
    apply mul_le_mul_of_nonneg_left ((I.balanced i.val.val i.val.property).1.2) (by positivity)
  · exact fun g i => (seed (lift g).1.val).degrees _ i
  · intro y hy
    dsimp only [eqs]
    rw [hl y hy]
    exact (seed (selectedOwner (I.cube y)).val).regular y (hmem y hy)
  · intro y hy i
    dsimp only [eqs,old]
    rw [hl y hy]
    exact (seed (selectedOwner (I.cube y)).val).old_equations y (hmem y hy) i
  · intro y hy j
    dsimp only [eqs,polynomialGrainZeroSet]
    rw [hl y hy,hgeometry y hy j]
    exact (seed (selectedOwner (I.cube y)).val).geometry y (hmem y hy) j
  · intro y hy j
    rw [haxes y hy j]
    exact (seed (selectedOwner (I.cube y)).val).axes y (hmem y hy) j

end BufferedStageInput
end KakeyaTwoScale
#print axioms KakeyaTwoScale.BufferedStageInput.exists_actual_synchronized_seed
