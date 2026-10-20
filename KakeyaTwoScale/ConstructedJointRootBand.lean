module
public import KakeyaTwoScale.WeightedGrainFibers
public import KakeyaTwoScale.SeedSupportTransport
public import KakeyaTwoScale.ConcreteRootState
public import KakeyaTwoScale.WeightedTupleMass

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Construct a genuine joint tuple-count band, retaining whole original
cube fibers and the actual nonlinear objective. No marginal bands enter. -/
theorem exists_constructed_joint_root_band {T C : Type*} [DecidableEq C]
    (Y : Finset T) (cube : T→C) (hne : Y.Nonempty)
    {k : ℕ} (hk : 0<k) {p : ℝ} (hp : 0<p) :
    ∃ j ≤ Y.card.log2+1, ∃ μ : ℝ, ∃ Z : Finset T,
      0<μ ∧ μ^k=(2:ℝ)^j ∧ Z=ParentLevel.selected Y cube j ∧
      Z.Nonempty ∧ Z⊆Y ∧
      (∀ q∈Z.image cube, Z.filter (fun y => cube y=q)=Y.filter (fun y => cube y=q)) ∧
      (∀ q∈Z.image cube, μ^k≤(ParentLevel.capacity Z cube q:ℝ) ∧
        (ParentLevel.capacity Z cube q:ℝ)<2*μ^k) ∧
      tupleCubeMass Y cube (Y.image cube) p ≤
        ((Y.card.log2+2:ℕ):ℝ)*tupleCubeMass Z cube (Y.image cube) p ∧
      (∀ (w : T→ℝ) (θ : ℝ), 0<θ → (∀ y∈Y, θ≤w y ∧ w y≤2*θ) →
        weightedTupleCubeMass Y cube (Y.image cube) w p /
          ((2:ℝ)^p*((Y.card.log2+2:ℕ):ℝ)) ≤
            weightedTupleCubeMass Z cube (Y.image cube) w p) := by
  classical
  have hb : Y.card ≤ 2^(Y.card.log2+1) :=
    ((Nat.log2_lt (Finset.card_ne_zero.mpr hne)).mp (by omega)).le
  obtain ⟨j,hj,hsub,hfiber,hband,hmass⟩ :=
    WeightedGrain.exists_full_fiber_rpow_selection Y cube (Y.card.log2+1)
      (fun q _ => (ParentLevel.capacity_le Y cube q).trans hb) p
  let Z := ParentLevel.selected Y cube j
  have hpos : 0<tupleCubeMass Y cube (Y.image cube) p := by
    apply Finset.sum_pos
    · intro q hq
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
      exact Real.rpow_pos_of_pos (by exact_mod_cast ParentLevel.capacity_pos Y cube hy) _
    · exact hne.image cube
  have hZ : Z.Nonempty := by
    by_contra he
    have hz : Z=∅ := Finset.not_nonempty_iff_eq_empty.mp he
    change tupleCubeMass Y cube (Y.image cube) p ≤
      ((Y.card.log2+1+1:ℕ):ℝ)*tupleCubeMass Z cube (Z.image cube) p at hmass
    rw [hz] at hmass
    simp only [Finset.image_empty,tupleCubeMass,Finset.sum_empty,mul_zero] at hmass
    exact (not_le_of_gt hpos) hmass
  let μ : ℝ := ((2:ℝ)^j)^(1/(k:ℝ))
  have hμ : 0<μ := Real.rpow_pos_of_pos (by positivity) _
  have hmupow : μ^k=(2:ℝ)^j := by
    dsimp [μ]
    rw [one_div, Real.rpow_inv_natCast_pow (by positivity) (Nat.ne_of_gt hk)]
  refine ⟨j,hj,μ,Z,hμ,hmupow,rfl,hZ,hsub,hfiber,?_,?_⟩
  · intro q hq
    rw [hmupow]
    have hh := hband q hq
    constructor
    · exact_mod_cast hh.1
    · have hh' : (ParentLevel.capacity Z cube q:ℝ)<(2:ℝ)^(j+1) := by exact_mod_cast hh.2
      simpa only [pow_succ,mul_comm] using hh'
  · have he := tupleCubeMass_eq_of_support Z cube (Z.image cube) (Y.image cube)
      (Finset.image_subset_image hsub) (fun y hy => Finset.mem_image.mpr ⟨y,hy,rfl⟩) hp
    change tupleCubeMass Y cube (Y.image cube) p ≤
      ((Y.card.log2+1+1:ℕ):ℝ)*tupleCubeMass Z cube (Z.image cube) p at hmass
    have hm : tupleCubeMass Y cube (Y.image cube) p ≤
        ((Y.card.log2+2:ℕ):ℝ)*tupleCubeMass Z cube (Y.image cube) p := by
      simpa only [he,show Y.card.log2+1+1=Y.card.log2+2 by omega] using hmass
    refine ⟨hm,?_⟩
    intro w θ hθ hw
    apply weightedTupleCubeMass_dyadic_retention Y Z hsub cube (Y.image cube) w hθ hp.le
      (by positivity) hw
    exact (div_le_iff₀ (by positivity : (0:ℝ)<((Y.card.log2+2:ℕ):ℝ))).mpr
      (by simpa only [mul_comm] using hm)

/-- The selected relation is an actual balanced physical root in the same
coarse block. Original cylinder IDs remain literal; only whole cubes are
removed. Count upper bounds are rederived from the actual subset. -/
theorem exists_concrete_joint_band_root {n k : ℕ} {O : Type} [instO : DecidableEq O]
    (Y : Finset (RootTuple n k O)) (hne : Y.Nonempty) (hk : 0<k)
    (q : ℕ) (a : Fin n→ℤ) (b u : O→EuclideanSpace ℝ (Fin n))
    (hu : ∀ o, ‖u o‖=1)
    (hloc : ∀ y∈Y, rootCoarseOwner ((2:ℝ)^q)⁻¹ y.1=a)
    (hinc : ∀ y∈Y, ∀ j, (rootGridCube ((2:ℝ)^q)⁻¹ y.1 ∩
      flatCylinder (b (y.2 j)) (u (y.2 j)) 1 ((2:ℝ)^q)⁻¹).Nonempty)
    {p : ℝ} (hp : 0<p) :
    ∃ j ≤ Y.card.log2+1, ∃ μ : ℝ, ∃ Z : Finset (RootTuple n k O),
      0<μ ∧ μ^k=(2:ℝ)^j ∧ Z=ParentLevel.selected Y Prod.fst j ∧
      Z.Nonempty ∧ Z⊆Y ∧
      (∀ z∈Z.image Prod.fst, Z.filter (fun y => y.1=z)=Y.filter (fun y => y.1=z)) ∧
      (∀ z∈Z.image Prod.fst, μ^k≤(ParentLevel.capacity Z Prod.fst z:ℝ) ∧
        (ParentLevel.capacity Z Prod.fst z:ℝ)<2*μ^k) ∧
      tupleCubeMass Y Prod.fst (Y.image Prod.fst) p ≤
        ((Y.card.log2+2:ℕ):ℝ)*tupleCubeMass Z Prod.fst (Y.image Prod.fst) p ∧
      (∀ (w : RootTuple n k O→ℝ) (θ : ℝ), 0<θ → (∀ y∈Y, θ≤w y ∧ w y≤2*θ) →
        weightedTupleCubeMass Y Prod.fst (Y.image Prod.fst) w p /
          ((2:ℝ)^p*((Y.card.log2+2:ℕ):ℝ)) ≤
            weightedTupleCubeMass Z Prod.fst (Y.image Prod.fst) w p) ∧
      let W := concreteRootState Z q a b u
      W.tuples=Z ∧ W.tuples.Nonempty ∧
      W.Valid Z Prod.fst Prod.snd (rootGridCube ((2:ℝ)^q)⁻¹) ((2:ℝ)^q)⁻¹ ∧
      W.Balanced Prod.fst (Z.image Prod.fst) p ∧
      (∀ l, W.length ((2:ℝ)^q)⁻¹ l=1) ∧
      (∀ l, W.count l≤(Y.image (fun y => y.2 l)).card) ∧
      (∀ y∈Z, ∀ l, W.original l (W.parent y l)=y.2 l) := by
  classical
  obtain ⟨j,hj,μ,Z,hμ,hpow,hZ,hneZ,hsub,hfiber,hband,hmass,hweighted⟩ :=
    exists_constructed_joint_root_band Y Prod.fst hne hk hp
  have hcoarse : coarseRootTuples Z ((2:ℝ)^q)⁻¹ a=Z :=
    Finset.filter_eq_self.mpr (fun y hy => hloc y (hsub hy))
  have hincZ := fun y hy => hinc y (hsub hy)
  refine ⟨j,hj,μ,Z,hμ,hpow,hZ,hneZ,hsub,hfiber,hband,hmass,hweighted,?_,?_,?_,?_,?_,?_,?_⟩
  · exact hcoarse
  · change (coarseRootTuples Z ((2:ℝ)^q)⁻¹ a).Nonempty
    rwa [hcoarse]
  · simpa only [hcoarse] using concreteRootState_valid Z q a b u hu hincZ
  · exact concreteRootState_balanced Z q a b u (hcoarse.symm ▸ hneZ) _ p
  · exact concreteRootState_length Z q a b u
  · intro l
    have he : (concreteRootState Z q a b u).records l=Z.image (fun y => y.2 l) := by
      change @Finset.image (RootTuple n k O) O (fun x y => Classical.propDecidable (x=y))
        (fun y => y.2 l) (coarseRootTuples Z ((2:ℝ)^q)⁻¹ a) =
        @Finset.image (RootTuple n k O) O instO (fun y => y.2 l) Z
      rw [hcoarse]
      ext o
      simp only [Finset.mem_image]
    rw [FrozenGeometryState.count,he]
    exact Finset.card_le_card (Finset.image_subset_image hsub)
  · intros; rfl

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_constructed_joint_root_band

#print axioms KakeyaTwoScale.exists_concrete_joint_band_root
