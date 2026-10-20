module
public import KakeyaTwoScale.ConstructedJointRootBand
public import KakeyaTwoScale.ConcreteRootAmbient
public import KakeyaTwoScale.FullRunLossAbsorption

@[expose] public section

open Filter
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- The literal relation cardinality is bounded from coarse cube packing and
separated unit directions. No supplied relation-size calendar is needed. -/
theorem concrete_local_relation_card_bound {n k N q : ℕ} (hq : 1≤q)
    (Y : Finset (RootTuple n k (Fin N))) (a : Fin n→ℤ)
    (u : Fin N→EuclideanSpace ℝ (Fin n)) (hu : ∀ o, ‖u o‖=1)
    (hsep : ∀ o p, o≠p → ((2:ℝ)^q)⁻¹≤Real.arccos |inner ℝ (u o) (u p)|)
    (hloc : ∀ y∈Y, rootCoarseOwner ((2:ℝ)^q)⁻¹ y.1=a) :
    Y.card≤2^(((4*k+3)*n)*q) := by
  classical
  have he : coarseRootTuples Y ((2:ℝ)^q)⁻¹ a=Y := Finset.filter_eq_self.mpr hloc
  have hh := coarseRootTuples_card_bound hq Y a u hu (fun o p hop =>
    projective_separation_half_chord (u o) (u p) (hu o) (hu p) _ (hsep o p hop))
  rw [he] at hh
  exact_mod_cast hh

/-- Actual root fiber-band count is linear in the scale, including empty
relations. The estimate is independent of translation and population size. -/
theorem concrete_local_relation_band_count {n k N q : ℕ} (hq : 1≤q)
    (Y : Finset (RootTuple n k (Fin N))) (a : Fin n→ℤ)
    (u : Fin N→EuclideanSpace ℝ (Fin n)) (hu : ∀ o, ‖u o‖=1)
    (hsep : ∀ o p, o≠p → ((2:ℝ)^q)⁻¹≤Real.arccos |inner ℝ (u o) (u p)|)
    (hloc : ∀ y∈Y, rootCoarseOwner ((2:ℝ)^q)⁻¹ y.1=a) :
    Y.card.log2+2≤(((4*k+3)*n)+2)*q := by
  have hh := concrete_local_relation_card_bound hq Y a u hu hsep hloc
  have hl : Y.card.log2≤((4*k+3)*n)*q := by
    by_cases hz : Y.card=0
    · simp [hz]
    · have hp : Y.card<2^(((4*k+3)*n)*q+1) := by
        apply hh.trans_lt
        rw [Nat.pow_succ]
        have : 0<2^(((4*k+3)*n)*q) := by positivity
        omega
      have := (Nat.log2_lt hz).mpr hp
      omega
  nlinarith

/-- Fix the dimensions, exponent p, power of the loss L, and epsilon before
choosing the scale threshold or any finite relation. Every localized original
relation then has its full weighted band-selection loss absorbed. -/
theorem eventually_concrete_root_band_loss_pow (n k : ℕ) (p L : ℝ)
    (hL : 0≤L) {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ q : ℕ in atTop, 1≤q ∧
      ∀ (N : ℕ) (Y : Finset (RootTuple n k (Fin N))) (a : Fin n→ℤ)
        (u : Fin N→EuclideanSpace ℝ (Fin n)),
      (∀ o, ‖u o‖=1) →
      (∀ o r, o≠r → ((2:ℝ)^q)⁻¹≤Real.arccos |inner ℝ (u o) (u r)|) →
      (∀ y∈Y, rootCoarseOwner ((2:ℝ)^q)⁻¹ y.1=a) →
      ((2:ℝ)^p*((Y.card.log2+2:ℕ):ℝ))^L≤(2:ℝ)^(epsilon*(q:ℝ)) := by
  let C : ℝ := (2:ℝ)^p*((((4*k+3)*n)+2:ℕ):ℝ)
  have hC : 0<C := by dsimp [C]; positivity
  have hrate : 0<epsilon*Real.log 2 := mul_pos hepsilon (Real.log_pos (by norm_num))
  filter_upwards [eventually_full_polylog_absorbed (Real.rpow_pos_of_pos hC L) L hrate,
    eventually_ge_atTop 1] with q hpoly hq
  refine ⟨hq,?_⟩
  intro N Y a u hu hsep hloc
  have hc : ((Y.card.log2+2:ℕ):ℝ)≤((((4*k+3)*n)+2:ℕ):ℝ)*(q:ℝ) := by
    exact_mod_cast concrete_local_relation_band_count hq Y a u hu hsep hloc
  have hh : (2:ℝ)^p*((Y.card.log2+2:ℕ):ℝ)≤C*(q:ℝ) := by
    simpa only [C,mul_assoc] using mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg (by norm_num) p)
  have hhL := Real.rpow_le_rpow (by positivity : 0≤(2:ℝ)^p*((Y.card.log2+2:ℕ):ℝ)) hh hL
  rw [Real.mul_rpow hC.le (Nat.cast_nonneg q)] at hhL
  apply (hhL.trans hpoly).trans_eq
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  congr 1
  ring

/-- In particular the full weighted selection loss (not merely its logarithm)
is bounded by one dyadic epsilon factor uniformly before finite root data. -/
theorem eventually_concrete_root_band_loss (n k : ℕ) (p : ℝ)
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ q : ℕ in atTop, 1≤q ∧
      ∀ (N : ℕ) (Y : Finset (RootTuple n k (Fin N))) (a : Fin n→ℤ)
        (u : Fin N→EuclideanSpace ℝ (Fin n)),
      (∀ o, ‖u o‖=1) →
      (∀ o r, o≠r → ((2:ℝ)^q)⁻¹≤Real.arccos |inner ℝ (u o) (u r)|) →
      (∀ y∈Y, rootCoarseOwner ((2:ℝ)^q)⁻¹ y.1=a) →
      (2:ℝ)^p*((Y.card.log2+2:ℕ):ℝ)≤(2:ℝ)^(epsilon*(q:ℝ)) := by
  simpa only [Real.rpow_one] using eventually_concrete_root_band_loss_pow n k p 1 (by norm_num) hepsilon

/-- Actual whole-fiber band selection with one scale-uniform epsilon loss.
Precision is fixed before N, directions, positions, relation, and its coarse
owner. The selected relation constructs a valid balanced physical root. -/
theorem eventually_exists_concrete_joint_band_root (n k : ℕ) (hk : 0<k)
    (p : ℝ) (hp : 0<p) {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ q : ℕ in atTop, 1≤q ∧
      ∀ (N : ℕ) (Y : Finset (RootTuple n k (Fin N))), Y.Nonempty →
      ∀ (a : Fin n→ℤ) (b u : Fin N→EuclideanSpace ℝ (Fin n)),
      (∀ o, ‖u o‖=1) →
      (∀ o r, o≠r → ((2:ℝ)^q)⁻¹≤Real.arccos |inner ℝ (u o) (u r)|) →
      (∀ y∈Y, rootCoarseOwner ((2:ℝ)^q)⁻¹ y.1=a) →
      (∀ y∈Y, ∀ l, (rootGridCube ((2:ℝ)^q)⁻¹ y.1 ∩
        flatCylinder (b (y.2 l)) (u (y.2 l)) 1 ((2:ℝ)^q)⁻¹).Nonempty) →
      ∃ j≤(((4*k+3)*n)+2)*q, ∃ mu : ℝ, ∃ Z : Finset (RootTuple n k (Fin N)),
        0 < mu ∧ mu^k=(2:ℝ)^j ∧ Z=ParentLevel.selected Y Prod.fst j ∧
        Z.Nonempty ∧ Z⊆Y ∧
        (∀ z∈Z.image Prod.fst, Z.filter (fun y => y.1=z)=Y.filter (fun y => y.1=z)) ∧
        (∀ z∈Z.image Prod.fst, mu^k≤(ParentLevel.capacity Z Prod.fst z:ℝ) ∧
          (ParentLevel.capacity Z Prod.fst z:ℝ)<2*mu^k) ∧
        tupleCubeMass Y Prod.fst (Y.image Prod.fst) p ≤
          (2:ℝ)^(epsilon*(q:ℝ))*tupleCubeMass Z Prod.fst (Y.image Prod.fst) p ∧
        (∀ (w : RootTuple n k (Fin N)→ℝ) (theta : ℝ), 0 < theta →
          (∀ y∈Y, theta≤w y ∧ w y≤2*theta) →
          weightedTupleCubeMass Y Prod.fst (Y.image Prod.fst) w p /
            (2:ℝ)^(epsilon*(q:ℝ))≤weightedTupleCubeMass Z Prod.fst (Y.image Prod.fst) w p) ∧
        let W := concreteRootState Z q a b u
        W.tuples=Z ∧ W.tuples.Nonempty ∧
        W.Valid Z Prod.fst Prod.snd (rootGridCube ((2:ℝ)^q)⁻¹) ((2:ℝ)^q)⁻¹ ∧
        W.Balanced Prod.fst (Z.image Prod.fst) p ∧
        (∀ l, W.length ((2:ℝ)^q)⁻¹ l=1) ∧
        (∀ l, W.count l≤(Y.image (fun y => y.2 l)).card) ∧
        (∀ y∈Z, ∀ l, W.original l (W.parent y l)=y.2 l) := by
  classical
  filter_upwards [eventually_concrete_root_band_loss n k p hepsilon] with q hq
  refine ⟨hq.1,?_⟩
  intro N Y hne a b u hu hsep hloc hinc
  have hloss := hq.2 N Y a u hu hsep hloc
  have hcount := concrete_local_relation_band_count hq.1 Y a u hu hsep hloc
  obtain ⟨j,hj,mu,Z,hmu,hpow,hZ,hneZ,hsub,hfiber,hband,hmass,hweighted,hroot⟩ :=
    exists_concrete_joint_band_root Y hne hk q a b u hu hloc hinc hp
  refine ⟨j,by omega,mu,Z,hmu,hpow,hZ,hneZ,hsub,hfiber,hband,?_,?_,hroot⟩
  · have hcoeff : ((Y.card.log2+2:ℕ):ℝ)≤(2:ℝ)^(epsilon*(q:ℝ)) := by
      apply le_trans _ hloss
      exact le_mul_of_one_le_left (by positivity) (Real.one_le_rpow (by norm_num) hp.le)
    apply hmass.trans
    apply mul_le_mul_of_nonneg_right hcoeff
    unfold tupleCubeMass
    exact Finset.sum_nonneg fun z _ => Real.rpow_nonneg (Nat.cast_nonneg _) p
  · intro w theta htheta hw
    apply le_trans _ (hweighted w theta htheta hw)
    apply div_le_div_of_nonneg_left _ (by positivity) hloss
    unfold weightedTupleCubeMass
    apply Finset.sum_nonneg
    intro z _
    apply Real.rpow_nonneg
    apply Finset.sum_nonneg
    intro y hy
    exact htheta.le.trans (hw y (Finset.mem_filter.mp hy).1).1

end KakeyaTwoScale
#print axioms KakeyaTwoScale.concrete_local_relation_card_bound
#print axioms KakeyaTwoScale.concrete_local_relation_band_count
#print axioms KakeyaTwoScale.eventually_concrete_root_band_loss_pow
#print axioms KakeyaTwoScale.eventually_concrete_root_band_loss

#print axioms KakeyaTwoScale.eventually_exists_concrete_joint_band_root
