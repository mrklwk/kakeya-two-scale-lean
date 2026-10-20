module
public import KakeyaTwoScale.ActualNormalizedBufferedStage

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ActualNormalizedBufferedStage
attribute [local instance] Classical.propDecidable
variable {b c k A B Lh J s depth : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
  {I : BufferedStageInput b c k A B Lh J s depth T C O} {N : Fin k → ℝ} {P U : ℝ} {a : ℕ}

abbrev equations (Z : ActualNormalizedBufferedStage I N P U a) := fun g => Z.seed.equations (Z.seedGrain g)
abbrev oldGrain (Z : ActualNormalizedBufferedStage I N P U a) := Z.seed.oldGrain ∘ Z.seedGrain

theorem tuples_subset (Z : ActualNormalizedBufferedStage I N P U a) : Z.state.tuples ⊆ I.W.tuples :=
  Z.subset_seed.trans Z.seed.tuples_subset

theorem old_grain (Z : ActualNormalizedBufferedStage I N P U a) :
    ∀ y ∈ Z.state.tuples, Z.oldGrain (Z.state.grain (I.cube y))=I.W.grain (I.cube y) := by
  intro y hy
  exact (congrArg Z.seed.oldGrain (Z.grain_ancestry y hy)).trans (Z.seed.ancestry y (Z.subset_seed hy))

theorem degrees (Z : ActualNormalizedBufferedStage I N P U a) :
    ∀ g i, (Z.equations g i).totalDegree ≤
      max J (max (2*c*(J-1)) (b*(∑ i ∈ Finset.range s, I.D i))) :=
  fun g i => Z.seed.degrees (Z.seedGrain g) i

theorem regular (Z : ActualNormalizedBufferedStage I N P U a) :
    ∀ g ∈ Z.state.grains I.cube, ∀ x, rectangularPolynomialMap (Z.equations g) x=0 →
      (fderiv ℝ (rectangularPolynomialMap (Z.equations g)) x).range=⊤ := by
  classical
  intro g hg
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hg
  simpa only [equations,Function.comp_apply,Z.grain_ancestry y hy] using Z.seed.regular y (Z.subset_seed hy)

theorem old_equations (Z : ActualNormalizedBufferedStage I N P U a) :
    ∀ y ∈ Z.state.tuples, ∀ i, Z.equations (Z.state.grain (I.cube y)) i.succ =
      MvPolynomial.rename finSumFinEquiv (I.P (I.W.grain (I.cube y)) i) := by
  intro y hy i
  simpa only [equations,Z.grain_ancestry y hy,Z.seed.ancestry y (Z.subset_seed hy)] using
    Z.seed.old_equations y (Z.subset_seed hy) i

theorem geometry (Z : ActualNormalizedBufferedStage I N P U a) :
    ∀ y ∈ Z.state.tuples, ∀ j, Z.state.geometry I.δ j (Z.state.parent y j) ⊆
      I.W.geometry I.δ j (I.W.parent y j) ∩
        thickening ((I.R+3)*I.δ) (polynomialGrainZeroSet Z.equations (Z.state.grain (I.cube y))) := by
  intro y hy j
  have h := (Z.geometry_seed y hy j).trans (Z.seed.geometry y (Z.subset_seed hy) j)
  simpa only [polynomialGrainZeroSet,equations,Z.grain_ancestry y hy] using h

theorem axes (Z : ActualNormalizedBufferedStage I N P U a) :
    ∀ y ∈ Z.state.tuples, ∀ j, Z.state.axis j (Z.state.parent y j)=I.W.axis j (I.W.parent y j) :=
  fun y hy j => (Z.axes_seed y hy j).trans (Z.seed.axes y (Z.subset_seed hy) j)

theorem capture (Z : ActualNormalizedBufferedStage I N P U a) :
    ∀ y ∈ Z.state.tuples, ∀ j, Z.state.geometry I.δ j (Z.state.parent y j) ⊆
      thickening ((I.R+3)*I.δ) {x | rectangularPolynomialMap (Z.equations (Z.state.grain (I.cube y))) x=0} := by
  intro y hy j
  have he : polynomialGrainZeroSet Z.equations (Z.state.grain (I.cube y)) =
      {x | rectangularPolynomialMap (Z.equations (Z.state.grain (I.cube y))) x=0} := by
    ext x
    simp only [polynomialGrainZeroSet,Set.mem_ofPred_eq]
    change (∀ i, MvPolynomial.eval (fun j => x j) (Z.equations (Z.state.grain (I.cube y)) i)=0) ↔ _
    constructor
    · intro h; exact PiLp.ext (fun i => h i)
    · intro h i; exact congrArg (fun z : EuclideanSpace ℝ (Fin (c+1)) => z i) h
  rw [← he]
  exact (Z.geometry y hy j).trans inter_subset_right

def degree (Z : ActualNormalizedBufferedStage I N P U a) : ℝ :=
  (((Z.state.grains I.cube).card:ℝ)/(I.W.grains I.cube).card)^(1/(b:ℝ))

def retentionLoss (Z : ActualNormalizedBufferedStage I N P U a) : ℝ :=
  Z.seed.loss * (((3^k*(2*(A+(b+c)+5)+1)^(b+c)*(B+1)^(k+1):ℕ):ℝ)^Z.rounds)

def upperFactor (Z : ActualNormalizedBufferedStage I N P U a) : ℝ :=
  (2:ℝ)^(Z.rounds+1)*max (Z.seed.normalizationUpper U) ((2:ℝ)^(a+1))

theorem degree_pos (Z : ActualNormalizedBufferedStage I N P U a) : 0 < Z.degree := by
  have hh : (0:ℝ) < (I.W.grains I.cube).card := by exact_mod_cast Finset.card_pos.mpr (I.nonempty.image _)
  have hh' : (0:ℝ) < (Z.state.grains I.cube).card := by exact_mod_cast Finset.card_pos.mpr (Z.nonempty.image _)
  exact Real.rpow_pos_of_pos (div_pos hh' hh) _

theorem degree_identity (Z : ActualNormalizedBufferedStage I N P U a) :
    ((Z.state.grains I.cube).card:ℝ)=((I.W.grains I.cube).card:ℝ)*Z.degree^(b:ℝ) := by
  apply dimension_stage_degree_identity
  · exact_mod_cast Finset.card_pos.mpr (I.nonempty.image _)
  · exact_mod_cast Finset.card_pos.mpr (Z.nonempty.image _)
  · exact_mod_cast I.dimension_pos

theorem retentionLoss_pos (Z : ActualNormalizedBufferedStage I N P U a) : 0 < Z.retentionLoss := by
  exact mul_pos Z.seed.loss_pos (pow_pos (by positivity) _)

theorem upperFactor_pos (Z : ActualNormalizedBufferedStage I N P U a) : 0 < Z.upperFactor := by
  apply mul_pos (by positivity)
  exact lt_of_lt_of_le (by positivity : (0:ℝ)<2^(a+1)) (le_max_right _ _)

theorem grain_survival (Z : ActualNormalizedBufferedStage I N P U a) :
    (1/Z.retentionLoss)*((I.W.grains I.cube).card:ℝ) ≤ 2*((Z.state.grains I.cube).card:ℝ) := by
  classical
  have hmass : 0 < tupleCubeMass I.W.tuples I.cube I.cubes I.alpha := by
    obtain ⟨y,hy⟩ := I.nonempty
    exact lt_of_lt_of_le (by norm_num) (tuple_mass_one_le _ _ _ I.exponent_pos.le hy (I.support y (I.valid.1 hy)))
  apply selected_child_card_survival I.W.tuples Z.state.tuples I.cube I.cubes I.W.grain
    Z.state.grain Z.oldGrain Z.tuples_subset Z.old_grain I.exponent_pos (by norm_num) hmass
  · simpa only [retentionLoss,one_div,div_eq_mul_inv,mul_comm,one_mul] using Z.mass
  · exact fun g hg => (I.balanced g hg).1.2

theorem total_count (Z : ActualNormalizedBufferedStage I N P U a) :
    ∀ j, (Z.state.count j:ℝ) ≤ Z.upperFactor*(N j*(P*Z.degree)) := by
  classical
  intro j
  have hh : (0:ℝ) < (Z.state.grains I.cube).card := by exact_mod_cast Finset.card_pos.mpr (Z.nonempty.image _)
  have hc := total_record_count_eq_grain_sum Z.state.tuples I.cube Z.state.grain
    (fun y => Z.state.parent y j) (Z.state.origin j) (fun y hy => Z.valid.2.2.2.1 y hy j)
  have hcR : (Z.state.count j:ℝ) = ∑ g ∈ Z.state.grains I.cube,
      (grainRecordCount Z.state.tuples I.cube Z.state.grain (fun y => Z.state.parent y j) g:ℝ) := by
    exact_mod_cast hc
  rw [hcR]
  have hs := Finset.sum_le_sum (fun g hg => Z.upper g hg j)
  apply hs.trans_eq
  simp only [Finset.sum_const,nsmul_eq_mul]
  dsimp [upperFactor,degree]
  field_simp

/-- Deduplicated axial budgets are derived from the constructed transition. -/
theorem axial (Z : ActualNormalizedBufferedStage I N P U a) :
    ∀ j, Z.state.length I.δ j*(Z.state.count j:ℝ) ≤ I.W.length I.δ j*(I.W.count j:ℝ) :=
  (FrozenGeometryState.physical_transition_accounting I.W Z.state I.Y₀ I.cube I.tube
    (fun q => physicalCoordinateCube (I.Q q)) I.δ I.width_pos I.valid Z.valid Z.nonempty
    Z.tuples_subset (fun y hy j => (Z.geometry y hy j).trans inter_subset_left) Z.axes).2

end ActualNormalizedBufferedStage
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.regular
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.capture
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.degree_identity
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.grain_survival
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.total_count
#print axioms KakeyaTwoScale.ActualNormalizedBufferedStage.axial
