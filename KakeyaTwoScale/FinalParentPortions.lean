module
public import KakeyaTwoScale.RoundedParentPruning
public import KakeyaTwoScale.SafeParentDeletion

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- The complete source deletion chain for the actual rounded parent level.
Arithmetic pruning, measurable whole-cell high-overlap deletion and short-
portion deletion together retain U/4. The family, weights, assignments and
capacities remain the original ones throughout. -/
theorem rounded_parent_final_portions (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d r : ℝ) (hd : 0 < d) (hr : 0 < r),
      ∀ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)),
      Set.InjOn Prod.snd (↑G : Set ((Fin n → ℤ) × (Fin n → ℤ))) →
      ∀ (z w : Fin n → ℝ) (level : ℕ),
      let b := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.1+z
      let v := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.2+w
      let F := RoundedParentLevel.fixed G b v level (d^n) r (pow_pos hd n) hr
      let U := d^n*(F.children.card:ℝ)
      ∀ (I : ((Fin n → ℤ) × (Fin n → ℤ)) → Set ℝ) (V : ℝ), 0 < V →
      (∀ j, MeasurableSet (I j) ∧ I j ⊆ Set.Icc (0:ℝ) 1) →
      3*U/8 ≤ F.portionMass volume I →
      volume.real (occupiedGridRegion F.children b v r (fun _ => Set.Icc (0:ℝ) 1)) ≤ V →
      ∃ J : ((Fin n → ℤ) × (Fin n → ℤ)) → Set ℝ,
      (∀ j, MeasurableSet (J j) ∧ J j ⊆ I j) ∧
      (∀ p ∈ F.parents, ∀ t cell,
        ((F.children.filter (fun j => F.assign j=p ∧ t ∈ J j ∧
          gridIndex d (segmentPoint (b j) (v j) t)=cell)).card:ℝ) ≤
          C*(r/d)^((n:ℝ)*theta)*F.weight^theta) ∧
      let M := ((1/100:ℝ)*U)/V
      let K := F.longPortions volume (fun j => safeRetainedHeights F.parents
        (RoundedParentLevel.parentBase r) (RoundedParentLevel.parentSlope r)
        (b j) (v j) F.weight r M (J j)) (1/100)
      (∀ j, MeasurableSet (K j) ∧ K j ⊆ I j) ∧
      U/4 ≤ F.portionMass volume K ∧
      (∀ p ∈ F.parents, ∀ t cell,
        ((F.children.filter (fun j => F.assign j=p ∧ t ∈ K j ∧
          gridIndex d (segmentPoint (b j) (v j) t)=cell)).card:ℝ) ≤
          C*(r/d)^((n:ℝ)*theta)*F.weight^theta) := by
  obtain ⟨C,hC,hprune⟩ := rounded_parent_lattice_pruning n (1/100) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro d r hd hr G hinj z w level
  dsimp only
  let b := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.1+z
  let v := fun j : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint d j.2+w
  let F := RoundedParentLevel.fixed G b v level (d^n) r (pow_pos hd n) hr
  let U := d^n*(F.children.card:ℝ)
  intro I V hV hI hmass hvol
  obtain ⟨J,hJ,hJmass,hcap⟩ := hprune d r hd hr G hinj z w level I hI
  refine ⟨J,hJ,hcap,?_⟩
  let M := ((1/100:ℝ)*U)/V
  let K := F.longPortions volume (fun j => safeRetainedHeights F.parents
    (RoundedParentLevel.parentBase r) (RoundedParentLevel.parentSlope r)
    (b j) (v j) F.weight r M (J j)) (1/100)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hKJ (j) : K j ⊆ J j := (F.longPortions_subset volume _ (1/100) j).trans Set.inter_subset_left
  have hKm (j) : MeasurableSet (K j) :=
    F.longPortions_measurable volume _ (1/100)
      (measurableSet_safeRetainedHeights F.parents _ _ (b j) (v j) F.weight r M (hJ j).1)
  refine ⟨fun j => ⟨hKm j,(hKJ j).trans (hJ j).2⟩,?_,?_⟩
  · have hs := safe_long_mass_volume F b v (RoundedParentLevel.parentBase r)
      (RoundedParentLevel.parentSlope r) hr rfl M (1/100) hM (by norm_num) J
      (fun j _ => (hJ j).1) (fun j _ => (hJ j).2.trans (hI j).2)
      (fun j _ => rfl) (fun j _ => rfl)
    have hsmall := mul_le_mul_of_nonneg_left hvol (show 0 ≤ 2*M by positivity)
    have hthreshold : M*V=U/100 := by dsimp [M]; field_simp
    change F.portionMass volume I-(1/100)*d^n*F.children.card ≤ F.portionMass volume J at hJmass
    change F.portionMass volume J-2*M*volume.real
      (occupiedGridRegion F.children b v r (fun _ => Set.Icc (0:ℝ) 1))-
      (1/100)*d^n*F.children.card ≤ F.portionMass volume K at hs
    change U/4 ≤ F.portionMass volume K
    change 3*U/8 ≤ F.portionMass volume I at hmass
    have hcharge : (1/100:ℝ)*d^n*F.children.card=U/100 := by dsimp [U]; ring
    rw [hcharge] at hJmass hs
    nlinarith
  · intro p hp t cell
    have hs : F.children.filter (fun j => F.assign j=p ∧ t ∈ K j ∧
        gridIndex d (segmentPoint (b j) (v j) t)=cell) ⊆
        F.children.filter (fun j => F.assign j=p ∧ t ∈ J j ∧
        gridIndex d (segmentPoint (b j) (v j) t)=cell) := by
      intro j hj
      obtain ⟨hj,hp,ht,hcell⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hj,hp,hKJ j ht,hcell⟩
    have hcard := (Nat.cast_le (α:=ℝ)).mpr (Finset.card_le_card hs)
    have hh := hcard.trans (hcap p hp t cell)
    convert hh using 1

end KakeyaTwoScale
#print axioms KakeyaTwoScale.rounded_parent_final_portions
