module
public import KakeyaTwoScale.FrozenGeometryState

@[expose] public section

open Set
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
namespace KakeyaTwoScale
namespace FrozenGeometryState

def Balanced {n k : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    (S : FrozenGeometryState n k T C O) (cube : T → C) (cubes : Finset C) (p : ℝ) : Prop := by
  classical
  exact ∀ g ∈ S.grains cube,
    (tupleCubeMass S.tuples cube cubes p/(2*(S.grains cube).card) ≤
      tupleCubeMass (S.tuples.filter fun y => S.grain (cube y)=g) cube cubes p ∧
      tupleCubeMass (S.tuples.filter fun y => S.grain (cube y)=g) cube cubes p ≤
        2*tupleCubeMass S.tuples cube cubes p/(S.grains cube).card) ∧
    ∀ j, (S.count j:ℝ)/(2*(S.grains cube).card) ≤ grainRecordCount S.tuples cube S.grain (fun y => S.parent y j) g ∧
      (grainRecordCount S.tuples cube S.grain (fun y => S.parent y j) g:ℝ) ≤ 2*S.count j/(S.grains cube).card

/-- Actual whole-grain balancing constructs another valid geometric state
with the same exact heights and geometry. No count array is assumed. -/
theorem exists_balanced_state {n k B : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    (S : FrozenGeometryState n k T C O) (Y₀ : Finset T) (cube : T → C)
    (tube : T → Fin k → O) (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (cubes : Finset C) {δ p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hv : S.Valid Y₀ cube tube Q δ) (hne : S.tuples.Nonempty)
    (hcubes : ∀ y ∈ S.tuples, cube y ∈ cubes) (hbound : (S.tuples.card:ℝ) ≤ (2:ℝ)^B) :
    ∃ (S' : FrozenGeometryState n k T C O) (lift : S'.Grain → S.Grain),
      S'.Valid Y₀ cube tube Q δ ∧ S'.Balanced cube cubes p ∧ S'.tuples.Nonempty ∧
      S'.tuples ⊆ S.tuples ∧ S'.height=S.height ∧ S'.ballRadius=S.ballRadius ∧
      (∀ y ∈ S'.tuples, lift (S'.grain (cube y))=S.grain (cube y)) ∧
      tupleCubeMass S.tuples cube cubes p / (((B+1)^(k+1):ℕ):ℝ) ≤ tupleCubeMass S'.tuples cube cubes p ∧
      (∀ j, S'.count j ≤ S.count j) ∧
      (∀ (G : Type) (f : S.Grain → G) g j, grainRecordCount S'.tuples cube (f ∘ lift ∘ S'.grain) (fun y => S'.parent y j) g ≤
        grainRecordCount S.tuples cube (f ∘ S.grain) (fun y => S.parent y j) g) ∧
      (∀ y ∈ S'.tuples, ∀ j, S'.geometry δ j (S'.parent y j)=S.geometry δ j (S.parent y j)) ∧
      (∀ y ∈ S'.tuples, ∀ j, S'.axis j (S'.parent y j)=S.axis j (S.parent y j)) := by
  classical
  obtain ⟨band,R,hRS,hmass,hbands,hrecords⟩ := balanced_actual_grains S.tuples cube cubes S.grain S.parent
    hp hp1 hcubes hbound
  let Z := S.tuples.filter fun y => S.grain (cube y) ∈ R
  let S' : FrozenGeometryState n k T C O := { S with tuples := Z }
  have hZS : Z ⊆ S.tuples := Finset.filter_subset _ _
  have hpos : 0 < tupleCubeMass Z cube cubes p := by
    obtain ⟨y,hy⟩ := hne
    have hh := tuple_mass_one_le S.tuples cube cubes hp.le hy (hcubes y hy)
    have hd : (0:ℝ) < (((B+1)^(k+1):ℕ):ℝ) := by positivity
    exact (div_pos (by linarith) hd).trans_le hmass
  have hZ : Z.Nonempty := Finset.card_pos.mp (by
    have hh := tuple_mass_le_card Z cube cubes hp hp1
    exact_mod_cast (hpos.trans_le hh))
  have hgrains : S'.grains cube=R := by
    ext g
    simp only [grains,S',Z,Finset.mem_image,Finset.mem_filter,Function.comp_apply]
    constructor
    · rintro ⟨y,⟨hy,hR⟩,rfl⟩
      exact hR
    · intro hg
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp (hRS hg)
      change S.grain (cube y)=g at he
      exact ⟨y,⟨hy,by simpa only [he] using hg⟩,he⟩
  have hR : R.Nonempty := by
    rw [← hgrains]
    exact hZ.image _
  have hvalid : S'.Valid Y₀ cube tube Q δ := by
    refine ⟨hZS.trans hv.1,hv.2.1,?_,?_,?_,?_,?_⟩
    · exact fun y hy j => hv.2.2.1 y (hZS hy) j
    · exact fun y hy j => hv.2.2.2.1 y (hZS hy) j
    · exact fun y hy j => hv.2.2.2.2.1 y (hZS hy) j
    · intro j o s hs t ht hst
      exact hv.2.2.2.2.2.1 j o ⟨Finset.image_subset_image hZS hs.1,hs.2⟩
        ⟨Finset.image_subset_image hZS ht.1,ht.2⟩ hst
    · exact fun y hy => hv.2.2.2.2.2.2 y (hZS hy)
  have hbalanced : S'.Balanced cube cubes p := by
    intro g hg
    have hgR : g ∈ R := by simpa only [hgrains] using hg
    have hmass_eq : tupleCubeMass S'.tuples cube cubes p =
        ∑ t ∈ R, tupleCubeMass (S.tuples.filter fun y => S.grain (cube y)=t) cube cubes p :=
      grain_subset_mass S.tuples cube cubes S.grain R hp
    have hlocal_mass (t : S.Grain) (ht : t ∈ R) :
        tupleCubeMass (S'.tuples.filter fun y => S'.grain (cube y)=t) cube cubes p =
          tupleCubeMass (S.tuples.filter fun y => S.grain (cube y)=t) cube cubes p := by
      congr 1
      ext y
      simp only [S',Z,Finset.mem_filter]
      constructor
      · exact fun h => ⟨h.1.1,h.2⟩
      · intro h
        exact ⟨⟨h.1,by simpa only [h.2] using ht⟩,h.2⟩
    constructor
    · have hh := band_average_bounds R
        (fun t => tupleCubeMass (S.tuples.filter fun y => S.grain (cube y)=t) cube cubes p) hR
        (a:=(2:ℝ)^(band 0).val) (by
          intro t ht
          have hb := hbands t ht 0
          simp only [actualGrainQuantity,Fin.cases_zero,pow_succ] at hb
          exact ⟨hb.1,by nlinarith [hb.2]⟩) g hgR
      simpa only [hmass_eq,hgrains,hlocal_mass g hgR] using hh
    · intro j
      have hsum : (S'.count j:ℝ) = ∑ t ∈ R,
          (grainRecordCount S.tuples cube S.grain (fun y => S.parent y j) t:ℝ) := by
        have hh := total_record_count_eq_grain_sum S'.tuples cube S'.grain (fun y => S'.parent y j)
          (S'.origin j) (fun y hy => hvalid.2.2.2.1 y hy j)
        have hh' : (S'.count j:ℝ) = ∑ t ∈ S'.grains cube,
            (grainRecordCount S'.tuples cube S'.grain (fun y => S'.parent y j) t:ℝ) := by exact_mod_cast hh
        rw [hgrains] at hh'
        rw [hh']
        apply Finset.sum_congr rfl
        intro t ht
        exact congrArg Nat.cast (hrecords t ht j)
      have hh := band_average_bounds R
        (fun t => (grainRecordCount S.tuples cube S.grain (fun y => S.parent y j) t:ℝ)) hR
        (a:=(2:ℝ)^(band j.succ).val) (by
          intro t ht
          have hb := hbands t ht j.succ
          simp only [actualGrainQuantity,Fin.cases_succ,pow_succ] at hb
          exact ⟨hb.1,by nlinarith [hb.2]⟩) g hgR
      simpa only [← hsum,hgrains,show grainRecordCount S'.tuples cube S'.grain (fun y => S'.parent y j) g =
          grainRecordCount S.tuples cube S.grain (fun y => S.parent y j) g from hrecords g hgR j] using hh
  refine ⟨S',id,hvalid,hbalanced,hZ,hZS,rfl,rfl,fun _ _ => rfl,hmass,
    fun j => Finset.card_le_card (Finset.image_subset_image hZS),?_,fun _ _ _ => rfl,fun _ _ _ => rfl⟩
  intro G f g j
  apply Finset.card_le_card
  apply Finset.image_subset_image
  intro y hy
  exact Finset.mem_filter.mpr ⟨hZS (Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hy).2⟩

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.exists_balanced_state
