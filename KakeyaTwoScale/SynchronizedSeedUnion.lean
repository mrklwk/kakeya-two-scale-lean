module
public import KakeyaTwoScale.FrozenStateBalance
public import KakeyaTwoScale.WeightedLabelSelection

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace FrozenGeometryState
attribute [local instance] Classical.propDecidable

/-- The origin tag is part of the actual physical record, so records from
separate incoming varieties cannot accidentally be identified. -/
def synchronizedUnion {n k : ℕ} {T C O I : Type} [Fintype I]
    (S : I → FrozenGeometryState n k T C O) (owner : C → I) (cube : T → C)
    (height : Fin k → ℕ) (radius : ℝ) : FrozenGeometryState n k T C O := by
  classical
  exact {
    Piece := Σ i, (S i).Piece
    Grain := Σ i, (S i).Grain
    tuples := Finset.univ.biUnion (fun i => (S i).tuples)
    parent := fun y j => ⟨owner (cube y), (S (owner (cube y))).parent y j⟩
    grain := fun q => ⟨owner q, (S (owner q)).grain q⟩
    origin := fun j t => ⟨t.1, (S t.1).origin j t.2⟩
    original := fun j t => (S t.1).original j t.2
    base := fun j t => (S t.1).base j t.2
    axis := fun j t => (S t.1).axis j t.2
    height := height
    ballCenter := fun g => (S g.1).ballCenter g.2
    ballRadius := radius }

variable {n k : ℕ} {T C O I : Type} [Fintype I]

 theorem synchronizedUnion_mem (S : I → FrozenGeometryState n k T C O)
    (owner : C → I) (cube : T → C) (height : Fin k → ℕ) (radius : ℝ)
    (howner : ∀ i y, y ∈ (S i).tuples → owner (cube y)=i) (y : T) :
    y ∈ (synchronizedUnion S owner cube height radius).tuples ↔
      y ∈ (S (owner (cube y))).tuples := by
  classical
  change y ∈ Finset.univ.biUnion (fun i => (S i).tuples) ↔ _
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i,hy⟩
    simpa only [howner i y hy] using hy
  · exact fun hy => ⟨_,hy⟩

 theorem synchronizedUnion_geometry (S : I → FrozenGeometryState n k T C O)
    (owner : C → I) (cube : T → C) (height : Fin k → ℕ) (radius δ : ℝ)
    (hheight : ∀ i, (S i).height=height) (j : Fin k) (t : (synchronizedUnion S owner cube height radius).Piece) :
    (synchronizedUnion S owner cube height radius).geometry δ j t =
      (S t.1).geometry δ j t.2 := by
  change flatCylinder _ _ (δ*2^(height j)) δ = flatCylinder _ _ (δ*2^((S t.1).height j)) δ
  rw [hheight]
  rfl

/-- Cross-variety disjointness is proved from actual incoming disjoint tubes
and local containment; it is not imposed on the newly assembled union. -/
theorem synchronizedUnion_valid (S : I → FrozenGeometryState n k T C O)
    (owner : C → I) (cube : T → C) (height : Fin k → ℕ) (radius δ : ℝ)
    (Y : Finset T) (tube : T → Fin k → O) (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (U : FrozenGeometryState n k T C O)
    (hU : U.Valid Y cube tube Q δ)
    (old : I → U.Grain) (hold : Function.Injective old)
    (hv : ∀ i, (S i).Valid Y cube tube Q δ)
    (howner : ∀ i y, y ∈ (S i).tuples → owner (cube y)=i)
    (hsub : ∀ i, (S i).tuples ⊆ U.tuples)
    (hgrain : ∀ i y, y ∈ (S i).tuples → U.grain (cube y)=old i)
    (hgeom : ∀ i y, y ∈ (S i).tuples → ∀ j,
      (S i).geometry δ j ((S i).parent y j) ⊆ U.geometry δ j (U.parent y j))
    (hheight : ∀ i, (S i).height=height)
    (hradius : ∀ i, (S i).ballRadius ≤ radius) :
    (synchronizedUnion S owner cube height radius).Valid Y cube tube Q δ := by
  classical
  let V := synchronizedUnion S owner cube height radius
  have hm (y : T) (hy : y ∈ V.tuples) : y ∈ (S (owner (cube y))).tuples :=
    (synchronizedUnion_mem S owner cube height radius howner y).mp hy
  have hg (j) (t : V.Piece) : V.geometry δ j t=(S t.1).geometry δ j t.2 :=
    synchronizedUnion_geometry S owner cube height radius δ hheight j t
  refine ⟨fun y hy => (hv _).1 (hm y hy), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j t => (hv t.1).2.1 j t.2
  · exact fun y hy j => (hv _).2.2.1 y (hm y hy) j
  · intro y hy j
    exact congrArg (fun g : (S (owner (cube y))).Grain => (⟨owner (cube y),g⟩ : Σ i, (S i).Grain)) ((hv _).2.2.2.1 y (hm y hy) j)
  · intro y hy j
    rw [hg]
    exact (hv _).2.2.2.2.1 y (hm y hy) j
  · intro j o a ha b hb hab
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ha.1
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb.1
    have hy' := hm y hy
    have hz' := hm z hz
    change Disjoint (V.geometry δ j (V.parent y j)) (V.geometry δ j (V.parent z j))
    rw [hg,hg]
    by_cases he : owner (cube y)=owner (cube z)
    · have hz'' : z ∈ (S (owner (cube y))).tuples := by simpa only [← he] using hz'
      have hab' : (S (owner (cube y))).parent y j ≠ (S (owner (cube y))).parent z j := by
        intro h
        apply hab
        change Sigma.mk _ _ = Sigma.mk _ _
        exact (congrArg (Sigma.mk (owner (cube y))) h).trans
          (congrArg (fun i => (⟨i,(S i).parent z j⟩ : Σ i, (S i).Piece)) he)
      have ha' : (S (owner (cube y))).original j ((S (owner (cube y))).parent y j)=o := ha.2
      have hb' : (S (owner (cube y))).original j ((S (owner (cube y))).parent z j)=o := by
        have hbb : (S (owner (cube z))).original j ((S (owner (cube z))).parent z j)=o := hb.2
        rw [he]
        exact hbb
      have hh := (hv (owner (cube y))).2.2.2.2.2.1 j o
        ⟨Finset.mem_image.mpr ⟨y,hy',rfl⟩,ha'⟩ ⟨Finset.mem_image.mpr ⟨z,hz'',rfl⟩,hb'⟩ hab'
      change Disjoint ((S (owner (cube y))).geometry δ j ((S (owner (cube y))).parent y j))
        ((S (owner (cube z))).geometry δ j ((S (owner (cube z))).parent z j))
      rw [← he]
      exact hh
    · have hparents : U.parent y j ≠ U.parent z j := by
        intro h
        apply he
        apply hold
        rw [← hgrain _ y hy',← hgrain _ z hz']
        rw [← hU.2.2.2.1 y (hsub _ hy') j,← hU.2.2.2.1 z (hsub _ hz') j,h]
      have hoY : U.original j (U.parent y j)=o := by
        rw [hU.2.2.1 y (hsub _ hy') j,← (hv _).2.2.1 y hy' j]
        exact ha.2
      have hoZ : U.original j (U.parent z j)=o := by
        rw [hU.2.2.1 z (hsub _ hz') j,← (hv _).2.2.1 z hz' j]
        exact hb.2
      exact (hU.2.2.2.2.2.1 j o
        ⟨Finset.mem_image.mpr ⟨y,hsub _ hy',rfl⟩,hoY⟩
        ⟨Finset.mem_image.mpr ⟨z,hsub _ hz',rfl⟩,hoZ⟩ hparents).mono
        (hgeom _ y hy' j) (hgeom _ z hz' j)
  · intro y hy
    obtain ⟨hQ,hT⟩ := (hv _).2.2.2.2.2.2 y (hm y hy)
    refine ⟨hQ.trans (ball_subset_ball (hradius _)),?_⟩
    intro j
    rw [hg]
    exact (hT j).trans (ball_subset_ball (hradius _))

/-- Every cube fiber belongs to one incoming variety, so the nonlinear
mass of the tagged union is exactly additive, without a concavity loss. -/
theorem synchronizedUnion_mass [DecidableEq T] [DecidableEq C]
    (S : I → FrozenGeometryState n k T C O) (owner : C → I) (cube : T → C)
    (height : Fin k → ℕ) (radius : ℝ) (cubes : Finset C) {p : ℝ} (hp : 0 < p)
    (howner : ∀ i y, y ∈ (S i).tuples → owner (cube y)=i) :
    tupleCubeMass (synchronizedUnion S owner cube height radius).tuples cube cubes p =
      ∑ i, tupleCubeMass (S i).tuples cube cubes p := by
  classical
  let V := synchronizedUnion S owner cube height radius
  have hf (i : I) : V.tuples.filter (fun y => owner (cube y)=i)=(S i).tuples := by
    ext y
    rw [Finset.mem_filter,synchronizedUnion_mem S owner cube height radius howner]
    constructor
    · rintro ⟨hy,he⟩
      simpa only [he] using hy
    · intro hy
      exact ⟨by simpa only [howner i y hy] using hy,howner i y hy⟩
  have hh := grain_subset_mass V.tuples cube cubes owner Finset.univ hp
  simpa only [Finset.mem_univ,Finset.filter_true,hf] using hh

 theorem synchronizedUnion_count (S : I → FrozenGeometryState n k T C O)
    (owner : C → I) (cube : T → C) (height : Fin k → ℕ) (radius : ℝ)
    (howner : ∀ i y, y ∈ (S i).tuples → owner (cube y)=i) (j : Fin k) :
    (synchronizedUnion S owner cube height radius).count j ≤ ∑ i, (S i).count j := by
  classical
  let V := synchronizedUnion S owner cube height radius
  have hs : V.records j ⊆ Finset.univ.biUnion (fun i => ((S i).records j).image (Sigma.mk i)) := by
    intro t ht
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
    have hy' := (synchronizedUnion_mem S owner cube height radius howner y).mp hy
    exact Finset.mem_biUnion.mpr ⟨owner (cube y),Finset.mem_univ _,
      Finset.mem_image.mpr ⟨_,Finset.mem_image.mpr ⟨y,hy',rfl⟩,rfl⟩⟩
  apply (Finset.card_le_card hs).trans
  apply (Finset.card_biUnion_le).trans
  apply Finset.sum_le_sum
  intro i _
  exact Finset.card_image_le

/-- One finite bin synchronizes both the actual cellular stopping depth and
all family heights. It selects whole local seeds, preserving their physical
records and paying only the displayed number of possible bins. -/
theorem exists_synchronized_seed_bin {depth Lh : ℕ} [Nonempty I]
    (S : I → FrozenGeometryState n k T C O) (d : I → ℕ)
    (hd : ∀ i, d i ≤ depth) (hh : ∀ i j, (S i).height j ≤ Lh)
    (w : I → ℝ) (hw : ∀ i, 0 < w i) :
    ∃ (v : Fin (depth+1) × (Fin k → Fin (Lh+1))) (J : Finset I),
      J.Nonempty ∧
      (∀ i, i ∈ J ↔ d i=v.1.val ∧ ∀ j, (S i).height j=(v.2 j).val) ∧
      (∑ i, w i) / (((depth+1)*(Lh+1)^k : ℕ):ℝ) ≤ ∑ i ∈ J, w i := by
  classical
  let bin : I → Fin (depth+1) × (Fin k → Fin (Lh+1)) :=
    fun i => (⟨d i,Nat.lt_succ_of_le (hd i)⟩,fun j => ⟨(S i).height j,Nat.lt_succ_of_le (hh i j)⟩)
  obtain ⟨v,hv⟩ := exists_heaviest_weighted_label Finset.univ bin w
  let J := Finset.univ.filter (fun i => bin i=v)
  have hcard : Fintype.card (Fin (depth+1) × (Fin k → Fin (Lh+1))) = (depth+1)*(Lh+1)^k := by simp
  rw [hcard] at hv
  have hmass : (∑ i, w i) / (((depth+1)*(Lh+1)^k : ℕ):ℝ) ≤ ∑ i ∈ J, w i := by
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hv
  have hne : J.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he,Finset.sum_empty] at hmass
    have hp : 0 < ∑ i, w i := Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
    exact (not_lt_of_ge hmass) (div_pos hp (by positivity))
  refine ⟨v,J,hne,?_,hmass⟩
  intro i
  simp only [J,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h
    exact ⟨congrArg (fun z => z.1.val) h,fun j => congrArg (fun z => (z.2 j).val) h⟩
  · rintro ⟨hd,hh⟩
    apply Prod.ext
    · exact Fin.ext hd
    · exact funext (fun j => Fin.ext (hh j))

/-- Restrict a global cube owner to the selected nonempty bin. The arbitrary
fallback is used only on cubes absent from every selected local seed. -/
def selectedSeedOwner [DecidableEq I] (J : Finset I) (hJ : J.Nonempty)
    (owner : C → I) (q : C) : {i // i ∈ J} :=
  if h : owner q ∈ J then ⟨owner q,h⟩ else ⟨hJ.choose,hJ.choose_spec⟩

omit [Fintype I] in
theorem selectedSeedOwner_eq [DecidableEq I] (J : Finset I) (hJ : J.Nonempty)
    (owner : C → I) (q : C) (i : {i // i ∈ J}) (h : owner q=i.val) :
    selectedSeedOwner J hJ owner q=i := by
  apply Subtype.ext
  simp only [selectedSeedOwner]
  rw [dite_eq_left (h ▸ i.property)]
  exact h

omit [Fintype I] in
theorem selectedSeedOwner_local [DecidableEq I]
    (S : I → FrozenGeometryState n k T C O) (owner : C → I) (cube : T → C)
    (howner : ∀ i y, y ∈ (S i).tuples → owner (cube y)=i)
    (J : Finset I) (hJ : J.Nonempty) :
    ∀ (i : {i // i ∈ J}) y, y ∈ (S i).tuples → selectedSeedOwner J hJ owner (cube y)=i := by
  intro i y hy
  exact selectedSeedOwner_eq J hJ owner (cube y) i (howner i y hy)

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.synchronizedUnion_valid

#print axioms KakeyaTwoScale.FrozenGeometryState.synchronizedUnion_mass
#print axioms KakeyaTwoScale.FrozenGeometryState.synchronizedUnion_count
#print axioms KakeyaTwoScale.FrozenGeometryState.exists_synchronized_seed_bin
#print axioms KakeyaTwoScale.FrozenGeometryState.selectedSeedOwner_local
