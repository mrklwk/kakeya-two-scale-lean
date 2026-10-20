module
public import KakeyaTwoScale.FrozenGeometryState

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
namespace KakeyaTwoScale
namespace FrozenGeometryState

/-- Construct an actual all-family geometric successor at any smaller dyadic
height vector. Every original tuple, parent, tube ID and incidence is tracked.
There is no assumed transition or retained-mass oracle. -/
theorem exists_geometric_cut {n k A : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    (S : FrozenGeometryState n k T C O) (Y₀ : Finset T) (cube : T → C)
    (tube : T → Fin k → O) (Q : C → Set (EuclideanSpace ℝ (Fin n)))
    (cubes : Finset C) (center : C → EuclideanSpace ℝ (Fin n))
    {δ r p : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hδr : δ ≤ r)
    (hp : 0 < p) (hp1 : p ≤ 1) (hv : S.Valid Y₀ cube tube Q δ)
    (hne : S.tuples.Nonempty) (hcubes : ∀ y ∈ S.tuples, cube y ∈ cubes)
    (H : Fin k → ℕ) (hH : ∀ j, H j ≤ S.height j)
    (hHr : ∀ j, δ*2^(H j) ≤ 2*r)
    (hQ : ∀ q ∈ cubes, ∀ x ∈ Q q, dist x (center q) ≤ (A:ℝ)*r) :
    ∃ (S' : FrozenGeometryState n k T C O) (lift : S'.Grain → S.Grain),
      S'.Valid Y₀ cube tube Q δ ∧ S'.tuples ⊆ S.tuples ∧ S'.height=H ∧ S'.ballRadius=(A+n+5:ℝ)*r ∧
      (∀ y ∈ S'.tuples, lift (S'.grain (cube y))=S.grain (cube y)) ∧
      tupleCubeMass S.tuples cube cubes p / ((3^k*(2*(A+n+5)+1)^n:ℕ):ℝ) ≤
        tupleCubeMass S'.tuples cube cubes p ∧
      (∀ j, (S'.count j:ℝ) ≤ (S.length δ j/(δ*2^(H j)))*(S.count j:ℝ)) ∧
      (∀ g j, (grainRecordCount S'.tuples cube (lift ∘ S'.grain) (fun y => S'.parent y j) g:ℝ) ≤
        (S.length δ j/(δ*2^(H j)))*(grainRecordCount S.tuples cube S.grain (fun y => S.parent y j) g:ℝ)) ∧
      (∀ y ∈ S'.tuples, ∀ j, S'.geometry δ j (S'.parent y j) ⊆ S.geometry δ j (S.parent y j)) ∧
      (∀ y ∈ S'.tuples, ∀ j, S'.axis j (S'.parent y j)=S.axis j (S.parent y j)) := by
  classical
  let ell (j : Fin k) : ℝ := δ*2^(H j)
  have hell (j : Fin k) : 0 < ell j := by dsimp [ell]; positivity
  have hlen (j : Fin k) : ell j ≤ S.length δ j := by
    dsimp [ell,length]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (hH j)) hδ.le
  obtain ⟨color,start,Z,hZS,hmass,hchild,hdisj,hlocal,_hcounts⟩ := family_shared_cap_localization
    S.tuples cube cubes Q center S.parent S.origin S.grain S.base S.axis
    (fun j _ => S.length δ j) (S.length δ) ell δ r p hδ hell
    (fun j _ _ => hlen j) (fun _ _ _ => le_rfl) hr hδr hHr hQ hcubes hv.2.1 hv.2.2.2.1 hv.2.2.2.2.1 hp hp1
  let c (q : C) := gridIndex r (WithLp.ofLp (center q))
  let child (y : T) (j : Fin k) := (S.parent y j,start y j)
  obtain ⟨y₀,hy₀⟩ := hne
  have hlabels : ∀ j, ∃ label : S.Piece×ℝ → S.Grain×(Fin n → ℤ),
      ∀ y ∈ Z, label (child y j)=(S.grain (cube y),c (cube y)) := by
    intro j
    apply exists_record_label Z (fun y => child y j) (fun y => (S.grain (cube y),c (cube y)))
      (S.grain (cube y₀),0)
    have hh := localized_piece_label_consistent Z (fun y => child y j) (fun s => S.origin j s.1)
      (fun y => c (cube y))
      (fun s => flatCylinder (S.base j s.1+s.2 • S.axis j s.1) (S.axis j s.1) (ell j) δ)
      (fun z => ball (latticeCenter r z) ((A+n+5:ℝ)*r)) hdisj
      (fun y hy => (hchild y hy j).2.1.mono (fun _ hx => hx.2))
      (fun y hy => (hlocal y hy).2 j)
    intro y hy z hz he
    have he' := hh y hy z hz he
    simpa only [child,hv.2.2.2.1 y (hZS hy) j,hv.2.2.2.1 z (hZS hz) j] using he'
  choose labels hlabels using hlabels
  let S' : FrozenGeometryState n k T C O := {
    Piece := S.Piece×ℝ
    Grain := S.Grain×(Fin n → ℤ)
    tuples := Z
    parent := child
    grain := fun q => (S.grain q,c q)
    origin := labels
    original := fun j t => S.original j t.1
    base := fun j t => S.base j t.1+t.2 • S.axis j t.1
    axis := fun j t => S.axis j t.1
    height := H
    ballCenter := fun g => latticeCenter r g.2
    ballRadius := (A+n+5:ℝ)*r }
  have hvalid : S'.Valid Y₀ cube tube Q δ := by
    refine ⟨hZS.trans hv.1,?_,?_,?_,?_,?_,?_⟩
    · intro j t
      exact hv.2.1 j t.1
    · intro y hy j
      exact hv.2.2.1 y (hZS hy) j
    · intro y hy j
      exact hlabels j y hy
    · intro y hy j
      exact (hchild y hy j).2.1
    · intro j o
      have hh := shared_children_disjoint {t | t ∈ S.records j ∧ S.original j t=o}
        (S.base j) (S.axis j) (fun _ => S.length δ j) (hell j)
        (fun t _ => hv.2.1 j t) (fun _ _ => hlen j) (color j) (hv.2.2.2.2.2.1 j o)
      intro s hs t ht hst
      apply hh ?_ ?_ hst
      · have hs' : s ∈ Z.image (fun y => child y j) := by simpa [records,S'] using hs.1
        obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hs'
        subst s
        exact ⟨⟨Finset.mem_image_of_mem _ (hZS hy),hs.2⟩,(hchild y hy j).1⟩
      · have ht' : t ∈ Z.image (fun y => child y j) := by simpa [records,S'] using ht.1
        obtain ⟨y,hy,he⟩ := Finset.mem_image.mp ht'
        subst t
        exact ⟨⟨Finset.mem_image_of_mem _ (hZS hy),ht.2⟩,(hchild y hy j).1⟩
    · exact hlocal
  refine ⟨S',Prod.fst,hvalid,hZS,rfl,rfl,fun _ _ => rfl,hmass,?_,?_,?_,fun _ _ _ => rfl⟩
  · intro j
    have hc := variable_child_record_bound S.tuples Z (fun y => S.parent y j) (fun y => start y j)
      (fun _ => cappedStarts (S.length δ j) (ell j) (color j)) hZS
      (fun y hy => (hchild y hy j).1) (X:=S.length δ j/ell j) (by
        intro t ht
        have hh := cappedStarts_length_budget (hell j) (hlen j) (color j)
        exact (le_div_iff₀ (hell j)).mpr (by nlinarith))
    have he : Z.image (fun y => (S.parent y j,start y j)) = S'.records j := by
      ext t
      simp [records,S',child]
    rw [he] at hc
    exact hc
  · intro g j
    have hc := variable_child_record_bound
      (S.tuples.filter fun y => S.grain (cube y)=g) (Z.filter fun y => S.grain (cube y)=g)
      (fun y => S.parent y j) (fun y => start y j)
      (fun _ => cappedStarts (S.length δ j) (ell j) (color j))
      (by intro y hy; exact Finset.mem_filter.mpr ⟨hZS (Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hy).2⟩)
      (fun y hy => (hchild y (Finset.mem_filter.mp hy).1 j).1) (X:=S.length δ j/ell j) (by
        intro t ht
        have hh := cappedStarts_length_budget (hell j) (hlen j) (color j)
        exact (le_div_iff₀ (hell j)).mpr (by nlinarith))
    convert hc using 1
    · congr 2
    · rfl
  · intro y hy j
    exact (hchild y hy j).2.2

end FrozenGeometryState
end KakeyaTwoScale
#print axioms KakeyaTwoScale.FrozenGeometryState.exists_geometric_cut
