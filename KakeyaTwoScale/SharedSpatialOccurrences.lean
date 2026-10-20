module
public import KakeyaTwoScale.SpatialTupleLocalization
public import KakeyaTwoScale.UpperBudgetReset

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Registering a physical piece once in its unique label does not multiply
its cardinality by the number of tuple witnesses. -/
theorem consistent_labeled_image_card {T P G : Type*}
    [DecidableEq T] [DecidableEq P] [DecidableEq G]
    (Y : Finset T) (piece : T → P) (label : T → G)
    (hc : ∀ y ∈ Y, ∀ z ∈ Y, piece y=piece z → label y=label z) :
    (Y.image (fun y => (label y,piece y))).card = (Y.image piece).card := by
  classical
  let S := Y.image (fun y => (label y,piece y))
  have hi : Set.InjOn Prod.snd (↑S : Set (G×P)) := by
    intro a ha b hb he
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
    exact Prod.ext (hc y hy z hz he) he
  have hh := Finset.card_image_of_injOn hi
  simpa only [S,Finset.image_image,Function.comp_def] using hh.symm

/-- Geometric containment in disjoint selected-center balls constructs
consistent spatial labels for actual nonempty pieces. Old origins are kept. -/
theorem localized_piece_label_consistent {X T P G C : Type*} [DecidableEq T] [DecidableEq C]
    (Y : Finset T) (piece : T → P) (origin : P → G) (center : T → C)
    (geometry : P → Set X) (balls : C → Set X)
    (hd : PairwiseDisjoint (↑(Y.image center) : Set C) balls)
    (hne : ∀ y ∈ Y, (geometry (piece y)).Nonempty)
    (hfit : ∀ y ∈ Y, geometry (piece y) ⊆ balls (center y)) :
    ∀ y ∈ Y, ∀ z ∈ Y, piece y=piece z →
      (origin (piece y),center y)=(origin (piece z),center z) := by
  intro y hy z hz he
  apply Prod.ext (congrArg origin he)
  exact localized_piece_center_unique balls _ hd (Finset.mem_image_of_mem center hy)
    (Finset.mem_image_of_mem center hz) (hne y hy) (hfit y hy)
    (by simpa only [he] using hfit z hz)

/-- Exact total and old-origin counts for spatially registered occurrences. -/
theorem localized_occurrence_counts {X T P G C : Type*}
    [DecidableEq T] [DecidableEq P] [DecidableEq G] [DecidableEq C]
    (Y : Finset T) (piece : T → P) (origin : P → G) (center : T → C)
    (geometry : P → Set X) (balls : C → Set X)
    (hd : PairwiseDisjoint (↑(Y.image center) : Set C) balls)
    (hne : ∀ y ∈ Y, (geometry (piece y)).Nonempty)
    (hfit : ∀ y ∈ Y, geometry (piece y) ⊆ balls (center y)) :
    let S := Y.image (fun y => ((origin (piece y),center y),piece y))
    S.card = (Y.image piece).card ∧ ∀ g,
      (S.filter fun s => s.1.1=g).card = ((Y.filter fun y => origin (piece y)=g).image piece).card := by
  classical
  dsimp only
  have hc := localized_piece_label_consistent Y piece origin center geometry balls hd hne hfit
  refine ⟨consistent_labeled_image_card Y piece _ hc,?_⟩
  intro g
  have he : (Y.image (fun y => ((origin (piece y),center y),piece y))).filter (fun s => s.1.1=g) =
      (Y.filter fun y => origin (piece y)=g).image (fun y => ((origin (piece y),center y),piece y)) := by
    ext s
    simp only [Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨y,hy,rfl⟩,hg⟩
      exact ⟨y,⟨hy,hg⟩,rfl⟩
    · rintro ⟨y,⟨hy,hg⟩,rfl⟩
      exact ⟨⟨y,hy,rfl⟩,hg⟩
  rw [he]
  exact consistent_labeled_image_card _ piece _
    (fun y hy z hz => hc y (Finset.mem_filter.mp hy).1 z (Finset.mem_filter.mp hz).1)

/-- Deduplicated selected child records fit in the literal product of their
old parent IDs and one common finite start family. -/
theorem child_record_card_bound {T P A : Type*}
    [DecidableEq T] [DecidableEq P] [DecidableEq A]
    (Y Z : Finset T) (parent : T → P) (start : T → A) (starts : Finset A)
    (hZY : Z ⊆ Y) (hstart : ∀ y ∈ Z, start y ∈ starts) :
    (Z.image (fun y => (parent y,start y))).card ≤ (Y.image parent).card*starts.card := by
  have hs : Z.image (fun y => (parent y,start y)) ⊆ (Y.image parent).product starts := by
    intro a ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem parent (hZY hy),hstart y hy⟩
  exact (Finset.card_le_card hs).trans_eq (Finset.card_product _ _)

/-- The same actual child count bound holds separately over each old origin. -/
theorem child_record_origin_bound {T P A G : Type*}
    [DecidableEq T] [DecidableEq P] [DecidableEq A] [DecidableEq G]
    (Y Z : Finset T) (parent : T → P) (origin : P → G) (start : T → A) (starts : Finset A)
    (hZY : Z ⊆ Y) (hstart : ∀ y ∈ Z, start y ∈ starts) (g : G) :
    ((Z.filter fun y => origin (parent y)=g).image (fun y => (parent y,start y))).card ≤
      ((Y.filter fun y => origin (parent y)=g).image parent).card*starts.card := by
  exact child_record_card_bound _ _ parent start starts
    (fun y hy => Finset.mem_filter.mpr ⟨hZY (Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hy).2⟩)
    (fun y hy => hstart y (Finset.mem_filter.mp hy).1)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.consistent_labeled_image_card
#print axioms KakeyaTwoScale.localized_piece_label_consistent
#print axioms KakeyaTwoScale.localized_occurrence_counts
#print axioms KakeyaTwoScale.child_record_card_bound
#print axioms KakeyaTwoScale.child_record_origin_bound
