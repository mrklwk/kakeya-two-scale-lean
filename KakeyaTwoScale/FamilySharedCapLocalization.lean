module
public import KakeyaTwoScale.FamilyPrescribedTransport
public import KakeyaTwoScale.VariableParentCounts

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- All-family shortening and localization on shared parent IDs. Actual child
records are (parent,start), not tuple occurrences. Both total and old-origin
counts are proved from the geometric construction. Actual parent lengths may
vary. The output children all have exactly the family-specific prescribed length ell j; the
count ratio uses the proved common upper bound Lmax j, never a substituted geometry. -/
theorem family_shared_cap_localization {n A k : ℕ} {T C P G : Type*}
    [DecidableEq T] [DecidableEq C] [DecidableEq P] [DecidableEq G]
    (Y : Finset T) (cube : T → C) (cubes : Finset C)
    (Q : C → Set (EuclideanSpace ℝ (Fin n))) (center : C → EuclideanSpace ℝ (Fin n))
    (parent : T → Fin k → P) (origin : Fin k → P → G) (grain : C → G)
    (b u : Fin k → P → EuclideanSpace ℝ (Fin n)) (L : Fin k → P → ℝ)
    (Lmax ell : Fin k → ℝ) (δ r p : ℝ)
    (_hδ : 0 < δ) (hℓ : ∀ j, 0 < ell j) (hL : ∀ j, ∀ t ∈ Y.image (fun y => parent y j), ell j ≤ L j t)
    (hLmax : ∀ j, ∀ t ∈ Y.image (fun y => parent y j), L j t ≤ Lmax j) (hr : 0 < r) (hδr : δ ≤ r) (hℓr : ∀ j, ell j ≤ 2*r)
    (hQ : ∀ q ∈ cubes, ∀ x ∈ Q q, dist x (center q) ≤ (A:ℝ)*r)
    (hY : ∀ y ∈ Y, cube y ∈ cubes) (hu : ∀ j t, ‖u j t‖=1)
    (horigin : ∀ y ∈ Y, ∀ j, origin j (parent y j)=grain (cube y))
    (hinc : ∀ y ∈ Y, ∀ j, (Q (cube y) ∩ flatCylinder (b j (parent y j)) (u j (parent y j)) (L j (parent y j)) δ).Nonempty)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ (color : Fin k → Fin 3) (start : T → Fin k → ℝ) (Z : Finset T), Z ⊆ Y ∧
      tupleCubeMass Y cube cubes p / ((3^k*(2*(A+n+5)+1)^n:ℕ):ℝ) ≤ tupleCubeMass Z cube cubes p ∧
      (∀ y ∈ Z, ∀ j, start y j ∈ cappedStarts (L j (parent y j)) (ell j) (color j) ∧
        (Q (cube y) ∩ flatCylinder (b j (parent y j)+start y j • u j (parent y j)) (u j (parent y j)) (ell j) δ).Nonempty ∧
        flatCylinder (b j (parent y j)+start y j • u j (parent y j)) (u j (parent y j)) (ell j) δ ⊆
          flatCylinder (b j (parent y j)) (u j (parent y j)) (L j (parent y j)) δ) ∧
      PairwiseDisjoint (↑(Z.image (fun y => gridIndex r (WithLp.ofLp (center (cube y))))) : Set (Fin n → ℤ))
        (fun z => ball (latticeCenter r z) ((A+n+5:ℝ)*r)) ∧
      (∀ y ∈ Z, Q (cube y) ⊆ ball (latticeCenter r (gridIndex r (WithLp.ofLp (center (cube y))))) ((A+n+5:ℝ)*r) ∧
        ∀ j, flatCylinder (b j (parent y j)+start y j • u j (parent y j)) (u j (parent y j)) (ell j) δ ⊆
          ball (latticeCenter r (gridIndex r (WithLp.ofLp (center (cube y))))) ((A+n+5:ℝ)*r)) ∧
      (∀ j, let records := Z.image (fun y => ((grain (cube y),gridIndex r (WithLp.ofLp (center (cube y)))),(parent y j,start y j)))
       (records.card:ℝ) ≤ (Lmax j/ell j)*((Y.image (fun y => parent y j)).card:ℝ) ∧
       ∀ g, ((records.filter fun s => s.1.1=g).card:ℝ) ≤
         (Lmax j/ell j)*(((Y.filter fun y => origin j (parent y j)=g).image (fun y => parent y j)).card:ℝ)) := by
  classical
  obtain ⟨color,W,hWY,hWmass,hW⟩ := family_prescribed_length_transport Y cube cubes Q
    (fun y j => b j (parent y j)) (fun y j => u j (parent y j)) (fun y j => L j (parent y j))
    ell hℓ hp hp1 (fun y hy j => hL j _ (Finset.mem_image_of_mem _ hy))
    (fun y _ j => hu j (parent y j)) hinc
  have hex : ∀ y, ∀ j, ∃ a : ℝ, y ∈ W → a ∈ cappedStarts (L j (parent y j)) (ell j) (color j) ∧
      (Q (cube y) ∩ flatCylinder (b j (parent y j)+a • u j (parent y j)) (u j (parent y j)) (ell j) δ).Nonempty ∧
      flatCylinder (b j (parent y j)+a • u j (parent y j)) (u j (parent y j)) (ell j) δ ⊆
        flatCylinder (b j (parent y j)) (u j (parent y j)) (L j (parent y j)) δ := by
    intro y j
    by_cases hy : y ∈ W
    · obtain ⟨a,ha,hi,hs⟩ := (hW y hy j).2.2
      exact ⟨a,fun _ => ⟨ha,hi,hs⟩⟩
    · exact ⟨0,fun h => False.elim (hy h)⟩
  choose start hstart using hex
  obtain ⟨_,Z,_,hZW,hZmass,hdisj,hloc,_⟩ := exists_spatial_tuple_localization W cube cubes Q center
    (fun y j => b j (parent y j)+start y j • u j (parent y j))
    (fun y j => u j (parent y j)) (fun _ j => ell j)
    hr hδr hQ (fun y hy => hY y (hWY hy)) (fun y _ j => hu j (parent y j))
    (fun _ _ j => hℓr j) (fun y hy j => (hstart y j hy).2.1) hp hp1
  have hZY : Z ⊆ Y := hZW.trans hWY
  refine ⟨color,start,Z,hZY,?_,fun y hy j => hstart y j (hZW hy),hdisj,hloc,?_⟩
  · have hh := (div_le_div_of_nonneg_right hWmass
      (show (0:ℝ) ≤ (((2*(A+n+5)+1)^n:ℕ):ℝ) by positivity)).trans hZmass
    simpa only [div_div,Nat.cast_mul] using hh
  · intro j
    let c (y : T) := gridIndex r (WithLp.ofLp (center (cube y)))
    let child (y : T) := (parent y j,start y j)
    let geom (s : P×ℝ) := flatCylinder (b j s.1+s.2 • u j s.1) (u j s.1) (ell j) δ
    let balls (z : Fin n → ℤ) := ball (latticeCenter r z) ((A+n+5:ℝ)*r)
    have he := localized_occurrence_counts Z child (fun s => origin j s.1) c geom balls hdisj
      (fun y hy => (hstart y j (hZW hy)).2.1.mono (fun _ hx => hx.2))
      (fun y hy => (hloc y hy).2 j)
    have hlabel : Z.image (fun y => ((grain (cube y),c y),child y)) =
        Z.image (fun y => ((origin j (parent y j),c y),child y)) := by
      apply Finset.image_congr
      intro y hy
      dsimp only
      rw [horigin y (hZY hy) j]
    change ((Z.image (fun y => ((grain (cube y),c y),child y))).card:ℝ) ≤ _ ∧ _
    rw [hlabel]
    have hmem : ∀ y ∈ Z, start y j ∈ cappedStarts (L j (parent y j)) (ell j) (color j) :=
      fun y hy => (hstart y j (hZW hy)).1
    have hcount' : ∀ t ∈ Y.image (fun y => parent y j),
        ((cappedStarts (L j t) (ell j) (color j)).card:ℝ) ≤ Lmax j/ell j := by
      intro t ht
      have hh := cappedStarts_length_budget (hℓ j) (hL j t ht) (color j)
      exact (le_div_iff₀ (hℓ j)).mpr (by nlinarith [hLmax j t ht])
    constructor
    · rw [he.1]
      exact variable_child_record_bound Y Z (fun y => parent y j) (fun y => start y j)
        (fun t => cappedStarts (L j t) (ell j) (color j)) hZY hmem hcount'
    · intro g
      rw [he.2 g]
      exact variable_child_origin_bound Y Z (fun y => parent y j) (origin j) (fun y => start y j)
        (fun t => cappedStarts (L j t) (ell j) (color j)) hZY hmem hcount' g

end KakeyaTwoScale
#print axioms KakeyaTwoScale.family_shared_cap_localization
