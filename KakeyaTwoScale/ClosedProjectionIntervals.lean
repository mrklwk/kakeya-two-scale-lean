module
public import KakeyaTwoScale.SeparatedProjectionCount
public import Mathlib.Topology.Order.Compact

@[expose] public section

open Set Metric MvPolynomial
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

def realSetComponents (S : Set ℝ) : Set (Set ℝ) :=
  {C | ∃ x ∈ S, connectedComponentIn S x=C}

theorem different_real_components_separator (S : Set ℝ) {x y : ℝ}
    (hx : x ∈ S) (hy : y ∈ S)
    (hne : connectedComponentIn S x ≠ connectedComponentIn S y) :
    ∃ r : ℝ, ((x<r ∧ r<y) ∨ (y<r ∧ r<x)) ∧ r ∉ S := by
  have step : ∀ {a b : ℝ}, a ∈ S → b ∈ S →
      connectedComponentIn S a ≠ connectedComponentIn S b → a<b →
      ∃ r ∈ Ioo a b, r ∉ S := by
    intro a b ha hb hne hab
    by_contra! hh
    have hsub : Icc a b ⊆ S := by
      intro r hr
      by_cases hra : r=a
      · simpa [hra] using ha
      by_cases hrb : r=b
      · simpa [hrb] using hb
      exact hh r ⟨lt_of_le_of_ne hr.1 (fun he => hra he.symm),lt_of_le_of_ne hr.2 hrb⟩
    have hbC := isPreconnected_Icc.subset_connectedComponentIn
      (show a ∈ Icc a b from ⟨le_rfl,hab.le⟩) hsub
      (show b ∈ Icc a b from ⟨hab.le,le_rfl⟩)
    exact hne (connectedComponentIn_eq hbC)
  by_cases hxy : x<y
  · obtain ⟨r,hr,hout⟩ := step hx hy hne hxy
    exact ⟨r,Or.inl hr,hout⟩
  · have hyx : y<x := lt_of_le_of_ne (le_of_not_gt hxy)
      (fun he => hne (by rw [he]))
    obtain ⟨r,hr,hout⟩ := step hy hx hne.symm hyx
    exact ⟨r,Or.inr hr,hout⟩

/-- No quantifier elimination: a closed coordinate projection of a
nonnegative polynomial zero set has a bounded closed-interval cover after
clipping. The separator polynomial and actual component finiteness are proved. -/
theorem exists_closed_algebraic_projection_intervals {n D : ℕ}
    (G : MvPolynomial (Fin n) ℝ) (coordinate : Fin n) (S : Set ℝ)
    (hS : IsClosed S) (hprojection : ∀ t, t ∈ S ↔ ∃ z : EuclideanSpace ℝ (Fin n),
      z coordinate=t ∧ eval (fun i => z i) G=0)
    (hdegree : G.totalDegree ≤ D)
    (hnonneg : ∀ z : EuclideanSpace ℝ (Fin n), 0 ≤ eval (fun i => z i) G)
    {L : ℝ} (_hL : 0 < L) :
    ∃ C : Finset (ℝ × ℝ), C.card ≤ (2*(max D 2)+1)^n ∧
      (∀ a ∈ C, 0 ≤ a.1 ∧ a.1 ≤ a.2 ∧ a.2 ≤ L) ∧
      ∀ t : ℝ, (t ∈ Icc (0:ℝ) L ∧ t ∈ S) ↔ ∃ a ∈ C, t ∈ Icc a.1 a.2 := by
  classical
  let T := Icc (0:ℝ) L ∩ S
  have hTc : IsCompact T := isCompact_Icc.inter_right hS
  have hbound : ∀ A : Finset (Set ℝ), (A : Set (Set ℝ)) ⊆ realSetComponents T →
      A.card ≤ (2*(max D 2)+1)^n := by
    intro A hA
    have hreps : ∀ C : A, ∃ t ∈ T, connectedComponentIn T t=C.val := fun C => hA C.property
    choose t ht hcomp using hreps
    have hw : ∀ C : A, ∃ z : EuclideanSpace ℝ (Fin n),
        z coordinate=t C ∧ eval (fun i => z i) G=0 := fun C =>
      (hprojection _).mp (ht C).2
    choose z hzcoord hzero using hw
    have hh := algebraic_projection_separated_count G coordinate z hdegree hnonneg hzero
      (by
        intro C E hne
        have hce : connectedComponentIn T (t C) ≠ connectedComponentIn T (t E) := by
          rw [hcomp,hcomp]
          exact fun he => hne (Subtype.ext he)
        obtain ⟨r,hr,hout⟩ := different_real_components_separator T (ht C) (ht E) hce
        have hrI : r ∈ Icc (0:ℝ) L := by
          rcases hr with hr | hr
          · exact ⟨(ht C).1.1.trans hr.1.le,hr.2.le.trans (ht E).1.2⟩
          · exact ⟨(ht E).1.1.trans hr.1.le,hr.2.le.trans (ht C).1.2⟩
        refine ⟨r,by simpa only [hzcoord] using hr,?_⟩
        intro w hwr hzero
        exact hout ⟨hrI,(hprojection r).mpr ⟨w,hwr,hzero⟩⟩)
    simpa using hh
  obtain ⟨hfinite,hcard⟩ := finite_ncard_le_of_finset_bound (realSetComponents T)
    ((2*(max D 2)+1)^n) hbound
  have hcomponent : ∀ C ∈ realSetComponents T,
      C.Nonempty ∧ IsCompact C ∧ C=Icc (sInf C) (sSup C) ∧ C ⊆ T := by
    intro C hC
    obtain ⟨x,hx,rfl⟩ := hC
    have hne : (connectedComponentIn T x).Nonempty := ⟨x,mem_connectedComponentIn hx⟩
    have hc : IsCompact (connectedComponentIn T x) := by
      rw [connectedComponentIn_eq_image hx]
      let : CompactSpace T := isCompact_iff_compactSpace.mp hTc
      exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
    exact ⟨hne,hc,eq_Icc_of_connected_compact
      ⟨hne,isPreconnected_connectedComponentIn⟩ hc,connectedComponentIn_subset T x⟩
  let C := hfinite.toFinset.image (fun A => (sInf A,sSup A))
  refine ⟨C,?_,?_,?_⟩
  · exact Finset.card_image_le.trans (by simpa only [Set.ncard_eq_toFinset_card (realSetComponents T) hfinite] using hcard)
  · intro a ha
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp ha
    have hA' := hfinite.mem_toFinset.mp hA
    obtain ⟨hne,hcompact,he,hsub⟩ := hcomponent A hA'
    have hlo := hcompact.isClosed.csInf_mem hne hcompact.bddBelow
    have hhi := hcompact.isClosed.csSup_mem hne hcompact.bddAbove
    exact ⟨(hsub hlo).1.1,csInf_le hcompact.bddBelow hhi,(hsub hhi).1.2⟩
  · intro t
    constructor
    · intro ht
      let A := connectedComponentIn T t
      have hA : A ∈ realSetComponents T := ⟨t,ht,rfl⟩
      refine ⟨(sInf A,sSup A),Finset.mem_image.mpr
        ⟨A,hfinite.mem_toFinset.mpr hA,rfl⟩,?_⟩
      rw [← (hcomponent A hA).2.2.1]
      exact mem_connectedComponentIn ht
    · rintro ⟨a,ha,ht⟩
      obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp ha
      have hA' := hfinite.mem_toFinset.mp hA
      have hcomp := hcomponent A hA'
      exact hcomp.2.2.2 (hcomp.2.2.1 ▸ ht)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.different_real_components_separator
#print axioms KakeyaTwoScale.exists_closed_algebraic_projection_intervals
