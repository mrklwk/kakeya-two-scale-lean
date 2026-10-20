module
public import KakeyaTwoScale.FiniteRootIntervals
public import KakeyaTwoScale.LocalizedAncestorCylinder
public import KakeyaTwoScale.AmbientPolynomialWall

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

def cellularRoots {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (b u : EuclideanSpace ℝ (Fin n)) (L : ℝ) : Finset ℝ :=
  (affineLineRestriction P b u).roots.toFinset.filter (fun r => 0 < r ∧ r < L)

theorem cellularRoots_bounds {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (b u : EuclideanSpace ℝ (Fin n)) (L : ℝ) :
    ∀ r ∈ cellularRoots P b u L, r ∈ Ioo (0:ℝ) L := by
  intro r hr
  exact (Finset.mem_filter.mp hr).2

theorem cellular_gap_count {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (b u : EuclideanSpace ℝ (Fin n)) (L : ℝ) :
    (insert 0 (cellularRoots P b u L)).card ≤ P.totalDegree+1 := by
  have hr : (cellularRoots P b u L).card ≤ (affineLineRestriction P b u).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro r hr
    exact Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1
  exact (Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right (hr.trans (affineLineRestriction_natDegree_le P b u)) 1)

/-- A perpendicular-axis representation is unique, so disjoint axial
intervals give disjoint full-width cylinders even when they spill across cells. -/
theorem cylinder_parameter_unique {n : ℕ} (b u x : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖=1) {t s : ℝ}
    (ht : inner ℝ u (x-(b+t • u))=0) (hs : inner ℝ u (x-(b+s • u))=0) : t=s := by
  simp only [inner_sub_right,inner_add_right,inner_smul_right,
    real_inner_self_eq_norm_sq,hu,one_pow,mul_one] at ht hs
  linarith

theorem cellular_cylinders_disjoint {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (b u : EuclideanSpace ℝ (Fin n)) (L δ : ℝ) (hu : ‖u‖=1) :
    PairwiseDisjoint (↑(insert 0 (cellularRoots P b u L)) : Set ℝ)
      (fun a => flatCylinder (b+a • u) u (rootNext (cellularRoots P b u L) L a-a) δ) := by
  intro a ha c hc hne
  have hd := root_intervals_disjoint (cellularRoots P b u L) L
    (fun r hr => (cellularRoots_bounds P b u L r hr).1) ha hc hne
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨t,ht0,htL,hti,_⟩ := hx
  obtain ⟨s,hs0,hsL,hsi,_⟩ := hy
  have ht : inner ℝ u (x-(b+(a+t) • u))=0 := by
    simpa only [show b+(a+t) • u=(b+a • u)+t • u by module] using hti
  have hs : inner ℝ u (x-(b+(c+s) • u))=0 := by
    simpa only [show b+(c+s) • u=(b+c • u)+s • u by module] using hsi
  have he := cylinder_parameter_unique b u x hu ht hs
  apply Set.disjoint_left.mp hd (show a+t ∈ Ioo a (rootNext (cellularRoots P b u L) L a) by
    constructor <;> linarith)
  rw [he]
  constructor <;> linarith

/-- An actual off-wall incidence selects its whole maximal root gap, not
an arbitrarily shortened delta-piece. The gap has length at least delta. -/
theorem exists_cellular_root_piece {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (b u x : EuclideanSpace ℝ (Fin n)) (L δ : ℝ)
    (hu : ‖u‖=1) (hδ : 0 < δ) (hL : δ ≤ L)
    (hx : x ∈ flatCylinder b u L δ)
    (hwall : x ∉ cthickening (2*δ) (ambientPolynomialZeroSet P)) :
    ∃ a ∈ insert 0 (cellularRoots P b u L),
      δ ≤ rootNext (cellularRoots P b u L) L a-a ∧
      x ∈ flatCylinder (b+a • u) u (rootNext (cellularRoots P b u L) L a-a) δ ∧
      flatCylinder (b+a • u) u (rootNext (cellularRoots P b u L) L a-a) δ ⊆
        flatCylinder b u L δ ∧
      ∀ r ∈ Ioo a (rootNext (cellularRoots P b u L) L a),
        b+r • u ∈ connectedComponentIn (ambientPolynomialZeroSet P)ᶜ x := by
  let R := cellularRoots P b u L
  let Z := ambientPolynomialZeroSet P
  obtain ⟨t,ht0,htL,hti,hxt⟩ := hx
  have hdist : dist x (b+t • u) < δ := hxt
  have hnonzero : (affineLineRestriction P b u).eval t ≠ 0 := by
    intro h
    have hz : b+t • u ∈ Z := by simpa [Z,ambientPolynomialZeroSet,affineLineRestriction_eval] using h
    exact hwall (mem_cthickening_of_dist_le x (b+t • u) (2*δ) Z hz (by linarith))
  have hP0 : affineLineRestriction P b u ≠ 0 := by
    intro h
    exact hnonzero (by rw [h]; simp)
  have hroot (r : ℝ) (hr : r ∈ Ioo (0:ℝ) L) :
      r ∈ R ↔ b+r • u ∈ Z := by
    simp only [R,cellularRoots,Finset.mem_filter,Multiset.mem_toFinset,
      Polynomial.mem_roots hP0,Polynomial.IsRoot,hr.1,hr.2,and_true]
    exact ⟨fun h => by simpa [Z,ambientPolynomialZeroSet,affineLineRestriction_eval] using h,
      fun h => by simpa [Z,ambientPolynomialZeroSet,affineLineRestriction_eval] using h⟩
  have htr : t ∉ R := by
    intro h
    exact hnonzero ((Polynomial.mem_roots hP0).mp
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp h).1))
  obtain ⟨a,ha,hat,htb⟩ := root_intervals_cover R L ⟨ht0,htL⟩ htr
  have ha0 : 0 ≤ a := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact le_rfl
    · exact (cellularRoots_bounds P b u L a ha).1.le
  have hab := rootNext_bounds R L a (hat.trans htL)
  have hgap : ∀ r ∈ Ioo a (rootNext R L a), r ∈ Ioo (0:ℝ) L :=
    fun r hr => ⟨lt_of_le_of_lt ha0 hr.1,lt_of_lt_of_le hr.2 hab.2⟩
  obtain ⟨s,hs0,hsL,hst,hts⟩ := exists_incident_subinterval hδ hL ht0 htL
  have hfree : ∀ r ∈ Ioo s (s+δ), r ∉ R := by
    intro r hr hrr
    have hz := (hroot r ⟨lt_of_le_of_lt hs0 hr.1,lt_of_lt_of_le hr.2 hsL⟩).mp hrr
    have hdr : dist (b+t • u) (b+r • u) < δ := by
      rw [dist_eq_norm,show (b+t • u)-(b+r • u)=(t-r) • u by module,
        norm_smul,Real.norm_eq_abs,hu,mul_one]
      apply abs_lt.mpr
      constructor <;> linarith [hr.1,hr.2]
    have htri := dist_triangle x (b+t • u) (b+r • u)
    exact hwall (mem_cthickening_of_dist_le x (b+r • u) (2*δ) Z hz (by linarith))
  have hlen := root_interval_contains_interval R L a s (s+δ) t ha hs0 hsL
    ⟨hst,hts⟩ ⟨hat,htb⟩ hfree
  refine ⟨a,ha,by linarith [hlen.1,hlen.2],?_,?_,?_⟩
  · have he : (b+a • u)+(t-a) • u=b+t • u := by module
    exact ⟨t-a,by linarith,by linarith,by simpa only [he] using hti,
      by simpa only [he] using hxt⟩
  · rintro y ⟨r,hr0,hrL,hri,hyr⟩
    have he : b+(a+r) • u=(b+a • u)+r • u := by module
    exact ⟨a+r,by linarith,by linarith [hab.2],by simpa only [he] using hri,
      by simpa only [he] using hyr⟩
  · intro r hr
    have hc := offwall_same_component Z (by positivity : 0 < 2*δ) hwall
      (show dist (b+t • u) x < 2*δ by rw [dist_comm]; linarith)
    rw [← hc]
    have hp : IsPreconnected ((fun z : ℝ => b+z • u) '' Ioo a (rootNext R L a)) :=
      isPreconnected_Ioo.image _ (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
    apply hp.subset_connectedComponentIn ⟨t,⟨hat,htb⟩,rfl⟩ _ ⟨r,hr,rfl⟩
    rintro z ⟨v,hv,rfl⟩ hz
    exact root_interval_free R L a v hv ((hroot v (hgap v hv)).mpr hz)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.cellular_gap_count
#print axioms KakeyaTwoScale.cylinder_parameter_unique
#print axioms KakeyaTwoScale.cellular_cylinders_disjoint
#print axioms KakeyaTwoScale.exists_cellular_root_piece
