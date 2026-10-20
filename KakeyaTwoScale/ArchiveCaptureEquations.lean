module
public import KakeyaTwoScale.ActualArchiveIndexing
public import KakeyaTwoScale.ActualPolynomialCalendar
public import KakeyaTwoScale.ActualArchiveAnalyticSelection
public import KakeyaTwoScale.UniversalCaptureSweep

@[expose] public section

open Set MvPolynomial
noncomputable section
namespace KakeyaTwoScale
namespace PolynomialArchiveSnapshot
variable {k : ℕ} {T C O : Type}

/-- Literal snapshot equations transported to the fixed root coordinates and
padded with zero equations. Padding changes neither the zero set nor degrees. -/
def captureEquations (S : PolynomialArchiveSnapshot k T C O) (n e : ℕ)
    (hd : S.dimension=n) (g : S.state.Grain) (j : Fin e) : MvPolynomial (Fin n) ℝ :=
  if hj : j.val<S.codimension then rename (Fin.cast hd) (S.equations g ⟨j.val,hj⟩) else 0

theorem captureEquations_degree (S : PolynomialArchiveSnapshot k T C O) (n e D : ℕ)
    (hd : S.dimension=n) (g : S.state.Grain)
    (hD : ∀ j, (S.equations g j).totalDegree≤D) (j : Fin e) :
    (S.captureEquations n e hd g j).totalDegree≤D := by
  classical
  unfold captureEquations
  split_ifs with hj
  · exact (totalDegree_rename_le _ _).trans (hD ⟨j.val,hj⟩)
  · simp

/-- The fixed-coordinate padded family has EXACTLY the snapshot zero set. -/
theorem captureEquations_zero (S : PolynomialArchiveSnapshot k T C O) (n e : ℕ)
    (hd : S.dimension=n) (he : S.codimension≤e) (g : S.state.Grain)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∀ j, eval x.ofLp (S.captureEquations n e hd g j)=0) ↔
      (hd.symm ▸ x) ∈ S.zeroSet g := by
  subst n
  change (∀ j, eval x.ofLp (S.captureEquations S.dimension e rfl g j)=0) ↔
    rectangularPolynomialMap (S.equations g) x=0
  have hzero : rectangularPolynomialMap (S.equations g) x=0 ↔
      ∀ j, eval x.ofLp (S.equations g j)=0 := by
    constructor
    · intro hh j; exact congrArg (fun z => z j) hh
    · intro hh; exact PiLp.ext hh
  rw [hzero]
  constructor
  · intro hh j
    have hj : j.val<e := j.isLt.trans_le he
    simpa [captureEquations,j.isLt,rename_id] using hh ⟨j.val,hj⟩
  · intro hh j
    unfold captureEquations
    split_ifs with hj
    · simpa [rename_id] using hh ⟨j.val,hj⟩
    · simp

end PolynomialArchiveSnapshot
namespace ActualBufferedArchive
open PolynomialArchiveSnapshot
variable {k A B Lh a t b c J s : ℕ} {T C O : Type} [DecidableEq T] [DecidableEq C]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T C O} {P U : ℝ} {fuel : ℕ}

/-- Exact indexing supplies a uniform equation budget at every actual entry. -/
theorem polynomialSnapshots_codimension_le
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (S : PolynomialArchiveSnapshot k T C O) (hS : S∈H.polynomialSnapshots) :
    S.codimension≤c+fuel := by
  obtain ⟨j,hj,hget⟩ := List.mem_iff_getElem.mp hS
  have he := H.polynomialSnapshots_codimension j S (by rw [List.getElem?_eq_getElem hj,hget])
  have hl := H.polynomialSnapshots_length_le
  omega

/-- The universal formula receives the original archived equations, not a
population-dependent interpolation through selected lines. -/
def captureEquationFamily (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (y : T) : Fin H.polynomialSnapshots.length → Fin (c+fuel) → MvPolynomial (Fin (b+c)) ℝ :=
  fun j =>
    let S := H.polynomialSnapshots[j]
    S.captureEquations (b+c) (c+fuel)
      (H.polynomialSnapshots_dimension S (List.getElem_mem j.isLt)) (S.state.grain (I.cube y))

/-- Only genuine degree bounds of the snapshots enter coefficient insertion;
no bounded-format hypothesis is assumed for the new relation. -/
theorem captureEquationFamily_degree
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel) (y : T)
    (hy : ∀ S∈H.polynomialSnapshots, y∈S.state.tuples)
    (D : ℕ) (hD : ∀ S∈H.polynomialSnapshots, S.degree≤D) :
    ∀ j q, (H.captureEquationFamily y j q).totalDegree≤D := by
  classical
  intro j q
  let S := H.polynomialSnapshots[j]
  have hS : S∈H.polynomialSnapshots := List.getElem_mem j.isLt
  apply S.captureEquations_degree
  intro z
  exact ((H.polynomialSnapshots_sound S hS).1 _
    (Finset.mem_image.mpr ⟨y,hy S hS,rfl⟩) z).trans (hD S hS)

/-- A literal terminal tuple is a member of every actual polynomial snapshot. -/
theorem terminal_mem_polynomialSnapshots
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (y : T) (hy : y∈H.terminal.state.tuples) :
    ∀ S∈H.polynomialSnapshots, y∈S.state.tuples := by
  intro S hS
  have hp : S.physical∈H.snapshots := by
    rw [← H.polynomialSnapshots_physical]
    exact List.mem_map.mpr ⟨S,hS,rfl⟩
  exact H.terminal_subset_every_snapshot S.physical hp hy

/-- Fixed degree calendar for the actual coefficient family, with tuple
membership and per-entry degree bounds DISCHARGED by the archive construction. -/
theorem captureEquationFamily_degree_calendar
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (y : T) (hy : y∈H.terminal.state.tuples) (J0 : ℕ) (hJ : J≤J0)
    (hs : s=b*t) (hseq : ∀ j∈Finset.range s, I.D j=partitionBoxDegree b j) :
    ∀ j q, (H.captureEquationFamily y j q).totalDegree ≤
      archiveDegreeCalendar (b+c) t J0 fuel := by
  apply H.captureEquationFamily_degree y (H.terminal_mem_polynomialSnapshots y hy)
  intro S hS
  have hh := H.polynomialSnapshots_calendar (b+c) J0 (max I.K 0)
    (le_max_right _ _) 0 rfl hs hseq hJ (le_max_left _ _) S hS
  simpa only [Nat.zero_add] using hh.1

/-- Fixed positive ambient dimension and a fixed equation budget for the
joint capture formula. The extra equation slots are literal zero padding. -/
def captureEquationFamilyAt (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n e : ℕ) (hn : b+c=n+1) (y : T) :
    Fin H.polynomialSnapshots.length → Fin e → MvPolynomial (Fin (n+1)) ℝ :=
  fun j =>
    let S := H.polynomialSnapshots[j]
    S.captureEquations (n+1) e
      ((H.polynomialSnapshots_dimension S (List.getElem_mem j.isLt)).trans hn)
      (S.state.grain (I.cube y))

theorem captureEquationFamilyAt_degree_calendar
    (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel)
    (n e : ℕ) (hn : b+c=n+1) (y : T) (hy : y∈H.terminal.state.tuples)
    (J0 : ℕ) (hJ : J≤J0)
    (hs : s=b*t) (hseq : ∀ j∈Finset.range s, I.D j=partitionBoxDegree b j) :
    ∀ j q, (H.captureEquationFamilyAt n e hn y j q).totalDegree ≤
      archiveDegreeCalendar (n+1) t J0 fuel := by
  classical
  intro j q
  let S := H.polynomialSnapshots[j]
  have hS : S∈H.polynomialSnapshots := List.getElem_mem j.isLt
  apply S.captureEquations_degree
  intro z
  have hc := H.polynomialSnapshots_calendar (n+1) J0 (max I.K 0)
    (le_max_right _ _) 0 hn hs hseq hJ (le_max_left _ _) S hS
  exact ((H.polynomialSnapshots_sound S hS).1 _
    (Finset.mem_image.mpr ⟨y,H.terminal_mem_polynomialSnapshots y hy S hS,rfl⟩) z).trans
    (by simpa only [Nat.zero_add] using hc.1)

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.PolynomialArchiveSnapshot.captureEquations_zero
#print axioms KakeyaTwoScale.ActualBufferedArchive.polynomialSnapshots_codimension_le
#print axioms KakeyaTwoScale.ActualBufferedArchive.captureEquationFamily_degree

#print axioms KakeyaTwoScale.ActualBufferedArchive.captureEquationFamily_degree_calendar

#print axioms KakeyaTwoScale.ActualBufferedArchive.captureEquationFamilyAt_degree_calendar
