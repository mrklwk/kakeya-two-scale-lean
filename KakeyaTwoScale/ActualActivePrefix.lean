module
public import KakeyaTwoScale.ActualDegreePrefixLog

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
namespace ActualBufferedArchive
variable {k A B Lh a t b c J s : ℕ} {T Q O : Type} [DecidableEq T] [DecidableEq Q]
    {N : Fin k→ℝ} {I : AmbientBufferedStageData b c k A B Lh J s T Q O}
    {P U : ℝ} {fuel : ℕ}

@[simp] theorem entryAt_zero (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel) :
    H.entryAt 0 (by omega)=⟨.ofState I.W,P,U⟩ := by cases H <;> rfl

@[simp] theorem entryAt_next_succ
    (Z : ActualNormalizedBufferedStage I.toInput N P U a) (hb : 1<b) (ht : 2≤t)
    (tail : ActualBufferedArchive k A B Lh a t T Q O N (I.nextData Z hb t ht)
      (P*Z.degree) Z.upperFactor (fuel+1)) (r : ℕ)
    (hr : r+1≤(ActualBufferedArchive.next I P U Z hb ht tail).drops) :
    (ActualBufferedArchive.next I P U Z hb ht tail).entryAt (r+1) hr=
      tail.entryAt r (by change r+1≤tail.drops+1 at hr; omega) := by
  rfl

/-- Positive archive levels have the actual active-family lower counts.
This is a statement about their full stored records, never about a later
selected marginal. Height-zero families are explicitly excluded. -/
theorem entryAt_active_lower
    (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel)
    (r : ℕ) (hr : r≤H.drops) (hr0 : 0<r) :
    ∀ g∈(H.entryAt r hr).snapshot.state.grains I.cube, ∀j,
      0<(H.entryAt r hr).snapshot.state.height j →
      N j*(H.entryAt r hr).prefixProduct/((H.entryAt r hr).snapshot.state.grains I.cube).card ≤
        ((H.entryAt r hr).snapshot.state.grainRecords I.cube g j).card := by
  classical
  induction H generalizing r with
  | zero => simp only [drops] at hr; omega
  | short => simp only [drops] at hr; omega
  | last I P U Z =>
    have he : r=1 := by change r≤1 at hr; omega
    subst r
    exact Z.lower
  | next I P U Z hb ht tail ih =>
    cases r with
    | zero => omega
    | succ r =>
      rw [entryAt_next_succ]
      cases r with
      | zero =>
        rw [entryAt_zero]
        let Lower (S : BufferedArchiveSnapshot k T Q O) : Prop :=
          ∀g∈S.state.grains I.cube, ∀j, 0<S.state.height j →
            N j*(P*Z.degree)/(S.state.grains I.cube).card≤(S.state.grainRecords I.cube g j).card
        change Lower (.ofState (I.nextData Z hb t ht).W)
        rw [AmbientBufferedStageData.nextData_snapshot]
        exact Z.lower
      | succ r =>
        simpa only [AmbientBufferedStageData.nextData_cube] using ih (r+1) (by change r+1+1≤tail.drops+1 at hr; omega) (by omega)

/-- Each active adjacent step keeps the same named family and uses the
incoming ledger upper factor. Both lengths are literal stored lengths. -/
theorem entryAt_active_length_step
    (H : ActualBufferedArchive k A B Lh a t T Q O N I P U fuel) :
    (∀j, 0<N j) → 0<P → (∀j, (I.W.count j:ℝ)≤U*(N j*P)) →
    ∀ (i : ℕ) (hi : i+1≤H.drops) (j : Fin k),
      0<(H.entryAt (i+1) hi).snapshot.state.height j →
      (H.stageDegrees[i]?.getD 1)*(H.entryAt (i+1) hi).snapshot.state.length I.δ j ≤
        (H.entryAt i (by omega)).upper*(H.entryAt i (by omega)).snapshot.state.length I.δ j := by
  induction H with
  | zero => intro _ _ _ i hi; simp only [drops] at hi; omega
  | short => intro _ _ _ i hi; simp only [drops] at hi; omega
  | last I P U Z =>
    intro hN hP hcount i hi j hj
    have he : i=0 := by change i+1≤1 at hi; omega
    subst i
    exact Z.active_length_step j hj (hN j) hP (hcount j)
  | next I P U Z hb ht tail ih =>
    intro hN hP hcount i hi j hj
    cases i with
    | zero =>
      rw [entryAt_next_succ,entryAt_zero] at hj ⊢
      rw [entryAt_zero]
      change 0<(BufferedArchiveSnapshot.ofState (I.nextData Z hb t ht).W).state.height j at hj
      rw [AmbientBufferedStageData.nextData_snapshot] at hj
      have hh := Z.active_length_step j hj (hN j) hP (hcount j)
      change Z.degree*(BufferedArchiveSnapshot.ofState (I.nextData Z hb t ht).W).state.length I.δ j≤_
      rw [AmbientBufferedStageData.nextData_snapshot]
      exact hh
    | succ i =>
      rw [entryAt_next_succ] at hj ⊢
      rw [entryAt_next_succ]
      have hc : ∀j, (((I.nextData Z hb t ht).W.count j):ℝ)≤Z.upperFactor*(N j*(P*Z.degree)) := by
        intro j
        simpa only [AmbientBufferedStageData.nextData_count] using Z.total_count j
      have hh := ih hN (mul_pos hP Z.degree_pos) hc i (by change i+1+1≤tail.drops+1 at hi; omega) j hj
      simpa only [stageDegrees,List.getElem?_cons_succ,AmbientBufferedStageData.nextData_delta] using hh

end ActualBufferedArchive
end KakeyaTwoScale
#print axioms KakeyaTwoScale.ActualBufferedArchive.entryAt_active_lower

#print axioms KakeyaTwoScale.ActualBufferedArchive.entryAt_active_length_step
