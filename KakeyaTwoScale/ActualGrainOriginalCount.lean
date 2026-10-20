module
public import KakeyaTwoScale.ArchiveCoordinateCapture
public import KakeyaTwoScale.SignedGeometricOriginalCount
public import KakeyaTwoScale.OwnedOriginalRepresentatives

@[expose] public section

open Set Metric MeasureTheory
noncomputable section
namespace KakeyaTwoScale

/-- Distinct-original count in an actual archived grain. Every geometric input
to the analytic count is derived from stored tuples, physical ancestry, archive
capture and the original directions. The root length and selected long-grain
radius bounds are explicit geometric boundary conditions. -/
theorem actual_grain_original_count (n t J0 fuel A : ℕ) (K0 C0 : ℝ)
    (hK0 : 0≤K0) (hC0 : 0≤C0) :
    ∃ K : ℝ, 0<K ∧ ∀ (k B Lh a J s : ℕ)
      (T C O : Type) [DecidableEq T] [DecidableEq C] [DecidableEq O]
      (N : Fin k→ℝ) (I : AmbientBufferedStageData (n+1) 0 k A B Lh J s T C O)
      (P U : ℝ) (H : ActualBufferedArchive k A B Lh a t T C O N I P U fuel),
    J≤J0 → s=(n+1)*t → (∀ j∈Finset.range s, I.D j=partitionBoxDegree (n+1) j) → I.K≤K0 →
    (∀ j, I.W.length I.δ j≤1) →
    ∀ (direction : O→EuclideanSpace ℝ (Fin (n+1))),
    (∀ y∈I.W.tuples, ∀ j, I.W.axis j (I.W.parent y j)=direction (I.tube y j)) →
    (∀ o p, o≠p → I.δ/2≤dist (direction o) (direction p)) →
    ∀ (depth : Fin H.polynomialSnapshots.length), 0<depth.val → depth.val≤n+1 →
    let S := H.coordinateState (n+1) rfl depth
    ∀ y∈S.tuples, ∀ (family : Fin k),
    8*(max 1 (archiveRadiusCalendar A K0 fuel)*I.δ)≤S.length I.δ family →
    S.ballRadius≤C0*S.length I.δ family →
    let F := (S.grainRecords I.cube (S.grain (I.cube y)) family).image (S.original family)
    let L := H.prefixCaptureLengths depth family
    (F.card:ℝ)≤K*((max 1 (archiveRadiusCalendar A K0 fuel)*I.δ)+I.δ)^depth.val/
      (I.δ^n*((List.finRange depth.val).map L).prod) := by
  classical
  obtain ⟨K,hK,hcount⟩ := geometric_original_count_all_charts n (n+1+fuel)
    (archiveDegreeCalendar (n+1) t J0 fuel) (fuel+1) C0 hC0
  refine ⟨K,hK,?_⟩
  intro k B Lh a J s T C O _ _ _ N I P U H hJ hs hseq hIK hrootL direction hrootAxis hsep depth hdpos hd
  dsimp only
  let S := H.coordinateState (n+1) rfl depth
  intro z hz family hlong hradius
  let F := (S.grainRecords I.cube (S.grain (I.cube z)) family).image (S.original family)
  let L := H.prefixCaptureLengths depth family
  let rho := max 1 (archiveRadiusCalendar A K0 fuel)*I.δ
  let ell := S.length I.δ family
  let center := S.ballCenter (S.grain (I.cube z))
  let Slevel (i : Fin depth.val) := H.coordinateState (n+1) rfl (H.positivePrefixIndex depth i)
  let equations := H.prefixCaptureEquations n (n+1+fuel) rfl depth z
  have hcert := H.coordinateState_certified (n+1) rfl depth
  have hlocal := H.coordinateState_localized (n+1) rfl depth
  have hz' : z∈(H.polynomialSnapshots[depth]).state.tuples := by
    rwa [H.coordinateState_tuples] at hz
  obtain ⟨Q,hQ⟩ := H.prefix_exists_root_equations n rfl rfl depth z hz' J0 hJ hs hseq
  have howned (o) (ho : o∈F) := S.grain_original_owned_witness I.cube (S.grain (I.cube z)) family o ho
  let y (o : O) : T := if ho : o∈F then (howned o ho).choose else z
  have hy (o) (ho : o∈F) : y o∈S.tuples ∧ S.grain (I.cube (y o))=S.grain (I.cube z) ∧
      S.original family (S.parent (y o) family)=o := by
    dsimp [y]
    rw [dite_eq_left ho]
    exact (howned o ho).choose_spec
  have hwitness (o) (ho : o∈F) : ∃ x, x∈S.geometry I.δ family (S.parent (y o) family) :=
    hcert.2.2.2.1 (y o) (hy o ho).1 family
  let w (o : O) : EuclideanSpace ℝ (Fin (n+1)) := if ho : o∈F then (hwitness o ho).choose else 0
  have hw (o) (ho : o∈F) : w o∈S.geometry I.δ family (S.parent (y o) family) := by
    dsimp [w]
    rw [dite_eq_left ho]
    exact (hwitness o ho).choose_spec
  have hancestor (i : Fin depth.val) := H.coordinateState_ancestor (n+1) rfl
    (H.positivePrefixIndex depth i) depth (H.positivePrefixIndex_le depth i)
  have hlength (i) : (Slevel i).length I.δ family=L i := H.coordinateState_length _ _ _ _
  have hell : 0<ell := by dsimp [ell]; exact mul_pos I.width_pos (pow_pos (by norm_num) _)
  have hdr : I.δ≤rho := by
    dsimp [rho]
    exact le_mul_of_one_le_left I.width_pos.le (le_max_left _ _)
  have hdepth : depth.val≤fuel+1 := by
    have hh := H.polynomialSnapshots_length_le
    have hi := depth.isLt
    omega
  have hlevel_root (i) := H.coordinateState_root (n+1) rfl (H.positivePrefixIndex depth i)
  have hrootcert : BufferedArchiveSnapshot.Certified I.δ I.tube (BufferedArchiveSnapshot.ofState I.W) :=
    BufferedArchiveSnapshot.certified_of_valid _ _ _ _ _ _ I.valid I.nonempty
  have hscale (i) : 0<L i ∧ L i≤1 ∧ ell≤L i ∧ 8*rho≤L i := by
    have hlen := (hancestor i).length_le I.width_pos I.tube
      (H.coordinateState_certified _ _ _) hcert family
    have hupper := (hlevel_root i).length_le I.width_pos I.tube hrootcert
      (H.coordinateState_certified _ _ _) family
    change ell≤(Slevel i).length I.δ family at hlen
    change (Slevel i).length I.δ family≤I.W.length I.δ family at hupper
    rw [hlength i] at hlen hupper
    exact ⟨H.prefixCaptureLengths_pos depth family i,hupper.trans (hrootL family),hlen,hlong.trans hlen⟩
  have huorig (o) (ho : o∈F) : S.axis family (S.parent (y o) family)=direction o := by
    obtain ⟨_,hsub,_,haxes,_⟩ := H.coordinateState_root (n+1) rfl depth
    change ∀ y∈S.tuples, ∀ j, S.axis j (S.parent y j)=I.W.axis j (I.W.parent y j) at haxes
    change S.tuples⊆I.W.tuples at hsub
    have ha := (haxes (y o) (hy o ho).1 family).trans (hrootAxis (y o) (hsub (hy o ho).1) family)
    have he := hcert.2.2.1 (y o) (hy o ho).1 family
    change S.original family (S.parent (y o) family)=I.tube (y o) family at he
    rw [← he,(hy o ho).2.2] at ha
    exact ha
  apply hcount depth.val hdepth hdpos hd O F equations
    (H.prefixCaptureEquations_degree_calendar n (n+1+fuel) rfl depth z hz' J0 hJ hs hseq) Q hQ
    (fun o i => (Slevel i).base family ((Slevel i).parent (y o) family))
    (fun o => S.base family (S.parent (y o) family))
    (fun o => S.axis family (S.parent (y o) family)) w center L ell I.δ rho
    hell I.width_pos hdr (H.prefixCaptureLengths_antitone depth family) hscale
  · intro o ho
    refine ⟨hcert.2.1 family _,hw o ho,?_,?_,?_⟩
    · have hh := hlocal (y o) (hy o ho).1 family (hw o ho)
      change dist (w o) (S.ballCenter (S.grain (I.cube (y o))))<S.ballRadius at hh
      rw [(hy o ho).2.1] at hh
      exact hh.trans_le hradius
    · intro i
      obtain ⟨_,hsub,hcontain,haxes,_⟩ := hancestor i
      change ∀ y∈S.tuples, ∀ j, S.axis j (S.parent y j)=(Slevel i).axis j ((Slevel i).parent y j) at haxes
      change ∀ y∈S.tuples, ∀ j, S.geometry I.δ j (S.parent y j)⊆(Slevel i).geometry I.δ j ((Slevel i).parent y j) at hcontain
      have hh := hcontain (y o) (hy o ho).1 family
      change flatCylinder _ _ _ _⊆flatCylinder _ _ _ _ at hh
      rw [hlength i,← haxes (y o) (hy o ho).1 family] at hh
      exact hh
    · intro i
      obtain ⟨_,hsub,hcontain,haxes,_⟩ := hancestor i
      change ∀ y∈S.tuples, ∀ j, S.axis j (S.parent y j)=(Slevel i).axis j ((Slevel i).parent y j) at haxes
      have hh := H.coordinate_prefix_capture n rfl depth (y o) z (hy o ho).1 hz (hy o ho).2.1
        J0 hJ hs hseq K0 hK0 hIK i family
      change flatCylinder ((Slevel i).base family ((Slevel i).parent (y o) family))
        ((Slevel i).axis family ((Slevel i).parent (y o) family)) ((Slevel i).length I.δ family) I.δ⊆_ at hh
      rw [hlength i,← haxes (y o) (hy o ho).1 family] at hh
      exact hh
  · intro o ho p hp hop
    rw [huorig o ho,huorig p hp]
    exact hsep o p hop

end KakeyaTwoScale
#print axioms KakeyaTwoScale.actual_grain_original_count
