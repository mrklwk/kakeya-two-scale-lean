module
public import KakeyaTwoScale.EuclideanTubes

@[expose] public section

open MeasureTheory
noncomputable section
namespace KakeyaTwoScale

def heightAffine {n : ℕ} (s L : ℝ) (p : ℝ × (Fin n → ℝ)) : ℝ × (Fin n → ℝ) :=
  (s+L*p.1,p.2)

theorem measurable_heightAffine {n : ℕ} (s L : ℝ) : Measurable (heightAffine (n:=n) s L) :=
  (measurable_const.add (measurable_const.mul measurable_fst)).prodMk measurable_snd

theorem map_heightAffine_volume {n : ℕ} (s : ℝ) {L : ℝ} (hL : 0 < L) :
    Measure.map (heightAffine (n:=n) s L) volume = ENNReal.ofReal L⁻¹ • volume := by
  have hm : Measure.map (fun t : ℝ => s+L*t) volume = ENNReal.ofReal L⁻¹ • volume := by
    rw [show (fun t : ℝ => s+L*t) = (fun t => s+t) ∘ (fun t => L*t) by rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop),Real.map_volume_mul_left hL.ne',
      Measure.map_smul,(measurePreserving_add_left volume s).map_eq]
    rw [abs_of_pos (inv_pos.mpr hL)]
    all_goals fun_prop
  rw [Measure.volume_eq_prod]
  change Measure.map (Prod.map (fun t : ℝ => s+L*t) id) (volume.prod volume) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id,hm,Measure.map_id,
    Measure.prod_smul_left]

/-- Correct Jacobian direction for the preimage of a measurable physical
region under the positive height dilation. -/
theorem volume_heightAffine_preimage {n : ℕ} (s : ℝ) {L : ℝ} (hL : 0 < L)
    (E : Set (ℝ × (Fin n → ℝ))) (hE : MeasurableSet E) :
    volume (heightAffine s L ⁻¹' E)=ENNReal.ofReal L⁻¹*volume E := by
  rw [← Measure.map_apply (measurable_heightAffine s L) hE,map_heightAffine_volume s hL]
  rfl

theorem volume_real_heightAffine_preimage {n : ℕ} (s : ℝ) {L : ℝ} (hL : 0 < L)
    (E : Set (ℝ × (Fin n → ℝ))) (hE : MeasurableSet E) :
    volume.real (heightAffine s L ⁻¹' E)=L⁻¹*volume.real E := by
  rw [Measure.real,volume_heightAffine_preimage s hL E hE,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hL.le)]
  rfl

/-- Coordinate splitting of Euclidean space preserves Lebesgue volume. -/
def euclideanSplit {n : ℕ} (i : Fin (n+1)) : EuclideanSpace ℝ (Fin (n+1)) → ℝ × (Fin n → ℝ) :=
  fun x => (x i,fun j => x (i.succAbove j))

theorem euclideanSplit_measurePreserving {n : ℕ} (i : Fin (n+1)) :
    MeasurePreserving (euclideanSplit i) := by
  exact (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).comp
    (PiLp.volume_preserving_ofLp _)

def euclideanUnsplit {n : ℕ} (i : Fin (n+1)) : ℝ × (Fin n → ℝ) → EuclideanSpace ℝ (Fin (n+1)) :=
  fun p => WithLp.toLp 2 (i.insertNth p.1 p.2)

theorem euclideanUnsplit_measurePreserving {n : ℕ} (i : Fin (n+1)) :
    MeasurePreserving (euclideanUnsplit i) := by
  exact (PiLp.volume_preserving_toLp _).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i))

theorem euclideanUnsplit_split {n : ℕ} (i : Fin (n+1)) (x : EuclideanSpace ℝ (Fin (n+1))) :
    euclideanUnsplit i (euclideanSplit i x)=x := by
  exact congrArg (WithLp.toLp 2)
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm_apply_apply (WithLp.ofLp x))

theorem euclideanSplit_unsplit {n : ℕ} (i : Fin (n+1)) (x : ℝ × (Fin n → ℝ)) :
    euclideanSplit i (euclideanUnsplit i x)=x := by
  exact (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).apply_symm_apply x

end KakeyaTwoScale
#print axioms KakeyaTwoScale.map_heightAffine_volume
#print axioms KakeyaTwoScale.volume_heightAffine_preimage
#print axioms KakeyaTwoScale.volume_real_heightAffine_preimage
#print axioms KakeyaTwoScale.euclideanSplit_measurePreserving
#print axioms KakeyaTwoScale.euclideanUnsplit_measurePreserving
#print axioms KakeyaTwoScale.euclideanUnsplit_split
#print axioms KakeyaTwoScale.euclideanSplit_unsplit
