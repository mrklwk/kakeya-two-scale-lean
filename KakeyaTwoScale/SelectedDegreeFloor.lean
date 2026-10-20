module
public import KakeyaTwoScale.SelectedAncestorSurvival
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace KakeyaTwoScale

/-- The degree can be below one after mass selection. This exact logarithmic
floor pays the explicit archived-grain retention loss. -/
theorem selected_degree_log_floor {h hnew D A eta dimension : ℝ}
    (hh : 0 < h) (hD : 0 < D) (hA : 0 < A) (heta : 0 < eta)
    (hdegree : hnew = h * D ^ dimension)
    (hsurvive : eta*h ≤ A*hnew) :
    Real.log eta - Real.log A ≤ dimension * Real.log D := by
  have hpow : eta / A ≤ D ^ dimension := by
    apply (div_le_iff₀ hA).mpr
    rw [hdegree] at hsurvive
    nlinarith
  have hlog := Real.log_le_log (div_pos heta hA) hpow
  rw [Real.log_div heta.ne' hA.ne',Real.log_rpow hD] at hlog
  exact hlog

/-- An actual parent lift and old grain upper balance supply the survival
premise for the numerical degree floor; no family record lower bound is used. -/
theorem selected_child_card_survival {T C G H : Type*}
    [DecidableEq T] [DecidableEq C] [DecidableEq G] [DecidableEq H]
    (Y Z : Finset T) (cube : T → C) (cubes : Finset C)
    (parent : C → G) (child : C → H) (lift : H → G)
    (hZY : Z ⊆ Y) (hlift : ∀ y ∈ Z, lift (child (cube y))=parent (cube y))
    {p A eta : ℝ} (hp : 0 < p) (hA : 0 ≤ A)
    (hpos : 0 < tupleCubeMass Y cube cubes p)
    (hret : eta*tupleCubeMass Y cube cubes p ≤ tupleCubeMass Z cube cubes p)
    (hbalance : ∀ g ∈ Y.image (parent ∘ cube),
      tupleCubeMass (Y.filter fun y => parent (cube y)=g) cube cubes p ≤
        A*tupleCubeMass Y cube cubes p/((Y.image (parent ∘ cube)).card:ℝ)) :
    eta*((Y.image (parent ∘ cube)).card:ℝ) ≤ A*((Z.image (child ∘ cube)).card:ℝ) := by
  have hs := selected_ancestor_card_survival Y Z cube cubes parent hZY hp hpos hret hbalance
  have hc : ((Z.image (parent ∘ cube)).card:ℝ) ≤ (Z.image (child ∘ cube)).card := by
    exact_mod_cast represented_parent_card_le Z cube parent child lift hlift
  exact hs.trans (mul_le_mul_of_nonneg_left hc hA)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.selected_degree_log_floor
#print axioms KakeyaTwoScale.selected_child_card_survival
