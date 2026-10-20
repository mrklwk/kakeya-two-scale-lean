module
public import KakeyaTwoScale.UniversalZeroNeighborhood
public import KakeyaTwoScale.PrescribedFatSignFormula

@[expose] public section

open Set MvPolynomial
open OAI.Release061 OAI.Release061.SignElimination
noncomputable section
namespace KakeyaTwoScale

abbrev TubeRecursionParameter (n r e : ℕ) := CaptureParameter n r e⊕Fin r

def nestedTubeBase {n r e : ℕ} (D : ℕ) (B : ℝ)
    (p : TubeRecursionParameter n r e→ℝ) (i : Fin r) (x : Fin (n+1)→ℝ) : Prop :=
  0<p (Sum.inl (.length i)) ∧
  universalZeroNear D (fun q => p (Sum.inl q)) i x ∧
  (∑ j, (x j-p (Sum.inl (.center j)))^2)<((B+2)*p (Sum.inl (.length i)))^2

/-- Actual backward Fat/neighborhood recursion, expressed in one fixed joint
formula. Dilation factors are parameter coordinates, avoiding implicit division. -/
def nestedTubeFormula {n r e : ℕ} (D : ℕ) (B kappa beta : ℝ) :
    List (Fin r) → (TubeRecursionParameter n r e→ℝ) → (Fin (n+1)→ℝ) → Prop
  | [], _, _ => False
  | [i], p, x => nestedTubeBase D B p i x
  | i::j::rest, p, x =>
    universalZeroNear D (fun q => p (Sum.inl q)) i x ∧
    prescribedFatFormula (p (Sum.inr i)) (kappa*p (Sum.inl (.length j)))
      (beta*p (Sum.inl .radius)) {y | nestedTubeFormula D B kappa beta (j::rest) p y} x

def nestedTubeFamily {n r e : ℕ} (D : ℕ) (B kappa beta : ℝ) (levels : List (Fin r)) :
    Set ((TubeRecursionParameter n r e→ℝ) × (Fin (n+1)→ℝ)) :=
  {z | nestedTubeFormula D B kappa beta levels z.1 z.2}

/-- The COMPLETE recursive family is jointly polynomial-sign. The formula
contains no atom indexed by a finite population of original lines. -/
theorem nestedTubeFamily_sign (n r e D : ℕ) (B kappa beta : ℝ) (levels : List (Fin r)) :
    PolynomialSignSet (fun z => Sum.elim z.1 z.2) (nestedTubeFamily (n := n) (e := e) D B kappa beta levels) := by
  let X := (TubeRecursionParameter n r e→ℝ) × (Fin (n+1)→ℝ)
  let c : X→TubeRecursionParameter n r e⊕Fin (n+1)→ℝ := fun z => Sum.elim z.1 z.2
  have hp (q : CaptureParameter n r e) : PolynomialScalar c (fun z => z.1 (Sum.inl q)) :=
    PolynomialScalar.coordinate (Sum.inl (Sum.inl q))
  have hx (j) : PolynomialScalar c (fun z => z.2 j) := PolynomialScalar.coordinate (Sum.inr j)
  have hnear (i) := universalZeroNear_sign c D (fun z q => z.1 (Sum.inl q)) Prod.snd hp hx i
  induction levels with
  | nil => exact PolynomialSignSet.empty
  | cons i tail ih =>
    cases tail with
    | nil =>
      have hd : PolynomialScalar c (fun z => ∑ j, (z.2 j-z.1 (Sum.inl (.center j)))^2) :=
        PolynomialScalar.sum Finset.univ _ (fun j _ => ((hx j).sub (hp (.center j))).pow 2)
      exact ((PolynomialScalar.const 0).lt (hp (.length i))).inter ((hnear i).inter
        (hd.lt (((PolynomialScalar.const (B+2)).mul (hp (.length i))).pow 2)))
    | cons j rest =>
      have hfat := prescribedFatFormula_sign c Prod.fst Prod.snd
        (fun z => z.1 (Sum.inr i)) (fun z => kappa*z.1 (Sum.inl (.length j)))
        (fun z => beta*z.1 (Sum.inl .radius))
        (nestedTubeFamily D B kappa beta (j::rest)) ih
        (fun q => PolynomialScalar.coordinate (Sum.inl q)) hx
        (PolynomialScalar.coordinate (Sum.inl (Sum.inr i)))
        ((PolynomialScalar.const kappa).mul (hp (.length j)))
        ((PolynomialScalar.const beta).mul (hp .radius))
      exact (hnear i).inter hfat

end KakeyaTwoScale
#print axioms KakeyaTwoScale.nestedTubeFamily_sign
