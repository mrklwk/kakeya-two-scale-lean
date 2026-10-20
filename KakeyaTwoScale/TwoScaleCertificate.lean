module
public import KakeyaTwoScale.VolumeCertificate

@[expose] public section

/-! An explicit volume-certificate endpoint. These predicates contain the
analytic estimates that geometry must produce. They do not assert those estimates. -/
open Filter
noncomputable section
namespace KakeyaTwoScale

/-- Neighborhood-volume bounds at delta=rho^20 and rho=2^(-q). -/
structure NeighborhoodUpper (n D : ℝ) (fine coarse : ℕ → ℝ) : Prop where
  fine_nonneg : ∀ q, 0 ≤ fine q
  coarse_nonneg : ∀ q, 0 ≤ coarse q
  bounds : ∀ ε : ℝ, 0 < ε → ∃ Cf Cc : ℝ, 0 < Cf ∧ 0 < Cc ∧
    ∀ᶠ q : ℕ in atTop,
      fine q ≤ Cf*Real.exp (-Real.log 2*20*(n-D-ε)*q) ∧
      coarse q ≤ Cc*Real.exp (-Real.log 2*(n-D-ε)*q)

 theorem NeighborhoodUpper.product_bound {n D : ℝ} {fine coarse : ℕ → ℝ}
    (H : NeighborhoodUpper n D fine coarse) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ q : ℕ in atTop,
      volumeProduct fine coarse q ≤
        C*Real.exp (-Real.log 2*(denominator*(n-D-ε))*q) := by
  obtain ⟨Cf,Cc,hCf,hCc,h⟩ := H.bounds ε hε
  refine ⟨Cf*Cc^(2+a/theta), by positivity, ?_⟩
  filter_upwards [h] with q hq
  exact volumeProduct_upper fine coarse q (n-D-ε) Cf Cc
    (H.fine_nonneg q) (H.coarse_nonneg q) hCf hCc hq.1 hq.2

 def NarrowTransfer (n k : ℝ) (fine coarse : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, ∃ᶠ q : ℕ in atTop,
    c*Real.exp (-Real.log 2*transferExponent n k*q)/(q:ℝ)^L ≤
      volumeProduct fine coarse q

 def zahlB (n k : ℝ) : ℝ := (n^2+k^2+n-k)/(2*n)

 /-- Broad lower bound after rho=delta^(1/20), with an arbitrary loss.
Loss is parameterized directly in the dimension exponent; Zahl's B*epsilon
can be converted to this form once B>0 is established. -/
 def BroadTransfer (n k : ℝ) (fine : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ,
    ∃ᶠ q : ℕ in atTop,
      c*Real.exp (-Real.log 2*20*(n-(zahlB n k-(k-1)/20)+ε)*q)/(q:ℝ)^L ≤ fine q

 theorem broad_endpoint_of_volume_certificate {n k D : ℝ} {fine coarse : ℕ → ℝ}
    (H : NeighborhoodUpper n D fine coarse) (B : BroadTransfer n k fine) :
    zahlB n k-(k-1)/20 ≤ D := by
  have he : ∀ ε : ℝ, 0 < ε →
      (zahlB n k-(k-1)/20-D)-2*ε ≤ 0 := by
    intro ε hε
    obtain ⟨Cf,Cc,hCf,_hCc,hu⟩ := H.bounds ε hε
    obtain ⟨c,hc,L,hl⟩ := B ε hε
    have hf := exponent_le_of_dyadic_envelopes fine
      (20*(n-D-ε)) (20*(n-(zahlB n k-(k-1)/20)+ε)) c Cf L hc hCf
      (by simpa only [mul_assoc] using
        (hl.and_eventually (hu.mono fun q hq => hq.1)))
    linarith
  have h := le_of_forall_positive_loss _ 0 2 (by norm_num) he
  linarith

 /-- Strongest current endpoint: true for arbitrary real volume sequences
 satisfying the displayed estimates; not yet a theorem about Kakeya sets. -/
 theorem endpoint_of_volume_dichotomy {n k D : ℝ} {fine coarse : ℕ → ℝ}
    (hn : 0 < n) (hklo : (n-1)/2 ≤ k) (hkhi : k ≤ n/2)
    (H : NeighborhoodUpper n D fine coarse)
    (h : BroadTransfer n k fine ∨ NarrowTransfer n k fine coarse) :
    (597/1000 : ℝ)*n ≤ D := by
  rcases h with hb | hnarrow
  · have hbD := broad_endpoint_of_volume_certificate H hb
    have hbnum := broad_exponent n k hn hklo hkhi
    change (3/5:ℝ)*n ≤ zahlB n k-(k-1)/20 at hbnum
    linarith
  · exact (narrow_endpoint_of_volume_certificate n k D hn.le hkhi fine coarse
      H.product_bound hnarrow).le

 theorem half_dimension_bounds (n : ℕ) :
    ((n:ℝ)-1)/2 ≤ (n/2:ℕ) ∧ ((n/2:ℕ):ℝ) ≤ (n:ℝ)/2 := by
  have hdiv : 2*(n/2)+n%2=n := Nat.div_add_mod n 2
  have hmod : n%2 ≤ 1 := by omega
  have hd : (2:ℝ)*(n/2:ℕ)+(n%2:ℕ)=n := by exact_mod_cast hdiv
  have hm : ((n%2:ℕ):ℝ) ≤ 1 := by exact_mod_cast hmod
  have hm0 : (0:ℝ) ≤ (n%2:ℕ) := by positivity
  constructor <;> linarith

 theorem endpoint_nat_of_volume_dichotomy (n : ℕ) (hn : 4 ≤ n)
    (D : ℝ) (fine coarse : ℕ → ℝ) (H : NeighborhoodUpper n D fine coarse)
    (h : BroadTransfer n (n/2:ℕ) fine ∨ NarrowTransfer n (n/2:ℕ) fine coarse) :
    (597/1000 : ℝ)*n ≤ D := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  exact endpoint_of_volume_dichotomy hn0 (half_dimension_bounds n).1
    (half_dimension_bounds n).2 H h
end KakeyaTwoScale
#print axioms KakeyaTwoScale.NeighborhoodUpper.product_bound
#print axioms KakeyaTwoScale.broad_endpoint_of_volume_certificate
#print axioms KakeyaTwoScale.endpoint_nat_of_volume_dichotomy
