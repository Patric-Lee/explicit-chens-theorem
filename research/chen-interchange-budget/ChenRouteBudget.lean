import ChenBudget
import Goldbach.Statement

/-! Interchangeable counting models and proved analytic producers.
No new axioms. A producer must bound its actual counting function; a numeric
coefficient or a descriptive label alone cannot construct one.
-/
noncomputable section
namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory SwitchingPrinciple SingularSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

structure ChenErrorEnvelope where
  eval : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ eval n

namespace ChenErrorEnvelope
def zero : ChenErrorEnvelope := ⟨fun _ => 0,fun _ => le_rfl⟩
def constant (c : ℝ) (hc : 0 ≤ c) : ChenErrorEnvelope := ⟨fun _ => c,fun _ => hc⟩
def add (a b : ChenErrorEnvelope) : ChenErrorEnvelope :=
  ⟨fun n => a.eval n+b.eval n,fun n => add_nonneg (a.nonneg n) (b.nonneg n)⟩
def logPower (c : ℝ) (hc : 0 ≤ c) (k : ℕ) : ChenErrorEnvelope :=
  ⟨fun n => c/(log (n:ℝ))^k,fun n => div_nonneg hc (pow_nonneg (log_natCast_nonneg n) k)⟩
def powerLog (c : ℝ) (hc : 0 ≤ c) (k : ℕ) (δ : ℝ) : ChenErrorEnvelope :=
  ⟨fun n => c*(log (n:ℝ))^k*(n:ℝ)^(-δ),fun n =>
    mul_nonneg (mul_nonneg hc (pow_nonneg (log_natCast_nonneg n) k))
      (rpow_nonneg (Nat.cast_nonneg n) _)⟩
end ChenErrorEnvelope

/-- Separate allocations remain visible; an aggregate legacy bound belongs
in `other`, rather than being assigned an invented decomposition. -/
structure ChenErrorBreakdown where
  product : ChenErrorEnvelope := .zero
  sieve : ChenErrorEnvelope := .zero
  mass : ChenErrorEnvelope := .zero
  distribution : ChenErrorEnvelope := .zero
  rounding : ChenErrorEnvelope := .zero
  boundary : ChenErrorEnvelope := .zero
  analytic : ChenErrorEnvelope := .zero
  other : ChenErrorEnvelope := .zero

def ChenErrorBreakdown.eval (e : ChenErrorBreakdown) (n : ℕ) : ℝ :=
  e.product.eval n+e.sieve.eval n+e.mass.eval n+e.distribution.eval n+
    e.rounding.eval n+e.boundary.eval n+e.analytic.eval n+e.other.eval n

theorem ChenErrorBreakdown.nonneg (e : ChenErrorBreakdown) (n : ℕ) : 0 ≤ e.eval n := by
  unfold ChenErrorBreakdown.eval
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (add_nonneg (e.product.nonneg n) (e.sieve.nonneg n)) (e.mass.nonneg n))
    (e.distribution.nonneg n)) (e.rounding.nonneg n)) (e.boundary.nonneg n))
    (e.analytic.nonneg n)) (e.other.nonneg n)

/-- Different sieve decompositions must supply their own finite counting
bridge to the SAME representation count. Normalizations may also differ. -/
structure ChenCountingModel where
  scale : ℕ → ℝ
  scale_pos : ∀ n, 9 ≤ n → Even n → 0 < scale n
  base : ℕ → ℝ
  medium : ℕ → ℝ
  boundary : ℕ → ℝ
  triple : ℕ → ℝ
  bridge : ∀ n, 9 ≤ n → Even n →
    base n-medium n/2-boundary n-triple n/2 ≤ ((chenGoodRepresentations n).card:ℝ)

structure ChenLowerProducer (scale target : ℕ → ℝ) where
  threshold : ℕ
  main : ℕ → ℝ
  errors : ChenErrorBreakdown
  bound : ∀ n, threshold ≤ n → Even n → (main n-errors.eval n)*scale n ≤ target n

structure ChenUpperProducer (scale target : ℕ → ℝ) where
  threshold : ℕ
  main : ℕ → ℝ
  errors : ChenErrorBreakdown
  bound : ∀ n, threshold ≤ n → Even n → target n ≤ (main n+errors.eval n)*scale n

def ChenLowerProducer.coefficient {s t} (p : ChenLowerProducer s t) (n : ℕ) : ℝ :=
  p.main n-p.errors.eval n
def ChenUpperProducer.coefficient {s t} (p : ChenUpperProducer s t) (n : ℕ) : ℝ :=
  p.main n+p.errors.eval n

structure ChenRoute (m : ChenCountingModel) where
  base : ChenLowerProducer m.scale m.base
  medium : ChenUpperProducer m.scale m.medium
  boundary : ChenUpperProducer m.scale m.boundary
  triple : ChenUpperProducer m.scale m.triple

def ChenRoute.threshold {m} (r : ChenRoute m) : ℕ :=
  max 9 (max (max r.base.threshold r.medium.threshold) (max r.boundary.threshold r.triple.threshold))
def ChenRoute.margin {m} (r : ChenRoute m) (n : ℕ) : ℝ :=
  r.base.coefficient n-r.medium.coefficient n/2-r.boundary.coefficient n-r.triple.coefficient n/2

def ChenRoute.mainMargin {m} (r : ChenRoute m) (n : ℕ) : ℝ :=
  r.base.main n-r.medium.main n/2-r.boundary.main n-r.triple.main n/2
def ChenRoute.errorCost {m} (r : ChenRoute m) (n : ℕ) : ℝ :=
  r.base.errors.eval n+r.medium.errors.eval n/2+r.boundary.errors.eval n+r.triple.errors.eval n/2

theorem chen_route_margin_decomposition {m} (r : ChenRoute m) (n : ℕ) :
    r.margin n=r.mainMargin n-r.errorCost n := by
  dsimp [ChenRoute.margin,ChenRoute.mainMargin,ChenRoute.errorCost,
    ChenLowerProducer.coefficient,ChenUpperProducer.coefficient]
  ring

theorem chen_route_thresholds_iff {m} (r : ChenRoute m) (n : ℕ) :
    r.threshold ≤ n ↔ 9 ≤ n ∧ r.base.threshold ≤ n ∧ r.medium.threshold ≤ n ∧
      r.boundary.threshold ≤ n ∧ r.triple.threshold ≤ n := by
  simp only [ChenRoute.threshold,max_le_iff]
  tauto

theorem chen_route_count {m} (r : ChenRoute m) {n : ℕ}
    (hn : r.threshold ≤ n) (he : Even n) :
    r.margin n*m.scale n ≤ ((chenGoodRepresentations n).card:ℝ) := by
  have h := max_le_iff.mp hn
  have h' := max_le_iff.mp h.2
  have hb := r.base.bound n (max_le_iff.mp h'.1).1 he
  have hm := r.medium.bound n (max_le_iff.mp h'.1).2 he
  have hd := r.boundary.bound n (max_le_iff.mp h'.2).1 he
  have ht := r.triple.bound n (max_le_iff.mp h'.2).2 he
  have hc := m.bridge n h.1 he
  dsimp [ChenRoute.margin,ChenLowerProducer.coefficient,ChenUpperProducer.coefficient]
  nlinarith only [hb,hm,hd,ht,hc]

theorem chen_route_existence {m} (r : ChenRoute m) {n : ℕ}
    (hn : r.threshold ≤ n) (he : Even n) (hmargin : 0 < r.margin n) :
    ∃ p q : ℕ, p.Prime ∧ (q.Prime ∨ ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ q=a*b) ∧ n=p+q := by
  have h9 := (le_max_left _ _).trans hn
  have hc := chen_route_count r hn he
  have hp := (mul_pos hmargin (m.scale_pos n h9 he)).trans_le hc
  have hcard : 0 < (chenGoodRepresentations n).card := by exact_mod_cast hp
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hcard
  simp only [chenGoodRepresentations,Finset.mem_filter,Finset.mem_range] at hp
  exact ⟨p,n-p,hp.2.1,MathlibNt.ChensTheorem.semiprime_iff.mp ⟨hp.2.2.1,hp.2.2.2⟩,by omega⟩

/-- A fixed numeric cutoff with all producer thresholds and positivity paid. -/
structure ChenRouteCertificate {m} (r : ChenRoute m) where
  cutoff : ℕ
  thresholds_paid : r.threshold ≤ cutoff
  margin_pos : ∀ n, cutoff ≤ n → Even n → 0 < r.margin n

theorem chen_route_original {m} {r : ChenRoute m} (c : ChenRouteCertificate r) :
    Goldbach.ChenTheorem :=
  ⟨c.cutoff,fun n hn he => chen_route_existence r (c.thresholds_paid.trans hn) he (c.margin_pos n hn he)⟩

/-- Swap one actual triple producer without rebuilding the other producers. -/
def ChenRoute.withTriple {m} (r : ChenRoute m) (t : ChenUpperProducer m.scale m.triple) :
    ChenRoute m := {r with triple:=t}
def ChenRoute.withBase {m} (r : ChenRoute m) (b : ChenLowerProducer m.scale m.base) :
    ChenRoute m := {r with base:=b}
def ChenRoute.withMedium {m} (r : ChenRoute m) (p : ChenUpperProducer m.scale m.medium) :
    ChenRoute m := {r with medium:=p}
def ChenRoute.withBoundary {m} (r : ChenRoute m) (p : ChenUpperProducer m.scale m.boundary) :
    ChenRoute m := {r with boundary:=p}

theorem chen_route_triple_improvement {m} (r : ChenRoute m)
    (t : ChenUpperProducer m.scale m.triple) (n : ℕ)
    (ht : t.coefficient n ≤ r.triple.coefficient n) :
    r.margin n ≤ (r.withTriple t).margin n := by
  dsimp [ChenRoute.margin,ChenRoute.withTriple]
  linarith only [ht]

#print axioms chen_route_original
end ChenEffective
