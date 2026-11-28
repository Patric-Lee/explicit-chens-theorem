import GRHQuarterGroup00
import GRHQuarterGroup01
import GRHQuarterGroup02
import GRHQuarterGroup03
import GRHQuarterGroup04
import GRHQuarterGroup05
import GRHQuarterGroup06
import GRHQuarterGroup07
import GRHQuarterGroup08
import GRHQuarterGroup09
import GRHQuarterGroup10
import GRHQuarterGroup11
import GRHQuarterGroup12
import GRHQuarterGroup13
import GRHQuarterGroup14
import GRHQuarterGroup15
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Kernel-certified real logarithmic Euler envelope, through four million. -/
theorem quarter_prime_envelope_cap (F : Finset ℕ)
 (hF : ∀ p∈F,p.Prime ∧ 2<p ∧ p≤4000000) :
 (∑ p∈F,primeEnvelope p) ≤ (1799/100:ℝ) := by
  classical
  have hp : ∀ p∈F,p.Prime := fun p h => (hF p h).1
  have h0 := GRHQuarterGroup00_bound F hp
  have h1 := GRHQuarterGroup01_bound F hp
  have h2 := GRHQuarterGroup02_bound F hp
  have h3 := GRHQuarterGroup03_bound F hp
  have h4 := GRHQuarterGroup04_bound F hp
  have h5 := GRHQuarterGroup05_bound F hp
  have h6 := GRHQuarterGroup06_bound F hp
  have h7 := GRHQuarterGroup07_bound F hp
  have h8 := GRHQuarterGroup08_bound F hp
  have h9 := GRHQuarterGroup09_bound F hp
  have h10 := GRHQuarterGroup10_bound F hp
  have h11 := GRHQuarterGroup11_bound F hp
  have h12 := GRHQuarterGroup12_bound F hp
  have h13 := GRHQuarterGroup13_bound F hp
  have h14 := GRHQuarterGroup14_bound F hp
  have h15 := GRHQuarterGroup15_bound F hp
  have hstart : envelopePrefix F 2=0 := by
    unfold envelopePrefix
    apply sum_eq_zero
    intro p hp
    have hf := mem_filter.mp hp
    have := (hF p hf.1).2.1
    omega
  have hend : envelopePrefix F 4000016=∑ p∈F,primeEnvelope p := by
    unfold envelopePrefix
    congr 1
    apply filter_eq_self.mpr
    intro p hp
    have := (hF p hp).2.2
    omega
  dsimp only [denominator] at *
  rw [hstart] at h0
  rw [hend] at h15
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15]

#print axioms quarter_prime_envelope_cap
end ChenEffective.H10Band
end
