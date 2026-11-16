import PlattIncrementKernel

/-! A proof-carrying global sum tree. The inductive conclusion prevents closed
sieve computations from being unfolded while composing existing certificates. -/
namespace ChenEffective.PlattWindow
inductive ReciprocalBound : Nat → Nat → Nat → Nat → Prop
  | zero (a : Nat) : ReciprocalBound a a 0 0
  | block {a b lower upper : Nat} {rows : List IncrementRow} :
    CertifiedIncrements rows → checkIncrementSummary a b lower upper rows = true →
      ReciprocalBound a b lower upper
  | append {a b c l₁ u₁ l₂ u₂ : Nat} :
    ReciprocalBound a b l₁ u₁ → ReciprocalBound b c l₂ u₂ →
      ReciprocalBound a c (l₁+l₂) (u₁+u₂)
  | relabel {a b lower upper lower' upper' : Nat} :
    lower=lower' → upper=upper' → ReciprocalBound a b lower upper →
      ReciprocalBound a b lower' upper'
end ChenEffective.PlattWindow
