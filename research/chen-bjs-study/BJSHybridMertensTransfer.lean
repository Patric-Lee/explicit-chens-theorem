import BJSHybridWeightedBridge

noncomputable section
namespace ChenEffective.HybridProduct
open Real Set MeasureTheory AnalyticNumberTheory.Mertens
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def prefixError (x : ℝ) : ℝ :=
  primeReciprocalSum ⌊x⌋₊-(log (log x)+mertensSecondConstant)

theorem actual_prefix_transfer {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    prefixError a = prefixError b+
      (Chebyshev.theta a-a)/(a*log a)-(Chebyshev.theta b-b)/(b*log b)-
      (psi1Error b*prefixWeight b-psi1Error a*prefixWeight a+
        (∫ t in a..b,psi1Error t*prefixSlope t)-
        ∫ t in a..b,(Chebyshev.psi t-Chebyshev.theta t)*prefixWeight t) := by
  have hea := mertensSecond_error_decomposition ha
  have heb := mertensSecond_error_decomposition (ha.trans hab)
  have hi := intervalIntegral.integral_Ioi_sub_Ioi
    (integrableOn_thetaErrorKernel.mono_set (by intro t ht; exact lt_of_le_of_lt ha ht)) hab
  rw [actual_theta_weighted_parts ha hab] at hi
  unfold prefixError
  linarith only [hea,heb,hi]

/-- A certified finite-window bridge. All analytic quantities here are actual
psi1, theta and prime-reciprocal sums; numerical certificate bounds can be
inserted separately without replacing any of these by assumed surrogates. -/
theorem actual_prefix_budget {a b R Ua Ub Fa Fb J P : ℝ}
    (ha : 2 ≤ a) (hab : a ≤ b)
    (hb : |prefixError b| ≤ R)
    (hua : |(Chebyshev.theta a-a)/(a*log a)| ≤ Ua)
    (hub : |(Chebyshev.theta b-b)/(b*log b)| ≤ Ub)
    (hfa : |psi1Error a*prefixWeight a| ≤ Fa)
    (hfb : |psi1Error b*prefixWeight b| ≤ Fb)
    (hj : |∫ t in a..b,psi1Error t*prefixSlope t| ≤ J)
    (hp : |∫ t in a..b,(Chebyshev.psi t-Chebyshev.theta t)*prefixWeight t| ≤ P) :
    |prefixError a| ≤ R+Ua+Ub+Fa+Fb+J+P := by
  rw [actual_prefix_transfer ha hab]
  have hh := abs_add_le (prefixError b) ((Chebyshev.theta a-a)/(a*log a))
  have hh2 := abs_sub (prefixError b+(Chebyshev.theta a-a)/(a*log a))
    ((Chebyshev.theta b-b)/(b*log b))
  have hh3 := abs_sub
    (prefixError b+(Chebyshev.theta a-a)/(a*log a)-(Chebyshev.theta b-b)/(b*log b))
    (psi1Error b*prefixWeight b-psi1Error a*prefixWeight a+
      (∫ t in a..b,psi1Error t*prefixSlope t)-
      ∫ t in a..b,(Chebyshev.psi t-Chebyshev.theta t)*prefixWeight t)
  have h1 := abs_sub (psi1Error b*prefixWeight b) (psi1Error a*prefixWeight a)
  have h2 := abs_add_le (psi1Error b*prefixWeight b-psi1Error a*prefixWeight a)
    (∫ t in a..b,psi1Error t*prefixSlope t)
  have h3 := abs_sub (psi1Error b*prefixWeight b-psi1Error a*prefixWeight a+
      (∫ t in a..b,psi1Error t*prefixSlope t))
      (∫ t in a..b,(Chebyshev.psi t-Chebyshev.theta t)*prefixWeight t)
  linarith only [hh,hh2,hh3,h1,h2,h3,hb,hua,hub,hfa,hfb,hj,hp]

#print axioms actual_prefix_transfer
end ChenEffective.HybridProduct
