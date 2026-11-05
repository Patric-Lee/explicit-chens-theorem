import NumericalSquareConstants
import ChenRouteBudget

noncomputable section
namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory SwitchingPrinciple SingularSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def routeSourceScale (n : ℕ) : ℝ := liuSingularSeries n*n/log (n:ℝ)^2

def routeSourceModel : ChenCountingModel where
  scale := routeSourceScale
  scale_pos := by
    intro n hn _he
    exact div_pos (mul_pos (liuSingularSeries_pos n) (by exact_mod_cast (show 0<n by omega)))
      (pow_pos (log_pos (by exact_mod_cast (show 1<n by omega))) 2)
  base := fun n => (jurkatRichertSourceCandidates n).card
  medium := jurkatRichertSourceMediumPrimeAggregate
  boundary := fun n => jurkatRichertSourceWeightedCount n-jurkatRichertWeightedCount n
  triple := correctedChenTriplePenalty
  bridge := by
    intro n hn _he
    have hb := corrected_counting_bridge_public_of_nine_le hn
    rw [correctedChenKeyCount_eq_jurkatRichertWeightedCount_sub_triple] at hb
    have hs := jurkatRichertSourceWeightedCount_eq n
    nlinarith only [hb,hs]

def routeSourceErrors (c : ℝ) (hc : 0 ≤ c) : ChenErrorBreakdown :=
  {other:=ChenErrorEnvelope.constant c hc}

def routeSourceBoundaryErrors : ChenErrorBreakdown :=
  {boundary:=ChenErrorEnvelope.constant (1/20000) (by norm_num)}

def routeSourceTripleErrors : ChenErrorBreakdown :=
  {analytic:=ChenErrorEnvelope.logPower (2*numericalTripleErrorCap) (by positivity) 1}

theorem route_source_boundary {n : ℕ} (hn : lowerEndpointThreshold ≤ n) (he : Even n) :
    routeSourceModel.boundary n ≤ (1/20000:ℝ)*routeSourceScale n := by
  have hbig : 2^110<n := by unfold lowerEndpointThreshold at hn; omega
  have hb := jurkatRichertSourceWeightedCount_sub_boundary_le_distinct n hbig he
  have hp := jurkatRichertDistinctWeightedCount_sub_proper_le n hbig he
  have hl := numerical_lower_endpoint_loss hn
  have hnorm : 60*(n:ℝ)^(9/10:ℝ) ≤ (1/20000:ℝ)*routeSourceScale n := by
    convert hl using 1
    dsimp [routeSourceScale]
    ring
  have hz := rpow_nonneg (Nat.cast_nonneg n) (9/10:ℝ)
  dsimp [routeSourceModel]
  nlinarith only [hb,hp,hnorm,hz]

/-- Normalize the actual inverse-log remainder without paying it by a constant. -/
theorem route_source_triple_error {n : ℕ} (hn : 9 ≤ n) :
    (numericalTripleErrorCap:ℝ)*n/log (n:ℝ)^3 ≤
      routeSourceTripleErrors.eval n*routeSourceScale n := by
  have hl : 0 < log (n:ℝ) := log_pos (by exact_mod_cast (show 1<n by omega))
  have hs := mul_le_mul_of_nonneg_left (half_le_liuSingularSeries n)
    (show 0 ≤ (2*numericalTripleErrorCap:ℝ) by positivity)
  have hm := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg n)
  have hd := div_le_div_of_nonneg_right hm (pow_pos hl 3).le
  norm_num only [mul_one_div] at hd
  have hleft : 2*(numericalTripleErrorCap:ℝ)/2*n/log (n:ℝ)^3 =
      (numericalTripleErrorCap:ℝ)*n/log (n:ℝ)^3 := by ring
  rw [hleft] at hd
  have hright : routeSourceTripleErrors.eval n*routeSourceScale n =
      2*(numericalTripleErrorCap:ℝ)*liuSingularSeries n*n/log (n:ℝ)^3 := by
    dsimp [routeSourceTripleErrors,ChenErrorBreakdown.eval,ChenErrorEnvelope.logPower,
      ChenErrorEnvelope.zero,routeSourceScale]
    field_simp
    ring
  rw [hright]
  exact hd
/-- Assemble independently supplied source bounds. The factory creates no
analytic assumptions; every bound is an explicit proof argument. -/
def routeSourceOfBounds (nBase nMedium nBoundary nTriple : ℕ)
    (bLoss mLoss : ℝ) (hbLoss : 0 ≤ bLoss) (hmLoss : 0 ≤ mLoss)
    (tripleErrors : ChenErrorBreakdown)
    (hbase : ∀ n, nBase ≤ n → Even n →
      (jurkatRichertBaseMainCoefficient jurkatRichertJ-bLoss)*routeSourceScale n ≤
        ((jurkatRichertSourceCandidates n).card:ℝ))
    (hmedium : ∀ n, nMedium ≤ n → Even n →
      jurkatRichertSourceMediumPrimeAggregate n ≤
        (jurkatRichertQ1MainCoefficient jurkatRichertK+mLoss)*routeSourceScale n)
    (hboundary : ∀ n, nBoundary ≤ n → Even n →
      routeSourceModel.boundary n ≤ (1/20000:ℝ)*routeSourceScale n)
    (htriple : ∀ n, nTriple ≤ n → Even n →
      correctedChenTriplePenalty n ≤ (3.94033+tripleErrors.eval n)*routeSourceScale n) :
    ChenRoute routeSourceModel where
  base := {
    threshold:=nBase, main:=fun _ => jurkatRichertBaseMainCoefficient jurkatRichertJ,
    errors:=routeSourceErrors bLoss hbLoss,
    bound:=by simpa [routeSourceModel,routeSourceErrors,ChenErrorBreakdown.eval,
      ChenErrorEnvelope.constant,ChenErrorEnvelope.zero] using hbase}
  medium := {
    threshold:=nMedium,main:=fun _ => jurkatRichertQ1MainCoefficient jurkatRichertK,
    errors:=routeSourceErrors mLoss hmLoss,
    bound:=by simpa [routeSourceModel,routeSourceErrors,ChenErrorBreakdown.eval,
      ChenErrorEnvelope.constant,ChenErrorEnvelope.zero] using hmedium}
  boundary := {
    threshold:=nBoundary,main:=fun _ => 0,errors:=routeSourceBoundaryErrors,
    bound:=by simpa [routeSourceBoundaryErrors,routeSourceModel,ChenErrorBreakdown.eval,
      ChenErrorEnvelope.constant,ChenErrorEnvelope.zero] using hboundary}
  triple := {threshold:=nTriple,main:=fun _ => 3.94033,errors:=tripleErrors,bound:=htriple}

theorem route_source_margin_floor (nb nm nd nt : ℕ) (b m : ℝ)
    (hb : 0 ≤ b) (hm : 0 ≤ m) (e : ChenErrorBreakdown)
    (hbase hmedium hboundary htriple) (n : ℕ) :
    2.6408-b-m/2-1/20000-(3.94033+e.eval n)/2 ≤
      (routeSourceOfBounds nb nm nd nt b m hb hm e hbase hmedium hboundary htriple).margin n := by
  have hh := jurkatRichert_mainCoefficient_ge_twoPoint6408
    jurkatRichertJ jurkatRichertK jurkatRichert_integralEstimate
  dsimp [ChenRoute.margin,ChenLowerProducer.coefficient,ChenUpperProducer.coefficient,
    routeSourceOfBounds,routeSourceErrors,routeSourceBoundaryErrors,ChenErrorBreakdown.eval,
    ChenErrorEnvelope.constant,ChenErrorEnvelope.zero]
  linarith only [hh]

#print axioms route_source_triple_error
end ChenEffective
