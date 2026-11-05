import ChenRouteProduction
import ChenRouteBJS

noncomputable section
namespace ChenEffective
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 512

/-- An actual mix: BJS lower/medium producers and the production triple producer. -/
def mixedBJSProductionRoute : ChenRoute routeSourceModel :=
  bjsRoute.withTriple productionRoute.triple

theorem mixed_route_same_margin (n : ℕ) :
    mixedBJSProductionRoute.margin n=bjsRoute.margin n := rfl

/-- Equal numerical envelopes do not erase the replacement producer's cutoff. -/
theorem mixed_route_retains_triple_cutoff :
    qualitativeGeometryThreshold ≤ mixedBJSProductionRoute.threshold := by
  have hh := (chen_route_thresholds_iff mixedBJSProductionRoute mixedBJSProductionRoute.threshold).mp le_rfl
  exact hh.2.2.2.2

private theorem route_nat_pow_mono (a b : ℕ) (h : a ≤ b) : (3:ℕ)^a ≤ 3^b :=
  Nat.pow_le_pow_right (by norm_num) h

theorem bjs_route_cutoff_le_production : bjsStudyGeometryThreshold ≤ qualitativeGeometryThreshold := by
  rw [bjsStudyGeometryThreshold_eq,qualitativeGeometryThreshold_eq]
  have hh : (3:ℕ)^171 ≤ 3^2900 :=
    route_nat_pow_mono 171 2900 (by norm_num)
  exact route_nat_pow_mono (3^171) (3^2900) hh
def mixedRouteCertificate : ChenRouteCertificate mixedBJSProductionRoute where
  cutoff := qualitativeGeometryThreshold
  thresholds_paid := by
    apply (chen_route_thresholds_iff _ _).mpr
    exact ⟨production_route_nine le_rfl,bjs_route_cutoff_le_production,
      bjs_route_cutoff_le_production,qualitative_endpoint le_rfl,le_rfl⟩
  margin_pos := by
    intro n hn he
    rw [mixed_route_same_margin]
    exact bjsRouteCertificate.margin_pos n (bjs_route_cutoff_le_production.trans hn) he

theorem mixed_route_original : Goldbach.ChenTheorem := chen_route_original mixedRouteCertificate

end ChenEffective
