import GRHQuarterMomentSoundness
import GRHQuarterCertificates.C480
import GRHQuarterCertificates.C481
import GRHQuarterCertificates.C482
import GRHQuarterCertificates.C483
import GRHQuarterCertificates.C484
import GRHQuarterCertificates.C485
import GRHQuarterCertificates.C486
import GRHQuarterCertificates.C487
import GRHQuarterCertificates.C488
import GRHQuarterCertificates.C489
import GRHQuarterCertificates.C490
import GRHQuarterCertificates.C491
import GRHQuarterCertificates.C492
import GRHQuarterCertificates.C493
import GRHQuarterCertificates.C494
import GRHQuarterCertificates.C495
import GRHQuarterCertificates.C496
import GRHQuarterCertificates.C497
import GRHQuarterCertificates.C498
import GRHQuarterCertificates.C499
import GRHQuarterCertificates.C500
import GRHQuarterCertificates.C501
import GRHQuarterCertificates.C502
import GRHQuarterCertificates.C503
import GRHQuarterCertificates.C504
import GRHQuarterCertificates.C505
import GRHQuarterCertificates.C506
import GRHQuarterCertificates.C507
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem GRHQuarterGroup15_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :
 envelopePrefix F 4000016 ≤ envelopePrefix F 3778320+(168235486244:ℝ)/denominator := by
  have h0 : envelopePrefix F 3786512 ≤ envelopePrefix F 3778320+(6429553993:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3778321) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C480.data C480.counts_checked C480.bounds_checked C480.weighted_checked
  have h1 : envelopePrefix F 3794704 ≤ envelopePrefix F 3786512+(6043070884:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3786513) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C481.data C481.counts_checked C481.bounds_checked C481.weighted_checked
  have h2 : envelopePrefix F 3802896 ≤ envelopePrefix F 3794704+(6467599671:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3794705) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C482.data C482.counts_checked C482.bounds_checked C482.weighted_checked
  have h3 : envelopePrefix F 3811088 ≤ envelopePrefix F 3802896+(6457060716:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3802897) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C483.data C483.counts_checked C483.bounds_checked C483.weighted_checked
  have h4 : envelopePrefix F 3819280 ≤ envelopePrefix F 3811088+(6528508625:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3811089) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C484.data C484.counts_checked C484.bounds_checked C484.weighted_checked
  have h5 : envelopePrefix F 3827472 ≤ envelopePrefix F 3819280+(6237880959:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3819281) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C485.data C485.counts_checked C485.bounds_checked C485.weighted_checked
  have h6 : envelopePrefix F 3835664 ≤ envelopePrefix F 3827472+(6344508430:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3827473) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C486.data C486.counts_checked C486.bounds_checked C486.weighted_checked
  have h7 : envelopePrefix F 3843856 ≤ envelopePrefix F 3835664+(6380753033:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3835665) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C487.data C487.counts_checked C487.bounds_checked C487.weighted_checked
  have h8 : envelopePrefix F 3852048 ≤ envelopePrefix F 3843856+(6254409019:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3843857) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C488.data C488.counts_checked C488.bounds_checked C488.weighted_checked
  have h9 : envelopePrefix F 3860240 ≤ envelopePrefix F 3852048+(6325567074:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3852049) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C489.data C489.counts_checked C489.bounds_checked C489.weighted_checked
  have h10 : envelopePrefix F 3868432 ≤ envelopePrefix F 3860240+(6176419250:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3860241) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C490.data C490.counts_checked C490.bounds_checked C490.weighted_checked
  have h11 : envelopePrefix F 3876624 ≤ envelopePrefix F 3868432+(6074054721:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3868433) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C491.data C491.counts_checked C491.bounds_checked C491.weighted_checked
  have h12 : envelopePrefix F 3884816 ≤ envelopePrefix F 3876624+(6145407317:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3876625) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C492.data C492.counts_checked C492.bounds_checked C492.weighted_checked
  have h13 : envelopePrefix F 3893008 ≤ envelopePrefix F 3884816+(6412468541:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3884817) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C493.data C493.counts_checked C493.bounds_checked C493.weighted_checked
  have h14 : envelopePrefix F 3901200 ≤ envelopePrefix F 3893008+(6275847081:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3893009) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C494.data C494.counts_checked C494.bounds_checked C494.weighted_checked
  have h15 : envelopePrefix F 3909392 ≤ envelopePrefix F 3901200+(6173707691:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3901201) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C495.data C495.counts_checked C495.bounds_checked C495.weighted_checked
  have h16 : envelopePrefix F 3917584 ≤ envelopePrefix F 3909392+(6164217151:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3909393) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C496.data C496.counts_checked C496.bounds_checked C496.weighted_checked
  have h17 : envelopePrefix F 3925776 ≤ envelopePrefix F 3917584+(6257578304:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3917585) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C497.data C497.counts_checked C497.bounds_checked C497.weighted_checked
  have h18 : envelopePrefix F 3933968 ≤ envelopePrefix F 3925776+(6259357722:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3925777) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C498.data C498.counts_checked C498.bounds_checked C498.weighted_checked
  have h19 : envelopePrefix F 3942160 ≤ envelopePrefix F 3933968+(6135262413:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3933969) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C499.data C499.counts_checked C499.bounds_checked C499.weighted_checked
  have h20 : envelopePrefix F 3950352 ≤ envelopePrefix F 3942160+(6422287492:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3942161) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C500.data C500.counts_checked C500.bounds_checked C500.weighted_checked
  have h21 : envelopePrefix F 3958544 ≤ envelopePrefix F 3950352+(5945287739:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3950353) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C501.data C501.counts_checked C501.bounds_checked C501.weighted_checked
  have h22 : envelopePrefix F 3966736 ≤ envelopePrefix F 3958544+(5811063751:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3958545) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C502.data C502.counts_checked C502.bounds_checked C502.weighted_checked
  have h23 : envelopePrefix F 3974928 ≤ envelopePrefix F 3966736+(6278870705:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3966737) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C503.data C503.counts_checked C503.bounds_checked C503.weighted_checked
  have h24 : envelopePrefix F 3983120 ≤ envelopePrefix F 3974928+(6076575142:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3974929) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C504.data C504.counts_checked C504.bounds_checked C504.weighted_checked
  have h25 : envelopePrefix F 3991312 ≤ envelopePrefix F 3983120+(5784136356:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3983121) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C505.data C505.counts_checked C505.bounds_checked C505.weighted_checked
  have h26 : envelopePrefix F 3999504 ≤ envelopePrefix F 3991312+(5967495643:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3991313) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C506.data C506.counts_checked C506.bounds_checked C506.weighted_checked
  have h27 : envelopePrefix F 4000016 ≤ envelopePrefix F 3999504+(406536821:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3999505) (w:=4) (degree:=3) (B:=16)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C507.data C507.counts_checked C507.bounds_checked C507.weighted_checked
  have m0 : envelopePrefix F 3794704 ≤ envelopePrefix F 3778320+(12472624877:ℝ)/denominator := by
    dsimp only [denominator] at h0 h1 ⊢
    linarith only [h0,h1]
  have m1 : envelopePrefix F 3811088 ≤ envelopePrefix F 3794704+(12924660387:ℝ)/denominator := by
    dsimp only [denominator] at h2 h3 ⊢
    linarith only [h2,h3]
  have m2 : envelopePrefix F 3827472 ≤ envelopePrefix F 3811088+(12766389584:ℝ)/denominator := by
    dsimp only [denominator] at h4 h5 ⊢
    linarith only [h4,h5]
  have m3 : envelopePrefix F 3843856 ≤ envelopePrefix F 3827472+(12725261463:ℝ)/denominator := by
    dsimp only [denominator] at h6 h7 ⊢
    linarith only [h6,h7]
  have m4 : envelopePrefix F 3860240 ≤ envelopePrefix F 3843856+(12579976093:ℝ)/denominator := by
    dsimp only [denominator] at h8 h9 ⊢
    linarith only [h8,h9]
  have m5 : envelopePrefix F 3876624 ≤ envelopePrefix F 3860240+(12250473971:ℝ)/denominator := by
    dsimp only [denominator] at h10 h11 ⊢
    linarith only [h10,h11]
  have m6 : envelopePrefix F 3893008 ≤ envelopePrefix F 3876624+(12557875858:ℝ)/denominator := by
    dsimp only [denominator] at h12 h13 ⊢
    linarith only [h12,h13]
  have m7 : envelopePrefix F 3909392 ≤ envelopePrefix F 3893008+(12449554772:ℝ)/denominator := by
    dsimp only [denominator] at h14 h15 ⊢
    linarith only [h14,h15]
  have m8 : envelopePrefix F 3925776 ≤ envelopePrefix F 3909392+(12421795455:ℝ)/denominator := by
    dsimp only [denominator] at h16 h17 ⊢
    linarith only [h16,h17]
  have m9 : envelopePrefix F 3942160 ≤ envelopePrefix F 3925776+(12394620135:ℝ)/denominator := by
    dsimp only [denominator] at h18 h19 ⊢
    linarith only [h18,h19]
  have m10 : envelopePrefix F 3958544 ≤ envelopePrefix F 3942160+(12367575231:ℝ)/denominator := by
    dsimp only [denominator] at h20 h21 ⊢
    linarith only [h20,h21]
  have m11 : envelopePrefix F 3974928 ≤ envelopePrefix F 3958544+(12089934456:ℝ)/denominator := by
    dsimp only [denominator] at h22 h23 ⊢
    linarith only [h22,h23]
  have m12 : envelopePrefix F 3991312 ≤ envelopePrefix F 3974928+(11860711498:ℝ)/denominator := by
    dsimp only [denominator] at h24 h25 ⊢
    linarith only [h24,h25]
  have m13 : envelopePrefix F 4000016 ≤ envelopePrefix F 3991312+(6374032464:ℝ)/denominator := by
    dsimp only [denominator] at h26 h27 ⊢
    linarith only [h26,h27]
  have m14 : envelopePrefix F 3811088 ≤ envelopePrefix F 3778320+(25397285264:ℝ)/denominator := by
    dsimp only [denominator] at m0 m1 ⊢
    linarith only [m0,m1]
  have m15 : envelopePrefix F 3843856 ≤ envelopePrefix F 3811088+(25491651047:ℝ)/denominator := by
    dsimp only [denominator] at m2 m3 ⊢
    linarith only [m2,m3]
  have m16 : envelopePrefix F 3876624 ≤ envelopePrefix F 3843856+(24830450064:ℝ)/denominator := by
    dsimp only [denominator] at m4 m5 ⊢
    linarith only [m4,m5]
  have m17 : envelopePrefix F 3909392 ≤ envelopePrefix F 3876624+(25007430630:ℝ)/denominator := by
    dsimp only [denominator] at m6 m7 ⊢
    linarith only [m6,m7]
  have m18 : envelopePrefix F 3942160 ≤ envelopePrefix F 3909392+(24816415590:ℝ)/denominator := by
    dsimp only [denominator] at m8 m9 ⊢
    linarith only [m8,m9]
  have m19 : envelopePrefix F 3974928 ≤ envelopePrefix F 3942160+(24457509687:ℝ)/denominator := by
    dsimp only [denominator] at m10 m11 ⊢
    linarith only [m10,m11]
  have m20 : envelopePrefix F 4000016 ≤ envelopePrefix F 3974928+(18234743962:ℝ)/denominator := by
    dsimp only [denominator] at m12 m13 ⊢
    linarith only [m12,m13]
  have m21 : envelopePrefix F 3843856 ≤ envelopePrefix F 3778320+(50888936311:ℝ)/denominator := by
    dsimp only [denominator] at m14 m15 ⊢
    linarith only [m14,m15]
  have m22 : envelopePrefix F 3909392 ≤ envelopePrefix F 3843856+(49837880694:ℝ)/denominator := by
    dsimp only [denominator] at m16 m17 ⊢
    linarith only [m16,m17]
  have m23 : envelopePrefix F 3974928 ≤ envelopePrefix F 3909392+(49273925277:ℝ)/denominator := by
    dsimp only [denominator] at m18 m19 ⊢
    linarith only [m18,m19]
  have m24 : envelopePrefix F 3909392 ≤ envelopePrefix F 3778320+(100726817005:ℝ)/denominator := by
    dsimp only [denominator] at m21 m22 ⊢
    linarith only [m21,m22]
  have m25 : envelopePrefix F 4000016 ≤ envelopePrefix F 3909392+(67508669239:ℝ)/denominator := by
    dsimp only [denominator] at m23 m20 ⊢
    linarith only [m23,m20]
  have m26 : envelopePrefix F 4000016 ≤ envelopePrefix F 3778320+(168235486244:ℝ)/denominator := by
    dsimp only [denominator] at m24 m25 ⊢
    linarith only [m24,m25]
  exact m26

#print axioms GRHQuarterGroup15_bound
end ChenEffective.H10Band
end
