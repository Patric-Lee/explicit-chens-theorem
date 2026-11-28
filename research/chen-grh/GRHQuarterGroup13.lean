import GRHQuarterMomentSoundness
import GRHQuarterCertificates.C416
import GRHQuarterCertificates.C417
import GRHQuarterCertificates.C418
import GRHQuarterCertificates.C419
import GRHQuarterCertificates.C420
import GRHQuarterCertificates.C421
import GRHQuarterCertificates.C422
import GRHQuarterCertificates.C423
import GRHQuarterCertificates.C424
import GRHQuarterCertificates.C425
import GRHQuarterCertificates.C426
import GRHQuarterCertificates.C427
import GRHQuarterCertificates.C428
import GRHQuarterCertificates.C429
import GRHQuarterCertificates.C430
import GRHQuarterCertificates.C431
import GRHQuarterCertificates.C432
import GRHQuarterCertificates.C433
import GRHQuarterCertificates.C434
import GRHQuarterCertificates.C435
import GRHQuarterCertificates.C436
import GRHQuarterCertificates.C437
import GRHQuarterCertificates.C438
import GRHQuarterCertificates.C439
import GRHQuarterCertificates.C440
import GRHQuarterCertificates.C441
import GRHQuarterCertificates.C442
import GRHQuarterCertificates.C443
import GRHQuarterCertificates.C444
import GRHQuarterCertificates.C445
import GRHQuarterCertificates.C446
import GRHQuarterCertificates.C447
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem GRHQuarterGroup13_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :
 envelopePrefix F 3516176 ≤ envelopePrefix F 3254032+(222520826850:ℝ)/denominator := by
  have h0 : envelopePrefix F 3262224 ≤ envelopePrefix F 3254032+(7322662687:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3254033) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C416.data C416.counts_checked C416.bounds_checked C416.weighted_checked
  have h1 : envelopePrefix F 3270416 ≤ envelopePrefix F 3262224+(7164322057:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3262225) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C417.data C417.counts_checked C417.bounds_checked C417.weighted_checked
  have h2 : envelopePrefix F 3278608 ≤ envelopePrefix F 3270416+(7426173077:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3270417) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C418.data C418.counts_checked C418.bounds_checked C418.weighted_checked
  have h3 : envelopePrefix F 3286800 ≤ envelopePrefix F 3278608+(6914662739:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3278609) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C419.data C419.counts_checked C419.bounds_checked C419.weighted_checked
  have h4 : envelopePrefix F 3294992 ≤ envelopePrefix F 3286800+(7163417526:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3286801) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C420.data C420.counts_checked C420.bounds_checked C420.weighted_checked
  have h5 : envelopePrefix F 3303184 ≤ envelopePrefix F 3294992+(6758665793:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3294993) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C421.data C421.counts_checked C421.bounds_checked C421.weighted_checked
  have h6 : envelopePrefix F 3311376 ≤ envelopePrefix F 3303184+(7293037822:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3303185) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C422.data C422.counts_checked C422.bounds_checked C422.weighted_checked
  have h7 : envelopePrefix F 3319568 ≤ envelopePrefix F 3311376+(7045642165:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3311377) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C423.data C423.counts_checked C423.bounds_checked C423.weighted_checked
  have h8 : envelopePrefix F 3327760 ≤ envelopePrefix F 3319568+(7110340925:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3319569) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C424.data C424.counts_checked C424.bounds_checked C424.weighted_checked
  have h9 : envelopePrefix F 3335952 ≤ envelopePrefix F 3327760+(6954819502:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3327761) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C425.data C425.counts_checked C425.bounds_checked C425.weighted_checked
  have h10 : envelopePrefix F 3344144 ≤ envelopePrefix F 3335952+(7135824725:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3335953) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C426.data C426.counts_checked C426.bounds_checked C426.weighted_checked
  have h11 : envelopePrefix F 3352336 ≤ envelopePrefix F 3344144+(6929255311:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3344145) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C427.data C427.counts_checked C427.bounds_checked C427.weighted_checked
  have h12 : envelopePrefix F 3360528 ≤ envelopePrefix F 3352336+(6594586310:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3352337) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C428.data C428.counts_checked C428.bounds_checked C428.weighted_checked
  have h13 : envelopePrefix F 3368720 ≤ envelopePrefix F 3360528+(7212307296:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3360529) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C429.data C429.counts_checked C429.bounds_checked C429.weighted_checked
  have h14 : envelopePrefix F 3376912 ≤ envelopePrefix F 3368720+(6955555986:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3368721) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C430.data C430.counts_checked C430.bounds_checked C430.weighted_checked
  have h15 : envelopePrefix F 3385104 ≤ envelopePrefix F 3376912+(7109417764:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3376913) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C431.data C431.counts_checked C431.bounds_checked C431.weighted_checked
  have h16 : envelopePrefix F 3393296 ≤ envelopePrefix F 3385104+(6866478112:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3385105) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C432.data C432.counts_checked C432.bounds_checked C432.weighted_checked
  have h17 : envelopePrefix F 3401488 ≤ envelopePrefix F 3393296+(7070980816:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3393297) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C433.data C433.counts_checked C433.bounds_checked C433.weighted_checked
  have h18 : envelopePrefix F 3409680 ≤ envelopePrefix F 3401488+(7147340739:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3401489) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C434.data C434.counts_checked C434.bounds_checked C434.weighted_checked
  have h19 : envelopePrefix F 3417872 ≤ envelopePrefix F 3409680+(6994587948:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3409681) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C435.data C435.counts_checked C435.bounds_checked C435.weighted_checked
  have h20 : envelopePrefix F 3426064 ≤ envelopePrefix F 3417872+(6867653897:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3417873) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C436.data C436.counts_checked C436.bounds_checked C436.weighted_checked
  have h21 : envelopePrefix F 3434256 ≤ envelopePrefix F 3426064+(6982108153:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3426065) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C437.data C437.counts_checked C437.bounds_checked C437.weighted_checked
  have h22 : envelopePrefix F 3442448 ≤ envelopePrefix F 3434256+(7108778433:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3434257) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C438.data C438.counts_checked C438.bounds_checked C438.weighted_checked
  have h23 : envelopePrefix F 3450640 ≤ envelopePrefix F 3442448+(7007664324:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3442449) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C439.data C439.counts_checked C439.bounds_checked C439.weighted_checked
  have h24 : envelopePrefix F 3458832 ≤ envelopePrefix F 3450640+(6654855683:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3450641) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C440.data C440.counts_checked C440.bounds_checked C440.weighted_checked
  have h25 : envelopePrefix F 3467024 ≤ envelopePrefix F 3458832+(6592700047:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3458833) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C441.data C441.counts_checked C441.bounds_checked C441.weighted_checked
  have h26 : envelopePrefix F 3475216 ≤ envelopePrefix F 3467024+(6782073552:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3467025) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C442.data C442.counts_checked C442.bounds_checked C442.weighted_checked
  have h27 : envelopePrefix F 3483408 ≤ envelopePrefix F 3475216+(6356376648:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3475217) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C443.data C443.counts_checked C443.bounds_checked C443.weighted_checked
  have h28 : envelopePrefix F 3491600 ≤ envelopePrefix F 3483408+(6720592625:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3483409) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C444.data C444.counts_checked C444.bounds_checked C444.weighted_checked
  have h29 : envelopePrefix F 3499792 ≤ envelopePrefix F 3491600+(6783763735:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3491601) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C445.data C445.counts_checked C445.bounds_checked C445.weighted_checked
  have h30 : envelopePrefix F 3507984 ≤ envelopePrefix F 3499792+(6634603902:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3499793) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C446.data C446.counts_checked C446.bounds_checked C446.weighted_checked
  have h31 : envelopePrefix F 3516176 ≤ envelopePrefix F 3507984+(6859576551:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=3507985) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C447.data C447.counts_checked C447.bounds_checked C447.weighted_checked
  have m0 : envelopePrefix F 3270416 ≤ envelopePrefix F 3254032+(14486984744:ℝ)/denominator := by
    dsimp only [denominator] at h0 h1 ⊢
    linarith only [h0,h1]
  have m1 : envelopePrefix F 3286800 ≤ envelopePrefix F 3270416+(14340835816:ℝ)/denominator := by
    dsimp only [denominator] at h2 h3 ⊢
    linarith only [h2,h3]
  have m2 : envelopePrefix F 3303184 ≤ envelopePrefix F 3286800+(13922083319:ℝ)/denominator := by
    dsimp only [denominator] at h4 h5 ⊢
    linarith only [h4,h5]
  have m3 : envelopePrefix F 3319568 ≤ envelopePrefix F 3303184+(14338679987:ℝ)/denominator := by
    dsimp only [denominator] at h6 h7 ⊢
    linarith only [h6,h7]
  have m4 : envelopePrefix F 3335952 ≤ envelopePrefix F 3319568+(14065160427:ℝ)/denominator := by
    dsimp only [denominator] at h8 h9 ⊢
    linarith only [h8,h9]
  have m5 : envelopePrefix F 3352336 ≤ envelopePrefix F 3335952+(14065080036:ℝ)/denominator := by
    dsimp only [denominator] at h10 h11 ⊢
    linarith only [h10,h11]
  have m6 : envelopePrefix F 3368720 ≤ envelopePrefix F 3352336+(13806893606:ℝ)/denominator := by
    dsimp only [denominator] at h12 h13 ⊢
    linarith only [h12,h13]
  have m7 : envelopePrefix F 3385104 ≤ envelopePrefix F 3368720+(14064973750:ℝ)/denominator := by
    dsimp only [denominator] at h14 h15 ⊢
    linarith only [h14,h15]
  have m8 : envelopePrefix F 3401488 ≤ envelopePrefix F 3385104+(13937458928:ℝ)/denominator := by
    dsimp only [denominator] at h16 h17 ⊢
    linarith only [h16,h17]
  have m9 : envelopePrefix F 3417872 ≤ envelopePrefix F 3401488+(14141928687:ℝ)/denominator := by
    dsimp only [denominator] at h18 h19 ⊢
    linarith only [h18,h19]
  have m10 : envelopePrefix F 3434256 ≤ envelopePrefix F 3417872+(13849762050:ℝ)/denominator := by
    dsimp only [denominator] at h20 h21 ⊢
    linarith only [h20,h21]
  have m11 : envelopePrefix F 3450640 ≤ envelopePrefix F 3434256+(14116442757:ℝ)/denominator := by
    dsimp only [denominator] at h22 h23 ⊢
    linarith only [h22,h23]
  have m12 : envelopePrefix F 3467024 ≤ envelopePrefix F 3450640+(13247555730:ℝ)/denominator := by
    dsimp only [denominator] at h24 h25 ⊢
    linarith only [h24,h25]
  have m13 : envelopePrefix F 3483408 ≤ envelopePrefix F 3467024+(13138450200:ℝ)/denominator := by
    dsimp only [denominator] at h26 h27 ⊢
    linarith only [h26,h27]
  have m14 : envelopePrefix F 3499792 ≤ envelopePrefix F 3483408+(13504356360:ℝ)/denominator := by
    dsimp only [denominator] at h28 h29 ⊢
    linarith only [h28,h29]
  have m15 : envelopePrefix F 3516176 ≤ envelopePrefix F 3499792+(13494180453:ℝ)/denominator := by
    dsimp only [denominator] at h30 h31 ⊢
    linarith only [h30,h31]
  have m16 : envelopePrefix F 3286800 ≤ envelopePrefix F 3254032+(28827820560:ℝ)/denominator := by
    dsimp only [denominator] at m0 m1 ⊢
    linarith only [m0,m1]
  have m17 : envelopePrefix F 3319568 ≤ envelopePrefix F 3286800+(28260763306:ℝ)/denominator := by
    dsimp only [denominator] at m2 m3 ⊢
    linarith only [m2,m3]
  have m18 : envelopePrefix F 3352336 ≤ envelopePrefix F 3319568+(28130240463:ℝ)/denominator := by
    dsimp only [denominator] at m4 m5 ⊢
    linarith only [m4,m5]
  have m19 : envelopePrefix F 3385104 ≤ envelopePrefix F 3352336+(27871867356:ℝ)/denominator := by
    dsimp only [denominator] at m6 m7 ⊢
    linarith only [m6,m7]
  have m20 : envelopePrefix F 3417872 ≤ envelopePrefix F 3385104+(28079387615:ℝ)/denominator := by
    dsimp only [denominator] at m8 m9 ⊢
    linarith only [m8,m9]
  have m21 : envelopePrefix F 3450640 ≤ envelopePrefix F 3417872+(27966204807:ℝ)/denominator := by
    dsimp only [denominator] at m10 m11 ⊢
    linarith only [m10,m11]
  have m22 : envelopePrefix F 3483408 ≤ envelopePrefix F 3450640+(26386005930:ℝ)/denominator := by
    dsimp only [denominator] at m12 m13 ⊢
    linarith only [m12,m13]
  have m23 : envelopePrefix F 3516176 ≤ envelopePrefix F 3483408+(26998536813:ℝ)/denominator := by
    dsimp only [denominator] at m14 m15 ⊢
    linarith only [m14,m15]
  have m24 : envelopePrefix F 3319568 ≤ envelopePrefix F 3254032+(57088583866:ℝ)/denominator := by
    dsimp only [denominator] at m16 m17 ⊢
    linarith only [m16,m17]
  have m25 : envelopePrefix F 3385104 ≤ envelopePrefix F 3319568+(56002107819:ℝ)/denominator := by
    dsimp only [denominator] at m18 m19 ⊢
    linarith only [m18,m19]
  have m26 : envelopePrefix F 3450640 ≤ envelopePrefix F 3385104+(56045592422:ℝ)/denominator := by
    dsimp only [denominator] at m20 m21 ⊢
    linarith only [m20,m21]
  have m27 : envelopePrefix F 3516176 ≤ envelopePrefix F 3450640+(53384542743:ℝ)/denominator := by
    dsimp only [denominator] at m22 m23 ⊢
    linarith only [m22,m23]
  have m28 : envelopePrefix F 3385104 ≤ envelopePrefix F 3254032+(113090691685:ℝ)/denominator := by
    dsimp only [denominator] at m24 m25 ⊢
    linarith only [m24,m25]
  have m29 : envelopePrefix F 3516176 ≤ envelopePrefix F 3385104+(109430135165:ℝ)/denominator := by
    dsimp only [denominator] at m26 m27 ⊢
    linarith only [m26,m27]
  have m30 : envelopePrefix F 3516176 ≤ envelopePrefix F 3254032+(222520826850:ℝ)/denominator := by
    dsimp only [denominator] at m28 m29 ⊢
    linarith only [m28,m29]
  exact m30

#print axioms GRHQuarterGroup13_bound
end ChenEffective.H10Band
end
