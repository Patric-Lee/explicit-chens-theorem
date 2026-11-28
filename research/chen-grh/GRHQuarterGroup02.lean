import GRHQuarterMomentSoundness
import GRHQuarterCertificates.C064
import GRHQuarterCertificates.C065
import GRHQuarterCertificates.C066
import GRHQuarterCertificates.C067
import GRHQuarterCertificates.C068
import GRHQuarterCertificates.C069
import GRHQuarterCertificates.C070
import GRHQuarterCertificates.C071
import GRHQuarterCertificates.C072
import GRHQuarterCertificates.C073
import GRHQuarterCertificates.C074
import GRHQuarterCertificates.C075
import GRHQuarterCertificates.C076
import GRHQuarterCertificates.C077
import GRHQuarterCertificates.C078
import GRHQuarterCertificates.C079
import GRHQuarterCertificates.C080
import GRHQuarterCertificates.C081
import GRHQuarterCertificates.C082
import GRHQuarterCertificates.C083
import GRHQuarterCertificates.C084
import GRHQuarterCertificates.C085
import GRHQuarterCertificates.C086
import GRHQuarterCertificates.C087
import GRHQuarterCertificates.C088
import GRHQuarterCertificates.C089
import GRHQuarterCertificates.C090
import GRHQuarterCertificates.C091
import GRHQuarterCertificates.C092
import GRHQuarterCertificates.C093
import GRHQuarterCertificates.C094
import GRHQuarterCertificates.C095
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem GRHQuarterGroup02_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :
 envelopePrefix F 632592 ≤ envelopePrefix F 370448+(1088937638285:ℝ)/denominator := by
  have h0 : envelopePrefix F 378640 ≤ envelopePrefix F 370448+(42361036887:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=370449) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C064.data C064.counts_checked C064.bounds_checked C064.weighted_checked
  have h1 : envelopePrefix F 386832 ≤ envelopePrefix F 378640+(41940949808:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=378641) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C065.data C065.counts_checked C065.bounds_checked C065.weighted_checked
  have h2 : envelopePrefix F 395024 ≤ envelopePrefix F 386832+(41856016588:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=386833) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C066.data C066.counts_checked C066.bounds_checked C066.weighted_checked
  have h3 : envelopePrefix F 403216 ≤ envelopePrefix F 395024+(39247541191:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=395025) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C067.data C067.counts_checked C067.bounds_checked C067.weighted_checked
  have h4 : envelopePrefix F 411408 ≤ envelopePrefix F 403216+(39212467796:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=403217) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C068.data C068.counts_checked C068.bounds_checked C068.weighted_checked
  have h5 : envelopePrefix F 419600 ≤ envelopePrefix F 411408+(39742192158:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=411409) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C069.data C069.counts_checked C069.bounds_checked C069.weighted_checked
  have h6 : envelopePrefix F 427792 ≤ envelopePrefix F 419600+(37828743278:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=419601) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C070.data C070.counts_checked C070.bounds_checked C070.weighted_checked
  have h7 : envelopePrefix F 435984 ≤ envelopePrefix F 427792+(39683470534:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=427793) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C071.data C071.counts_checked C071.bounds_checked C071.weighted_checked
  have h8 : envelopePrefix F 444176 ≤ envelopePrefix F 435984+(37408414721:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=435985) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C072.data C072.counts_checked C072.bounds_checked C072.weighted_checked
  have h9 : envelopePrefix F 452368 ≤ envelopePrefix F 444176+(36025038563:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=444177) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C073.data C073.counts_checked C073.bounds_checked C073.weighted_checked
  have h10 : envelopePrefix F 460560 ≤ envelopePrefix F 452368+(34450524475:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=452369) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C074.data C074.counts_checked C074.bounds_checked C074.weighted_checked
  have h11 : envelopePrefix F 468752 ≤ envelopePrefix F 460560+(35976816816:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=460561) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C075.data C075.counts_checked C075.bounds_checked C075.weighted_checked
  have h12 : envelopePrefix F 476944 ≤ envelopePrefix F 468752+(36182102220:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=468753) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C076.data C076.counts_checked C076.bounds_checked C076.weighted_checked
  have h13 : envelopePrefix F 485136 ≤ envelopePrefix F 476944+(34063441774:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=476945) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C077.data C077.counts_checked C077.bounds_checked C077.weighted_checked
  have h14 : envelopePrefix F 493328 ≤ envelopePrefix F 485136+(34177245529:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=485137) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C078.data C078.counts_checked C078.bounds_checked C078.weighted_checked
  have h15 : envelopePrefix F 501520 ≤ envelopePrefix F 493328+(34564298709:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=493329) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C079.data C079.counts_checked C079.bounds_checked C079.weighted_checked
  have h16 : envelopePrefix F 509712 ≤ envelopePrefix F 501520+(32436494857:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=501521) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C080.data C080.counts_checked C080.bounds_checked C080.weighted_checked
  have h17 : envelopePrefix F 517904 ≤ envelopePrefix F 509712+(33153352653:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=509713) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C081.data C081.counts_checked C081.bounds_checked C081.weighted_checked
  have h18 : envelopePrefix F 526096 ≤ envelopePrefix F 517904+(32816545869:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=517905) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C082.data C082.counts_checked C082.bounds_checked C082.weighted_checked
  have h19 : envelopePrefix F 534288 ≤ envelopePrefix F 526096+(31819855902:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=526097) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C083.data C083.counts_checked C083.bounds_checked C083.weighted_checked
  have h20 : envelopePrefix F 542480 ≤ envelopePrefix F 534288+(30997592245:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=534289) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C084.data C084.counts_checked C084.bounds_checked C084.weighted_checked
  have h21 : envelopePrefix F 550672 ≤ envelopePrefix F 542480+(30899272079:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=542481) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C085.data C085.counts_checked C085.bounds_checked C085.weighted_checked
  have h22 : envelopePrefix F 558864 ≤ envelopePrefix F 550672+(30359686924:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=550673) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C086.data C086.counts_checked C086.bounds_checked C086.weighted_checked
  have h23 : envelopePrefix F 567056 ≤ envelopePrefix F 558864+(30224871911:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=558865) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C087.data C087.counts_checked C087.bounds_checked C087.weighted_checked
  have h24 : envelopePrefix F 575248 ≤ envelopePrefix F 567056+(30286192739:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=567057) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C088.data C088.counts_checked C088.bounds_checked C088.weighted_checked
  have h25 : envelopePrefix F 583440 ≤ envelopePrefix F 575248+(30061076468:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=575249) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C089.data C089.counts_checked C089.bounds_checked C089.weighted_checked
  have h26 : envelopePrefix F 591632 ≤ envelopePrefix F 583440+(29368355037:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=583441) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C090.data C090.counts_checked C090.bounds_checked C090.weighted_checked
  have h27 : envelopePrefix F 599824 ≤ envelopePrefix F 591632+(29157883944:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=591633) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C091.data C091.counts_checked C091.bounds_checked C091.weighted_checked
  have h28 : envelopePrefix F 608016 ≤ envelopePrefix F 599824+(28906140292:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=599825) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C092.data C092.counts_checked C092.bounds_checked C092.weighted_checked
  have h29 : envelopePrefix F 616208 ≤ envelopePrefix F 608016+(28615150360:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=608017) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C093.data C093.counts_checked C093.bounds_checked C093.weighted_checked
  have h30 : envelopePrefix F 624400 ≤ envelopePrefix F 616208+(28104379640:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=616209) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C094.data C094.counts_checked C094.bounds_checked C094.weighted_checked
  have h31 : envelopePrefix F 632592 ≤ envelopePrefix F 624400+(27010486318:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=624401) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C095.data C095.counts_checked C095.bounds_checked C095.weighted_checked
  have m0 : envelopePrefix F 386832 ≤ envelopePrefix F 370448+(84301986695:ℝ)/denominator := by
    dsimp only [denominator] at h0 h1 ⊢
    linarith only [h0,h1]
  have m1 : envelopePrefix F 403216 ≤ envelopePrefix F 386832+(81103557779:ℝ)/denominator := by
    dsimp only [denominator] at h2 h3 ⊢
    linarith only [h2,h3]
  have m2 : envelopePrefix F 419600 ≤ envelopePrefix F 403216+(78954659954:ℝ)/denominator := by
    dsimp only [denominator] at h4 h5 ⊢
    linarith only [h4,h5]
  have m3 : envelopePrefix F 435984 ≤ envelopePrefix F 419600+(77512213812:ℝ)/denominator := by
    dsimp only [denominator] at h6 h7 ⊢
    linarith only [h6,h7]
  have m4 : envelopePrefix F 452368 ≤ envelopePrefix F 435984+(73433453284:ℝ)/denominator := by
    dsimp only [denominator] at h8 h9 ⊢
    linarith only [h8,h9]
  have m5 : envelopePrefix F 468752 ≤ envelopePrefix F 452368+(70427341291:ℝ)/denominator := by
    dsimp only [denominator] at h10 h11 ⊢
    linarith only [h10,h11]
  have m6 : envelopePrefix F 485136 ≤ envelopePrefix F 468752+(70245543994:ℝ)/denominator := by
    dsimp only [denominator] at h12 h13 ⊢
    linarith only [h12,h13]
  have m7 : envelopePrefix F 501520 ≤ envelopePrefix F 485136+(68741544238:ℝ)/denominator := by
    dsimp only [denominator] at h14 h15 ⊢
    linarith only [h14,h15]
  have m8 : envelopePrefix F 517904 ≤ envelopePrefix F 501520+(65589847510:ℝ)/denominator := by
    dsimp only [denominator] at h16 h17 ⊢
    linarith only [h16,h17]
  have m9 : envelopePrefix F 534288 ≤ envelopePrefix F 517904+(64636401771:ℝ)/denominator := by
    dsimp only [denominator] at h18 h19 ⊢
    linarith only [h18,h19]
  have m10 : envelopePrefix F 550672 ≤ envelopePrefix F 534288+(61896864324:ℝ)/denominator := by
    dsimp only [denominator] at h20 h21 ⊢
    linarith only [h20,h21]
  have m11 : envelopePrefix F 567056 ≤ envelopePrefix F 550672+(60584558835:ℝ)/denominator := by
    dsimp only [denominator] at h22 h23 ⊢
    linarith only [h22,h23]
  have m12 : envelopePrefix F 583440 ≤ envelopePrefix F 567056+(60347269207:ℝ)/denominator := by
    dsimp only [denominator] at h24 h25 ⊢
    linarith only [h24,h25]
  have m13 : envelopePrefix F 599824 ≤ envelopePrefix F 583440+(58526238981:ℝ)/denominator := by
    dsimp only [denominator] at h26 h27 ⊢
    linarith only [h26,h27]
  have m14 : envelopePrefix F 616208 ≤ envelopePrefix F 599824+(57521290652:ℝ)/denominator := by
    dsimp only [denominator] at h28 h29 ⊢
    linarith only [h28,h29]
  have m15 : envelopePrefix F 632592 ≤ envelopePrefix F 616208+(55114865958:ℝ)/denominator := by
    dsimp only [denominator] at h30 h31 ⊢
    linarith only [h30,h31]
  have m16 : envelopePrefix F 403216 ≤ envelopePrefix F 370448+(165405544474:ℝ)/denominator := by
    dsimp only [denominator] at m0 m1 ⊢
    linarith only [m0,m1]
  have m17 : envelopePrefix F 435984 ≤ envelopePrefix F 403216+(156466873766:ℝ)/denominator := by
    dsimp only [denominator] at m2 m3 ⊢
    linarith only [m2,m3]
  have m18 : envelopePrefix F 468752 ≤ envelopePrefix F 435984+(143860794575:ℝ)/denominator := by
    dsimp only [denominator] at m4 m5 ⊢
    linarith only [m4,m5]
  have m19 : envelopePrefix F 501520 ≤ envelopePrefix F 468752+(138987088232:ℝ)/denominator := by
    dsimp only [denominator] at m6 m7 ⊢
    linarith only [m6,m7]
  have m20 : envelopePrefix F 534288 ≤ envelopePrefix F 501520+(130226249281:ℝ)/denominator := by
    dsimp only [denominator] at m8 m9 ⊢
    linarith only [m8,m9]
  have m21 : envelopePrefix F 567056 ≤ envelopePrefix F 534288+(122481423159:ℝ)/denominator := by
    dsimp only [denominator] at m10 m11 ⊢
    linarith only [m10,m11]
  have m22 : envelopePrefix F 599824 ≤ envelopePrefix F 567056+(118873508188:ℝ)/denominator := by
    dsimp only [denominator] at m12 m13 ⊢
    linarith only [m12,m13]
  have m23 : envelopePrefix F 632592 ≤ envelopePrefix F 599824+(112636156610:ℝ)/denominator := by
    dsimp only [denominator] at m14 m15 ⊢
    linarith only [m14,m15]
  have m24 : envelopePrefix F 435984 ≤ envelopePrefix F 370448+(321872418240:ℝ)/denominator := by
    dsimp only [denominator] at m16 m17 ⊢
    linarith only [m16,m17]
  have m25 : envelopePrefix F 501520 ≤ envelopePrefix F 435984+(282847882807:ℝ)/denominator := by
    dsimp only [denominator] at m18 m19 ⊢
    linarith only [m18,m19]
  have m26 : envelopePrefix F 567056 ≤ envelopePrefix F 501520+(252707672440:ℝ)/denominator := by
    dsimp only [denominator] at m20 m21 ⊢
    linarith only [m20,m21]
  have m27 : envelopePrefix F 632592 ≤ envelopePrefix F 567056+(231509664798:ℝ)/denominator := by
    dsimp only [denominator] at m22 m23 ⊢
    linarith only [m22,m23]
  have m28 : envelopePrefix F 501520 ≤ envelopePrefix F 370448+(604720301047:ℝ)/denominator := by
    dsimp only [denominator] at m24 m25 ⊢
    linarith only [m24,m25]
  have m29 : envelopePrefix F 632592 ≤ envelopePrefix F 501520+(484217337238:ℝ)/denominator := by
    dsimp only [denominator] at m26 m27 ⊢
    linarith only [m26,m27]
  have m30 : envelopePrefix F 632592 ≤ envelopePrefix F 370448+(1088937638285:ℝ)/denominator := by
    dsimp only [denominator] at m28 m29 ⊢
    linarith only [m28,m29]
  exact m30

#print axioms GRHQuarterGroup02_bound
end ChenEffective.H10Band
end
