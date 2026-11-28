import GRHQuarterMomentSoundness
import GRHQuarterCertificates.C160
import GRHQuarterCertificates.C161
import GRHQuarterCertificates.C162
import GRHQuarterCertificates.C163
import GRHQuarterCertificates.C164
import GRHQuarterCertificates.C165
import GRHQuarterCertificates.C166
import GRHQuarterCertificates.C167
import GRHQuarterCertificates.C168
import GRHQuarterCertificates.C169
import GRHQuarterCertificates.C170
import GRHQuarterCertificates.C171
import GRHQuarterCertificates.C172
import GRHQuarterCertificates.C173
import GRHQuarterCertificates.C174
import GRHQuarterCertificates.C175
import GRHQuarterCertificates.C176
import GRHQuarterCertificates.C177
import GRHQuarterCertificates.C178
import GRHQuarterCertificates.C179
import GRHQuarterCertificates.C180
import GRHQuarterCertificates.C181
import GRHQuarterCertificates.C182
import GRHQuarterCertificates.C183
import GRHQuarterCertificates.C184
import GRHQuarterCertificates.C185
import GRHQuarterCertificates.C186
import GRHQuarterCertificates.C187
import GRHQuarterCertificates.C188
import GRHQuarterCertificates.C189
import GRHQuarterCertificates.C190
import GRHQuarterCertificates.C191
noncomputable section
namespace ChenEffective.H10Band
open Real Finset QuarterCert
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem GRHQuarterGroup05_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :
 envelopePrefix F 1419024 ≤ envelopePrefix F 1156880+(492995232186:ℝ)/denominator := by
  have h0 : envelopePrefix F 1165072 ≤ envelopePrefix F 1156880+(17475981521:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1156881) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C160.data C160.counts_checked C160.bounds_checked C160.weighted_checked
  have h1 : envelopePrefix F 1173264 ≤ envelopePrefix F 1165072+(16475739187:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1165073) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C161.data C161.counts_checked C161.bounds_checked C161.weighted_checked
  have h2 : envelopePrefix F 1181456 ≤ envelopePrefix F 1173264+(17123265360:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1173265) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C162.data C162.counts_checked C162.bounds_checked C162.weighted_checked
  have h3 : envelopePrefix F 1189648 ≤ envelopePrefix F 1181456+(16754206318:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1181457) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C163.data C163.counts_checked C163.bounds_checked C163.weighted_checked
  have h4 : envelopePrefix F 1197840 ≤ envelopePrefix F 1189648+(16304693948:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1189649) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C164.data C164.counts_checked C164.bounds_checked C164.weighted_checked
  have h5 : envelopePrefix F 1206032 ≤ envelopePrefix F 1197840+(15665107640:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1197841) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C165.data C165.counts_checked C165.bounds_checked C165.weighted_checked
  have h6 : envelopePrefix F 1214224 ≤ envelopePrefix F 1206032+(16303554403:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1206033) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C166.data C166.counts_checked C166.bounds_checked C166.weighted_checked
  have h7 : envelopePrefix F 1222416 ≤ envelopePrefix F 1214224+(15920027985:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1214225) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C167.data C167.counts_checked C167.bounds_checked C167.weighted_checked
  have h8 : envelopePrefix F 1230608 ≤ envelopePrefix F 1222416+(15949316819:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1222417) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C168.data C168.counts_checked C168.bounds_checked C168.weighted_checked
  have h9 : envelopePrefix F 1238800 ≤ envelopePrefix F 1230608+(15351402009:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1230609) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C169.data C169.counts_checked C169.bounds_checked C169.weighted_checked
  have h10 : envelopePrefix F 1246992 ≤ envelopePrefix F 1238800+(15899526221:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1238801) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C170.data C170.counts_checked C170.bounds_checked C170.weighted_checked
  have h11 : envelopePrefix F 1255184 ≤ envelopePrefix F 1246992+(15902795751:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1246993) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C171.data C171.counts_checked C171.bounds_checked C171.weighted_checked
  have h12 : envelopePrefix F 1263376 ≤ envelopePrefix F 1255184+(15905476045:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1255185) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C172.data C172.counts_checked C172.bounds_checked C172.weighted_checked
  have h13 : envelopePrefix F 1271568 ≤ envelopePrefix F 1263376+(16015180830:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1263377) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C173.data C173.counts_checked C173.bounds_checked C173.weighted_checked
  have h14 : envelopePrefix F 1279760 ≤ envelopePrefix F 1271568+(15113278626:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1271569) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C174.data C174.counts_checked C174.bounds_checked C174.weighted_checked
  have h15 : envelopePrefix F 1287952 ≤ envelopePrefix F 1279760+(15596777144:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1279761) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C175.data C175.counts_checked C175.bounds_checked C175.weighted_checked
  have h16 : envelopePrefix F 1296144 ≤ envelopePrefix F 1287952+(15101715054:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1287953) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C176.data C176.counts_checked C176.bounds_checked C176.weighted_checked
  have h17 : envelopePrefix F 1304336 ≤ envelopePrefix F 1296144+(15396617640:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1296145) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C177.data C177.counts_checked C177.bounds_checked C177.weighted_checked
  have h18 : envelopePrefix F 1312528 ≤ envelopePrefix F 1304336+(14932563409:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1304337) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C178.data C178.counts_checked C178.bounds_checked C178.weighted_checked
  have h19 : envelopePrefix F 1320720 ≤ envelopePrefix F 1312528+(14629976323:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1312529) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C179.data C179.counts_checked C179.bounds_checked C179.weighted_checked
  have h20 : envelopePrefix F 1328912 ≤ envelopePrefix F 1320720+(15519831881:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1320721) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C180.data C180.counts_checked C180.bounds_checked C180.weighted_checked
  have h21 : envelopePrefix F 1337104 ≤ envelopePrefix F 1328912+(14674306221:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1328913) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C181.data C181.counts_checked C181.bounds_checked C181.weighted_checked
  have h22 : envelopePrefix F 1345296 ≤ envelopePrefix F 1337104+(15068913194:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1337105) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C182.data C182.counts_checked C182.bounds_checked C182.weighted_checked
  have h23 : envelopePrefix F 1353488 ≤ envelopePrefix F 1345296+(14463875778:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1345297) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C183.data C183.counts_checked C183.bounds_checked C183.weighted_checked
  have h24 : envelopePrefix F 1361680 ≤ envelopePrefix F 1353488+(14703548068:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1353489) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C184.data C184.counts_checked C184.bounds_checked C184.weighted_checked
  have h25 : envelopePrefix F 1369872 ≤ envelopePrefix F 1361680+(14713139965:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1361681) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C185.data C185.counts_checked C185.bounds_checked C185.weighted_checked
  have h26 : envelopePrefix F 1378064 ≤ envelopePrefix F 1369872+(14646660934:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1369873) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C186.data C186.counts_checked C186.bounds_checked C186.weighted_checked
  have h27 : envelopePrefix F 1386256 ≤ envelopePrefix F 1378064+(14632638406:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1378065) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C187.data C187.counts_checked C187.bounds_checked C187.weighted_checked
  have h28 : envelopePrefix F 1394448 ≤ envelopePrefix F 1386256+(14268030038:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1386257) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C188.data C188.counts_checked C188.bounds_checked C188.weighted_checked
  have h29 : envelopePrefix F 1402640 ≤ envelopePrefix F 1394448+(14926506802:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1394449) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C189.data C189.counts_checked C189.bounds_checked C189.weighted_checked
  have h30 : envelopePrefix F 1410832 ≤ envelopePrefix F 1402640+(13994726666:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1402641) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C190.data C190.counts_checked C190.bounds_checked C190.weighted_checked
  have h31 : envelopePrefix F 1419024 ≤ envelopePrefix F 1410832+(13565852000:ℝ)/denominator :=
    certified_envelope_prefix F hF (lo:=1410833) (w:=4) (degree:=3) (B:=256)
      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])
      C191.data C191.counts_checked C191.bounds_checked C191.weighted_checked
  have m0 : envelopePrefix F 1173264 ≤ envelopePrefix F 1156880+(33951720708:ℝ)/denominator := by
    dsimp only [denominator] at h0 h1 ⊢
    linarith only [h0,h1]
  have m1 : envelopePrefix F 1189648 ≤ envelopePrefix F 1173264+(33877471678:ℝ)/denominator := by
    dsimp only [denominator] at h2 h3 ⊢
    linarith only [h2,h3]
  have m2 : envelopePrefix F 1206032 ≤ envelopePrefix F 1189648+(31969801588:ℝ)/denominator := by
    dsimp only [denominator] at h4 h5 ⊢
    linarith only [h4,h5]
  have m3 : envelopePrefix F 1222416 ≤ envelopePrefix F 1206032+(32223582388:ℝ)/denominator := by
    dsimp only [denominator] at h6 h7 ⊢
    linarith only [h6,h7]
  have m4 : envelopePrefix F 1238800 ≤ envelopePrefix F 1222416+(31300718828:ℝ)/denominator := by
    dsimp only [denominator] at h8 h9 ⊢
    linarith only [h8,h9]
  have m5 : envelopePrefix F 1255184 ≤ envelopePrefix F 1238800+(31802321972:ℝ)/denominator := by
    dsimp only [denominator] at h10 h11 ⊢
    linarith only [h10,h11]
  have m6 : envelopePrefix F 1271568 ≤ envelopePrefix F 1255184+(31920656875:ℝ)/denominator := by
    dsimp only [denominator] at h12 h13 ⊢
    linarith only [h12,h13]
  have m7 : envelopePrefix F 1287952 ≤ envelopePrefix F 1271568+(30710055770:ℝ)/denominator := by
    dsimp only [denominator] at h14 h15 ⊢
    linarith only [h14,h15]
  have m8 : envelopePrefix F 1304336 ≤ envelopePrefix F 1287952+(30498332694:ℝ)/denominator := by
    dsimp only [denominator] at h16 h17 ⊢
    linarith only [h16,h17]
  have m9 : envelopePrefix F 1320720 ≤ envelopePrefix F 1304336+(29562539732:ℝ)/denominator := by
    dsimp only [denominator] at h18 h19 ⊢
    linarith only [h18,h19]
  have m10 : envelopePrefix F 1337104 ≤ envelopePrefix F 1320720+(30194138102:ℝ)/denominator := by
    dsimp only [denominator] at h20 h21 ⊢
    linarith only [h20,h21]
  have m11 : envelopePrefix F 1353488 ≤ envelopePrefix F 1337104+(29532788972:ℝ)/denominator := by
    dsimp only [denominator] at h22 h23 ⊢
    linarith only [h22,h23]
  have m12 : envelopePrefix F 1369872 ≤ envelopePrefix F 1353488+(29416688033:ℝ)/denominator := by
    dsimp only [denominator] at h24 h25 ⊢
    linarith only [h24,h25]
  have m13 : envelopePrefix F 1386256 ≤ envelopePrefix F 1369872+(29279299340:ℝ)/denominator := by
    dsimp only [denominator] at h26 h27 ⊢
    linarith only [h26,h27]
  have m14 : envelopePrefix F 1402640 ≤ envelopePrefix F 1386256+(29194536840:ℝ)/denominator := by
    dsimp only [denominator] at h28 h29 ⊢
    linarith only [h28,h29]
  have m15 : envelopePrefix F 1419024 ≤ envelopePrefix F 1402640+(27560578666:ℝ)/denominator := by
    dsimp only [denominator] at h30 h31 ⊢
    linarith only [h30,h31]
  have m16 : envelopePrefix F 1189648 ≤ envelopePrefix F 1156880+(67829192386:ℝ)/denominator := by
    dsimp only [denominator] at m0 m1 ⊢
    linarith only [m0,m1]
  have m17 : envelopePrefix F 1222416 ≤ envelopePrefix F 1189648+(64193383976:ℝ)/denominator := by
    dsimp only [denominator] at m2 m3 ⊢
    linarith only [m2,m3]
  have m18 : envelopePrefix F 1255184 ≤ envelopePrefix F 1222416+(63103040800:ℝ)/denominator := by
    dsimp only [denominator] at m4 m5 ⊢
    linarith only [m4,m5]
  have m19 : envelopePrefix F 1287952 ≤ envelopePrefix F 1255184+(62630712645:ℝ)/denominator := by
    dsimp only [denominator] at m6 m7 ⊢
    linarith only [m6,m7]
  have m20 : envelopePrefix F 1320720 ≤ envelopePrefix F 1287952+(60060872426:ℝ)/denominator := by
    dsimp only [denominator] at m8 m9 ⊢
    linarith only [m8,m9]
  have m21 : envelopePrefix F 1353488 ≤ envelopePrefix F 1320720+(59726927074:ℝ)/denominator := by
    dsimp only [denominator] at m10 m11 ⊢
    linarith only [m10,m11]
  have m22 : envelopePrefix F 1386256 ≤ envelopePrefix F 1353488+(58695987373:ℝ)/denominator := by
    dsimp only [denominator] at m12 m13 ⊢
    linarith only [m12,m13]
  have m23 : envelopePrefix F 1419024 ≤ envelopePrefix F 1386256+(56755115506:ℝ)/denominator := by
    dsimp only [denominator] at m14 m15 ⊢
    linarith only [m14,m15]
  have m24 : envelopePrefix F 1222416 ≤ envelopePrefix F 1156880+(132022576362:ℝ)/denominator := by
    dsimp only [denominator] at m16 m17 ⊢
    linarith only [m16,m17]
  have m25 : envelopePrefix F 1287952 ≤ envelopePrefix F 1222416+(125733753445:ℝ)/denominator := by
    dsimp only [denominator] at m18 m19 ⊢
    linarith only [m18,m19]
  have m26 : envelopePrefix F 1353488 ≤ envelopePrefix F 1287952+(119787799500:ℝ)/denominator := by
    dsimp only [denominator] at m20 m21 ⊢
    linarith only [m20,m21]
  have m27 : envelopePrefix F 1419024 ≤ envelopePrefix F 1353488+(115451102879:ℝ)/denominator := by
    dsimp only [denominator] at m22 m23 ⊢
    linarith only [m22,m23]
  have m28 : envelopePrefix F 1287952 ≤ envelopePrefix F 1156880+(257756329807:ℝ)/denominator := by
    dsimp only [denominator] at m24 m25 ⊢
    linarith only [m24,m25]
  have m29 : envelopePrefix F 1419024 ≤ envelopePrefix F 1287952+(235238902379:ℝ)/denominator := by
    dsimp only [denominator] at m26 m27 ⊢
    linarith only [m26,m27]
  have m30 : envelopePrefix F 1419024 ≤ envelopePrefix F 1156880+(492995232186:ℝ)/denominator := by
    dsimp only [denominator] at m28 m29 ⊢
    linarith only [m28,m29]
  exact m30

#print axioms GRHQuarterGroup05_bound
end ChenEffective.H10Band
end
