import PlattAssemblyKernel
import PlattCertificates.Count131072.C072208
import PlattCertificates.Count131072.C072209
import PlattCertificates.Count131072.C072210
import PlattCertificates.Count131072.C072211
import PlattCertificates.Count131072.C072212
import PlattCertificates.Count131072.C072213
import PlattCertificates.Count131072.C072214
import PlattCertificates.Count131072.C072215
import PlattCertificates.Count131072.C072216
import PlattCertificates.Count131072.C072217
import PlattCertificates.Count131072.C072218
import PlattCertificates.Count131072.C072219
import PlattCertificates.Count131072.C072220
import PlattCertificates.Count131072.C072221
import PlattCertificates.Count131072.C072222
import PlattCertificates.Count131072.C072223
import PlattCertificates.Count131072.C072224
import PlattCertificates.Count131072.C072225
import PlattCertificates.Count131072.C072226
import PlattCertificates.Count131072.C072227
import PlattCertificates.Count131072.C072228
import PlattCertificates.Count131072.C072229
import PlattCertificates.Count131072.C072230
import PlattCertificates.Count131072.C072231
import PlattCertificates.Count131072.C072232
import PlattCertificates.Count131072.C072233
import PlattCertificates.Count131072.C072234
import PlattCertificates.Count131072.C072235
import PlattCertificates.Count131072.C072236
import PlattCertificates.Count131072.C072237
import PlattCertificates.Count131072.C072238
import PlattCertificates.Count131072.C072239
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000069
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72208 : List PrefixCut := [⟨6,16053048,16053058⟩,
⟨64,168437051,168437150⟩]
theorem checked72208 : checkPrefixCuts (2^48) 9468379137 10 Manual.Count131072.C072208.packed 64 cuts72208 = true := by
 decide +kernel
def pointBounds72208 : List (Nat × Nat × Nat) := [(9468391424,116194415476794,116194805206972)]
theorem point_links_checked72208 : (cuts72208.take 1).map (fun c => (9468379137-1+2*2^10*c.k,116194399423746+c.lower,116194789153914+c.upper)) = pointBounds72208 := by
 decide +kernel
def cuts72209 : List PrefixCut := [⟨64,171110161,171110259⟩]
theorem checked72209 : checkPrefixCuts (2^48) 9468510209 10 Manual.Count131072.C072209.packed 64 cuts72209 = true := by
 decide +kernel
def cuts72210 : List PrefixCut := [⟨23,60494422,60494458⟩,
⟨64,169145813,169145909⟩]
theorem checked72210 : checkPrefixCuts (2^48) 9468641281 10 Manual.Count131072.C072210.packed 64 cuts72210 = true := by
 decide +kernel
def pointBounds72210 : List (Nat × Nat × Nat) := [(9468688384,116194799465380,116195189195781)]
theorem point_links_checked72210 : (cuts72210.take 1).map (fun c => (9468641281-1+2*2^10*c.k,116194738970958+c.lower,116195128701323+c.upper)) = pointBounds72210 := by
 decide +kernel
def cuts72211 : List PrefixCut := [⟨64,169024561,169024659⟩]
theorem checked72211 : checkPrefixCuts (2^48) 9468772353 10 Manual.Count131072.C072211.packed 64 cuts72211 = true := by
 decide +kernel
def cuts72212 : List PrefixCut := [⟨40,102495628,102495695⟩,
⟨64,166763035,166763141⟩]
theorem checked72212 : checkPrefixCuts (2^48) 9468903425 10 Manual.Count131072.C072212.packed 64 cuts72212 = true := by
 decide +kernel
def pointBounds72212 : List (Nat × Nat × Nat) := [(9468985344,116195179636960,116195569367586)]
theorem point_links_checked72212 : (cuts72212.take 1).map (fun c => (9468903425-1+2*2^10*c.k,116195077141332+c.lower,116195466871891+c.upper)) = pointBounds72212 := by
 decide +kernel
def cuts72213 : List PrefixCut := [⟨64,169227976,169228068⟩]
theorem checked72213 : checkPrefixCuts (2^48) 9469034497 10 Manual.Count131072.C072213.packed 64 cuts72213 = true := by
 decide +kernel
def cuts72214 : List PrefixCut := [⟨57,150171876,150171973⟩,
⟨64,168958094,168958201⟩]
theorem checked72214 : checkPrefixCuts (2^48) 9469165569 10 Manual.Count131072.C072214.packed 64 cuts72214 = true := by
 decide +kernel
def pointBounds72214 : List (Nat × Nat × Nat) := [(9469282304,116195563304219,116195953035073)]
theorem point_links_checked72214 : (cuts72214.take 1).map (fun c => (9469165569-1+2*2^10*c.k,116195413132343+c.lower,116195802863100+c.upper)) = pointBounds72214 := by
 decide +kernel
def cuts72215 : List PrefixCut := [⟨64,168153192,168153292⟩]
theorem checked72215 : checkPrefixCuts (2^48) 9469296641 10 Manual.Count131072.C072215.packed 64 cuts72215 = true := by
 decide +kernel
def cuts72216 : List PrefixCut := [⟨64,170617999,170618100⟩]
theorem checked72216 : checkPrefixCuts (2^48) 9469427713 10 Manual.Count131072.C072216.packed 64 cuts72216 = true := by
 decide +kernel
def cuts72217 : List PrefixCut := [⟨10,25711390,25711405⟩,
⟨64,165562551,165562641⟩]
theorem checked72217 : checkPrefixCuts (2^48) 9469558785 10 Manual.Count131072.C072217.packed 64 cuts72217 = true := by
 decide +kernel
def pointBounds72217 : List (Nat × Nat × Nat) := [(9469579264,116195946573018,116196336304098)]
theorem point_links_checked72217 : (cuts72217.take 1).map (fun c => (9469558785-1+2*2^10*c.k,116195920861628+c.lower,116196310592693+c.upper)) = pointBounds72217 := by
 decide +kernel
def cuts72218 : List PrefixCut := [⟨64,173674790,173674895⟩]
theorem checked72218 : checkPrefixCuts (2^48) 9469689857 10 Manual.Count131072.C072218.packed 64 cuts72218 = true := by
 decide +kernel
def cuts72219 : List PrefixCut := [⟨27,72138382,72138424⟩,
⟨64,171770099,171770202⟩]
theorem checked72219 : checkPrefixCuts (2^48) 9469820929 10 Manual.Count131072.C072219.packed 64 cuts72219 = true := by
 decide +kernel
def pointBounds72219 : List (Nat × Nat × Nat) := [(9469876224,116196332237351,116196721968653)]
theorem point_links_checked72219 : (cuts72219.take 1).map (fun c => (9469820929-1+2*2^10*c.k,116196260098969+c.lower,116196649830229+c.upper)) = pointBounds72219 := by
 decide +kernel
def cuts72220 : List PrefixCut := [⟨64,167487645,167487752⟩]
theorem checked72220 : checkPrefixCuts (2^48) 9469952001 10 Manual.Count131072.C072220.packed 64 cuts72220 = true := by
 decide +kernel
def cuts72221 : List PrefixCut := [⟨44,117135960,117136032⟩,
⟨64,169595628,169595731⟩]
theorem checked72221 : checkPrefixCuts (2^48) 9470083073 10 Manual.Count131072.C072221.packed 64 cuts72221 = true := by
 decide +kernel
def pointBounds72221 : List (Nat × Nat × Nat) := [(9470173184,116196716492673,116197106224215)]
theorem point_links_checked72221 : (cuts72221.take 1).map (fun c => (9470083073-1+2*2^10*c.k,116196599356713+c.lower,116196989088183+c.upper)) = pointBounds72221 := by
 decide +kernel
def cuts72222 : List PrefixCut := [⟨64,169266330,169266429⟩]
theorem checked72222 : checkPrefixCuts (2^48) 9470214145 10 Manual.Count131072.C072222.packed 64 cuts72222 = true := by
 decide +kernel
def cuts72223 : List PrefixCut := [⟨61,163141427,163141527⟩,
⟨64,171195902,171196008⟩]
theorem checked72223 : checkPrefixCuts (2^48) 9470345217 10 Manual.Count131072.C072223.packed 64 cuts72223 = true := by
 decide +kernel
def pointBounds72223 : List (Nat × Nat × Nat) := [(9470470144,116197101360098,116197491091870)]
theorem point_links_checked72223 : (cuts72223.take 1).map (fun c => (9470345217-1+2*2^10*c.k,116196938218671+c.lower,116197327950343+c.upper)) = pointBounds72223 := by
 decide +kernel
def cuts72224 : List PrefixCut := [⟨64,168756394,168756500⟩]
theorem checked72224 : checkPrefixCuts (2^48) 9470476289 10 Manual.Count131072.C072224.packed 64 cuts72224 = true := by
 decide +kernel
def cuts72225 : List PrefixCut := [⟨64,167535513,167535606⟩]
theorem checked72225 : checkPrefixCuts (2^48) 9470607361 10 Manual.Count131072.C072225.packed 64 cuts72225 = true := by
 decide +kernel
def cuts72226 : List PrefixCut := [⟨14,37299145,37299166⟩,
⟨64,170534932,170535032⟩]
theorem checked72226 : checkPrefixCuts (2^48) 9470738433 10 Manual.Count131072.C072226.packed 64 cuts72226 = true := by
 decide +kernel
def pointBounds72226 : List (Nat × Nat × Nat) := [(9470767104,116197483005625,116197872737623)]
theorem point_links_checked72226 : (cuts72226.take 1).map (fun c => (9470738433-1+2*2^10*c.k,116197445706480+c.lower,116197835438457+c.upper)) = pointBounds72226 := by
 decide +kernel
def cuts72227 : List PrefixCut := [⟨64,171988849,171988951⟩]
theorem checked72227 : checkPrefixCuts (2^48) 9470869505 10 Manual.Count131072.C072227.packed 64 cuts72227 = true := by
 decide +kernel
def cuts72228 : List PrefixCut := [⟨31,83393081,83393132⟩,
⟨64,171392084,171392188⟩]
theorem checked72228 : checkPrefixCuts (2^48) 9471000577 10 Manual.Count131072.C072228.packed 64 cuts72228 = true := by
 decide +kernel
def pointBounds72228 : List (Nat × Nat × Nat) := [(9471064064,116197871623342,116198261355572)]
theorem point_links_checked72228 : (cuts72228.take 1).map (fun c => (9471000577-1+2*2^10*c.k,116197788230261+c.lower,116198177962440+c.upper)) = pointBounds72228 := by
 decide +kernel
def cuts72229 : List PrefixCut := [⟨64,170973629,170973733⟩]
theorem checked72229 : checkPrefixCuts (2^48) 9471131649 10 Manual.Count131072.C072229.packed 64 cuts72229 = true := by
 decide +kernel
def cuts72230 : List PrefixCut := [⟨48,126066636,126066711⟩,
⟨64,168831521,168831623⟩]
theorem checked72230 : checkPrefixCuts (2^48) 9471262721 10 Manual.Count131072.C072230.packed 64 cuts72230 = true := by
 decide +kernel
def pointBounds72230 : List (Nat × Nat × Nat) := [(9471361024,116198256662610,116198646395072)]
theorem point_links_checked72230 : (cuts72230.take 1).map (fun c => (9471262721-1+2*2^10*c.k,116198130595974+c.lower,116198520328361+c.upper)) = pointBounds72230 := by
 decide +kernel
def cuts72231 : List PrefixCut := [⟨64,170642007,170642109⟩]
theorem checked72231 : checkPrefixCuts (2^48) 9471393793 10 Manual.Count131072.C072231.packed 64 cuts72231 = true := by
 decide +kernel
def cuts72232 : List PrefixCut := [⟨64,167073515,167073617⟩]
theorem checked72232 : checkPrefixCuts (2^48) 9471524865 10 Manual.Count131072.C072232.packed 64 cuts72232 = true := by
 decide +kernel
def cuts72233 : List PrefixCut := [⟨1,2971760,2971761⟩,
⟨64,169894348,169894445⟩]
theorem checked72233 : checkPrefixCuts (2^48) 9471655937 10 Manual.Count131072.C072233.packed 64 cuts72233 = true := by
 decide +kernel
def pointBounds72233 : List (Nat × Nat × Nat) := [(9471657984,116198640114777,116199029847471)]
theorem point_links_checked72233 : (cuts72233.take 1).map (fun c => (9471655937-1+2*2^10*c.k,116198637143017+c.lower,116199026875710+c.upper)) = pointBounds72233 := by
 decide +kernel
def cuts72234 : List PrefixCut := [⟨64,170634921,170635016⟩]
theorem checked72234 : checkPrefixCuts (2^48) 9471787009 10 Manual.Count131072.C072234.packed 64 cuts72234 = true := by
 decide +kernel
def cuts72235 : List PrefixCut := [⟨18,46744402,46744430⟩,
⟨64,167066570,167066667⟩]
theorem checked72235 : checkPrefixCuts (2^48) 9471918081 10 Manual.Count131072.C072235.packed 64 cuts72235 = true := by
 decide +kernel
def pointBounds72235 : List (Nat × Nat × Nat) := [(9471954944,116199024416688,116199414149601)]
theorem point_links_checked72235 : (cuts72235.take 1).map (fun c => (9471918081-1+2*2^10*c.k,116198977672286+c.lower,116199367405171+c.upper)) = pointBounds72235 := by
 decide +kernel
def cuts72236 : List PrefixCut := [⟨64,169352403,169352502⟩]
theorem checked72236 : checkPrefixCuts (2^48) 9472049153 10 Manual.Count131072.C072236.packed 64 cuts72236 = true := by
 decide +kernel
def cuts72237 : List PrefixCut := [⟨35,92535140,92535197⟩,
⟨64,170479259,170479366⟩]
theorem checked72237 : checkPrefixCuts (2^48) 9472180225 10 Manual.Count131072.C072237.packed 64 cuts72237 = true := by
 decide +kernel
def pointBounds72237 : List (Nat × Nat × Nat) := [(9472251904,116199406626399,116199796359537)]
theorem point_links_checked72237 : (cuts72237.take 1).map (fun c => (9472180225-1+2*2^10*c.k,116199314091259+c.lower,116199703824340+c.upper)) = pointBounds72237 := by
 decide +kernel
def cuts72238 : List PrefixCut := [⟨64,166227615,166227711⟩]
theorem checked72238 : checkPrefixCuts (2^48) 9472311297 10 Manual.Count131072.C072238.packed 64 cuts72238 = true := by
 decide +kernel
def cuts72239 : List PrefixCut := [⟨52,136272842,136272922⟩,
⟨64,168097352,168097449⟩]
theorem checked72239 : checkPrefixCuts (2^48) 9472442369 10 Manual.Count131072.C072239.packed 64 cuts72239 = true := by
 decide +kernel
def pointBounds72239 : List (Nat × Nat × Nat) := [(9472548864,116199787070975,116200176804339)]
theorem point_links_checked72239 : (cuts72239.take 1).map (fun c => (9472442369-1+2*2^10*c.k,116199650798133+c.lower,116200040531417+c.upper)) = pointBounds72239 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000069
