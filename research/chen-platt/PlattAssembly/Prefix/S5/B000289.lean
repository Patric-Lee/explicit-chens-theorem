import PlattAssemblyKernel
import PlattCertificates.Count131072.C049248
import PlattCertificates.Count131072.C049249
import PlattCertificates.Count131072.C049250
import PlattCertificates.Count131072.C049251
import PlattCertificates.Count131072.C049252
import PlattCertificates.Count131072.C049253
import PlattCertificates.Count131072.C049254
import PlattCertificates.Count131072.C049255
import PlattCertificates.Count131072.C049256
import PlattCertificates.Count131072.C049257
import PlattCertificates.Count131072.C049258
import PlattCertificates.Count131072.C049259
import PlattCertificates.Count131072.C049260
import PlattCertificates.Count131072.C049261
import PlattCertificates.Count131072.C049262
import PlattCertificates.Count131072.C049263
import PlattCertificates.Count131072.C049264
import PlattCertificates.Count131072.C049265
import PlattCertificates.Count131072.C049266
import PlattCertificates.Count131072.C049267
import PlattCertificates.Count131072.C049268
import PlattCertificates.Count131072.C049269
import PlattCertificates.Count131072.C049270
import PlattCertificates.Count131072.C049271
import PlattCertificates.Count131072.C049272
import PlattCertificates.Count131072.C049273
import PlattCertificates.Count131072.C049274
import PlattCertificates.Count131072.C049275
import PlattCertificates.Count131072.C049276
import PlattCertificates.Count131072.C049277
import PlattCertificates.Count131072.C049278
import PlattCertificates.Count131072.C049279
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000289
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts49248 : List PrefixCut := [⟨64,253539698,253539840⟩]
theorem checked49248 : checkPrefixCuts (2^48) 6458966017 10 Manual.Count131072.C049248.packed 64 cuts49248 = true := by
 decide +kernel
def cuts49249 : List PrefixCut := [⟨2,8584875,8584879⟩,
⟨64,256759307,256759450⟩]
theorem checked49249 : checkPrefixCuts (2^48) 6459097089 10 Manual.Count131072.C049249.packed 64 cuts49249 = true := by
 decide +kernel
def pointBounds49249 : List (Nat × Nat × Nat) := [(6459101184,111468404293387,111468791308079)]
theorem point_links_checked49249 : (cuts49249.take 1).map (fun c => (6459097089-1+2*2^10*c.k,111468395708512+c.lower,111468782723200+c.upper)) = pointBounds49249 := by
 decide +kernel
def cuts49250 : List PrefixCut := [⟨37,143716669,143716748⟩,
⟨64,248648818,248648959⟩]
theorem checked49250 : checkPrefixCuts (2^48) 6459228161 10 Manual.Count131072.C049250.packed 64 cuts49250 = true := by
 decide +kernel
def pointBounds49250 : List (Nat × Nat × Nat) := [(6459303936,111468796184488,111469183199398)]
theorem point_links_checked49250 : (cuts49250.take 1).map (fun c => (6459228161-1+2*2^10*c.k,111468652467819+c.lower,111469039482650+c.upper)) = pointBounds49250 := by
 decide +kernel
def cuts49251 : List PrefixCut := [⟨64,253829294,253829440⟩]
theorem checked49251 : checkPrefixCuts (2^48) 6459359233 10 Manual.Count131072.C049251.packed 64 cuts49251 = true := by
 decide +kernel
def cuts49252 : List PrefixCut := [⟨8,30851346,30851363⟩,
⟨64,249118046,249118189⟩]
theorem checked49252 : checkPrefixCuts (2^48) 6459490305 10 Manual.Count131072.C049252.packed 64 cuts49252 = true := by
 decide +kernel
def pointBounds49252 : List (Nat × Nat × Nat) := [(6459506688,111469185797277,111469572812412)]
theorem point_links_checked49252 : (cuts49252.take 1).map (fun c => (6459490305-1+2*2^10*c.k,111469154945931+c.lower,111469541961049+c.upper)) = pointBounds49252 := by
 decide +kernel
def cuts49253 : List PrefixCut := [⟨43,172858936,172859031⟩,
⟨64,254821215,254821353⟩]
theorem checked49253 : checkPrefixCuts (2^48) 6459621377 10 Manual.Count131072.C049253.packed 64 cuts49253 = true := by
 decide +kernel
def pointBounds49253 : List (Nat × Nat × Nat) := [(6459709440,111469576922913,111469963938269)]
theorem point_links_checked49253 : (cuts49253.take 1).map (fun c => (6459621377-1+2*2^10*c.k,111469404063977+c.lower,111469791079238+c.upper)) = pointBounds49253 := by
 decide +kernel
def cuts49254 : List PrefixCut := [⟨64,254598174,254598321⟩]
theorem checked49254 : checkPrefixCuts (2^48) 6459752449 10 Manual.Count131072.C049254.packed 64 cuts49254 = true := by
 decide +kernel
def cuts49255 : List PrefixCut := [⟨14,57472334,57472366⟩,
⟨64,254854435,254854578⟩]
theorem checked49255 : checkPrefixCuts (2^48) 6459883521 10 Manual.Count131072.C049255.packed 64 cuts49255 = true := by
 decide +kernel
def pointBounds49255 : List (Nat × Nat × Nat) := [(6459912192,111469970955700,111470357971278)]
theorem point_links_checked49255 : (cuts49255.take 1).map (fun c => (6459883521-1+2*2^10*c.k,111469913483366+c.lower,111470300498912+c.upper)) = pointBounds49255 := by
 decide +kernel
def cuts49256 : List PrefixCut := [⟨49,188577578,188577689⟩,
⟨64,247093550,247093695⟩]
theorem checked49256 : checkPrefixCuts (2^48) 6460014593 10 Manual.Count131072.C049256.packed 64 cuts49256 = true := by
 decide +kernel
def pointBounds49256 : List (Nat × Nat × Nat) := [(6460114944,111470356915379,111470743931179)]
theorem point_links_checked49256 : (cuts49256.take 1).map (fun c => (6460014593-1+2*2^10*c.k,111470168337801+c.lower,111470555353490+c.upper)) = pointBounds49256 := by
 decide +kernel
def cuts49257 : List PrefixCut := [⟨64,253754819,253754963⟩]
theorem checked49257 : checkPrefixCuts (2^48) 6460145665 10 Manual.Count131072.C049257.packed 64 cuts49257 = true := by
 decide +kernel
def cuts49258 : List PrefixCut := [⟨20,80038018,80038062⟩,
⟨64,253226858,253227001⟩]
theorem checked49258 : checkPrefixCuts (2^48) 6460276737 10 Manual.Count131072.C049258.packed 64 cuts49258 = true := by
 decide +kernel
def pointBounds49258 : List (Nat × Nat × Nat) := [(6460317696,111470749224188,111471136240210)]
theorem point_links_checked49258 : (cuts49258.take 1).map (fun c => (6460276737-1+2*2^10*c.k,111470669186170+c.lower,111471056202148+c.upper)) = pointBounds49258 := by
 decide +kernel
def cuts49259 : List PrefixCut := [⟨55,216493536,216493659⟩,
⟨64,251478957,251479098⟩]
theorem checked49259 : checkPrefixCuts (2^48) 6460407809 10 Manual.Count131072.C049259.packed 64 cuts49259 = true := by
 decide +kernel
def pointBounds49259 : List (Nat × Nat × Nat) := [(6460520448,111471138906564,111471525922808)]
theorem point_links_checked49259 : (cuts49259.take 1).map (fun c => (6460407809-1+2*2^10*c.k,111470922413028+c.lower,111471309429149+c.upper)) = pointBounds49259 := by
 decide +kernel
def cuts49260 : List PrefixCut := [⟨64,255743518,255743665⟩]
theorem checked49260 : checkPrefixCuts (2^48) 6460538881 10 Manual.Count131072.C049260.packed 64 cuts49260 = true := by
 decide +kernel
def cuts49261 : List PrefixCut := [⟨26,102993017,102993075⟩,
⟨64,252122255,252122396⟩]
theorem checked49261 : checkPrefixCuts (2^48) 6460669953 10 Manual.Count131072.C049261.packed 64 cuts49261 = true := by
 decide +kernel
def pointBounds49261 : List (Nat × Nat × Nat) := [(6460723200,111471532628520,111471919644987)]
theorem point_links_checked49261 : (cuts49261.take 1).map (fun c => (6460669953-1+2*2^10*c.k,111471429635503+c.lower,111471816651912+c.upper)) = pointBounds49261 := by
 decide +kernel
def cuts49262 : List PrefixCut := [⟨61,243099089,243099228⟩,
⟨64,255428182,255428328⟩]
theorem checked49262 : checkPrefixCuts (2^48) 6460801025 10 Manual.Count131072.C049262.packed 64 cuts49262 = true := by
 decide +kernel
def pointBounds49262 : List (Nat × Nat × Nat) := [(6460925952,111471924856847,111472311873536)]
theorem point_links_checked49262 : (cuts49262.take 1).map (fun c => (6460801025-1+2*2^10*c.k,111471681757758+c.lower,111472068774308+c.upper)) = pointBounds49262 := by
 decide +kernel
def cuts49263 : List PrefixCut := [⟨64,252809072,252809213⟩]
theorem checked49263 : checkPrefixCuts (2^48) 6460932097 10 Manual.Count131072.C049263.packed 64 cuts49263 = true := by
 decide +kernel
def cuts49264 : List PrefixCut := [⟨32,129168962,129169035⟩,
⟨64,254154455,254154599⟩]
theorem checked49264 : checkPrefixCuts (2^48) 6461063169 10 Manual.Count131072.C049264.packed 64 cuts49264 = true := by
 decide +kernel
def pointBounds49264 : List (Nat × Nat × Nat) := [(6461128704,111472319163974,111472706180884)]
theorem point_links_checked49264 : (cuts49264.take 1).map (fun c => (6461063169-1+2*2^10*c.k,111472189995012+c.lower,111472577011849+c.upper)) = pointBounds49264 := by
 decide +kernel
def cuts49265 : List PrefixCut := [⟨64,253539398,253539543⟩]
theorem checked49265 : checkPrefixCuts (2^48) 6461194241 10 Manual.Count131072.C049265.packed 64 cuts49265 = true := by
 decide +kernel
def cuts49266 : List PrefixCut := [⟨3,12110516,12110523⟩,
⟨64,256017328,256017468⟩]
theorem checked49266 : checkPrefixCuts (2^48) 6461325313 10 Manual.Count131072.C049266.packed 64 cuts49266 = true := by
 decide +kernel
def pointBounds49266 : List (Nat × Nat × Nat) := [(6461331456,111472709799381,111473096816514)]
theorem point_links_checked49266 : (cuts49266.take 1).map (fun c => (6461325313-1+2*2^10*c.k,111472697688865+c.lower,111473084705991+c.upper)) = pointBounds49266 := by
 decide +kernel
def cuts49267 : List PrefixCut := [⟨38,150724115,150724199⟩,
⟨64,252396520,252396663⟩]
theorem checked49267 : checkPrefixCuts (2^48) 6461456385 10 Manual.Count131072.C049267.packed 64 cuts49267 = true := by
 decide +kernel
def pointBounds49267 : List (Nat × Nat × Nat) := [(6461534208,111473104430308,111473491447658)]
theorem point_links_checked49267 : (cuts49267.take 1).map (fun c => (6461456385-1+2*2^10*c.k,111472953706193+c.lower,111473340723459+c.upper)) = pointBounds49267 := by
 decide +kernel
def cuts49268 : List PrefixCut := [⟨64,250997436,250997577⟩]
theorem checked49268 : checkPrefixCuts (2^48) 6461587457 10 Manual.Count131072.C049268.packed 64 cuts49268 = true := by
 decide +kernel
def cuts49269 : List PrefixCut := [⟨9,36242185,36242205⟩,
⟨64,253605966,253606109⟩]
theorem checked49269 : checkPrefixCuts (2^48) 6461718529 10 Manual.Count131072.C049269.packed 64 cuts49269 = true := by
 decide +kernel
def pointBounds49269 : List (Nat × Nat × Nat) := [(6461736960,111473493342334,111473880359904)]
theorem point_links_checked49269 : (cuts49269.take 1).map (fun c => (6461718529-1+2*2^10*c.k,111473457100149+c.lower,111473844117699+c.upper)) = pointBounds49269 := by
 decide +kernel
def cuts49270 : List PrefixCut := [⟨44,175151502,175151601⟩,
⟨64,254864014,254864158⟩]
theorem checked49270 : checkPrefixCuts (2^48) 6461849601 10 Manual.Count131072.C049270.packed 64 cuts49270 = true := by
 decide +kernel
def pointBounds49270 : List (Nat × Nat × Nat) := [(6461939712,111473885857617,111474272875409)]
theorem point_links_checked49270 : (cuts49270.take 1).map (fun c => (6461849601-1+2*2^10*c.k,111473710706115+c.lower,111474097723808+c.upper)) = pointBounds49270 := by
 decide +kernel
def cuts49271 : List PrefixCut := [⟨64,251809779,251809929⟩]
theorem checked49271 : checkPrefixCuts (2^48) 6461980673 10 Manual.Count131072.C049271.packed 64 cuts49271 = true := by
 decide +kernel
def cuts49272 : List PrefixCut := [⟨15,59761058,59761094⟩,
⟨64,254461672,254461818⟩]
theorem checked49272 : checkPrefixCuts (2^48) 6462111745 10 Manual.Count131072.C049272.packed 64 cuts49272 = true := by
 decide +kernel
def pointBounds49272 : List (Nat × Nat × Nat) := [(6462142464,111474277140966,111474664158989)]
theorem point_links_checked49272 : (cuts49272.take 1).map (fun c => (6462111745-1+2*2^10*c.k,111474217379908+c.lower,111474604397895+c.upper)) = pointBounds49272 := by
 decide +kernel
def cuts49273 : List PrefixCut := [⟨50,196396246,196396361⟩,
⟨64,251538210,251538356⟩]
theorem checked49273 : checkPrefixCuts (2^48) 6462242817 10 Manual.Count131072.C049273.packed 64 cuts49273 = true := by
 decide +kernel
def pointBounds49273 : List (Nat × Nat × Nat) := [(6462345216,111474668237826,111475055256074)]
theorem point_links_checked49273 : (cuts49273.take 1).map (fun c => (6462242817-1+2*2^10*c.k,111474471841580+c.lower,111474858859713+c.upper)) = pointBounds49273 := by
 decide +kernel
def cuts49274 : List PrefixCut := [⟨64,258806879,258807033⟩]
theorem checked49274 : checkPrefixCuts (2^48) 6462373889 10 Manual.Count131072.C049274.packed 64 cuts49274 = true := by
 decide +kernel
def cuts49275 : List PrefixCut := [⟨21,81839716,81839764⟩,
⟨64,251571573,251571717⟩]
theorem checked49275 : checkPrefixCuts (2^48) 6462504961 10 Manual.Count131072.C049275.packed 64 cuts49275 = true := by
 decide +kernel
def pointBounds49275 : List (Nat × Nat × Nat) := [(6462547968,111475064026385,111475451044866)]
theorem point_links_checked49275 : (cuts49275.take 1).map (fun c => (6462504961-1+2*2^10*c.k,111474982186669+c.lower,111475369205102+c.upper)) = pointBounds49275 := by
 decide +kernel
def cuts49276 : List PrefixCut := [⟨56,218073922,218074045⟩,
⟨64,248648385,248648524⟩]
theorem checked49276 : checkPrefixCuts (2^48) 6462636033 10 Manual.Count131072.C049276.packed 64 cuts49276 = true := by
 decide +kernel
def pointBounds49276 : List (Nat × Nat × Nat) := [(6462750720,111475451832164,111475838850864)]
theorem point_links_checked49276 : (cuts49276.take 1).map (fun c => (6462636033-1+2*2^10*c.k,111475233758242+c.lower,111475620776819+c.upper)) = pointBounds49276 := by
 decide +kernel
def cuts49277 : List PrefixCut := [⟨64,251474255,251474402⟩]
theorem checked49277 : checkPrefixCuts (2^48) 6462767105 10 Manual.Count131072.C049277.packed 64 cuts49277 = true := by
 decide +kernel
def cuts49278 : List PrefixCut := [⟨27,105439970,105440029⟩,
⟨64,252296631,252296773⟩]
theorem checked49278 : checkPrefixCuts (2^48) 6462898177 10 Manual.Count131072.C049278.packed 64 cuts49278 = true := by
 decide +kernel
def pointBounds49278 : List (Nat × Nat × Nat) := [(6462953472,111475839320852,111476226339774)]
theorem point_links_checked49278 : (cuts49278.take 1).map (fun c => (6462898177-1+2*2^10*c.k,111475733880882+c.lower,111476120899745+c.upper)) = pointBounds49278 := by
 decide +kernel
def cuts49279 : List PrefixCut := [⟨62,242274852,242274992⟩,
⟨64,249547815,249547959⟩]
theorem checked49279 : checkPrefixCuts (2^48) 6463029249 10 Manual.Count131072.C049279.packed 64 cuts49279 = true := by
 decide +kernel
def pointBounds49279 : List (Nat × Nat × Nat) := [(6463156224,111476228452365,111476615471510)]
theorem point_links_checked49279 : (cuts49279.take 1).map (fun c => (6463029249-1+2*2^10*c.k,111475986177513+c.lower,111476373196518+c.upper)) = pointBounds49279 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000289
