import PlattAssemblyKernel
import PlattCertificates.Count131072.C053264
import PlattCertificates.Count131072.C053265
import PlattCertificates.Count131072.C053266
import PlattCertificates.Count131072.C053267
import PlattCertificates.Count131072.C053268
import PlattCertificates.Count131072.C053269
import PlattCertificates.Count131072.C053270
import PlattCertificates.Count131072.C053271
import PlattCertificates.Count131072.C053272
import PlattCertificates.Count131072.C053273
import PlattCertificates.Count131072.C053274
import PlattCertificates.Count131072.C053275
import PlattCertificates.Count131072.C053276
import PlattCertificates.Count131072.C053277
import PlattCertificates.Count131072.C053278
import PlattCertificates.Count131072.C053279
import PlattCertificates.Count131072.C053280
import PlattCertificates.Count131072.C053281
import PlattCertificates.Count131072.C053282
import PlattCertificates.Count131072.C053283
import PlattCertificates.Count131072.C053284
import PlattCertificates.Count131072.C053285
import PlattCertificates.Count131072.C053286
import PlattCertificates.Count131072.C053287
import PlattCertificates.Count131072.C053288
import PlattCertificates.Count131072.C053289
import PlattCertificates.Count131072.C053290
import PlattCertificates.Count131072.C053291
import PlattCertificates.Count131072.C053292
import PlattCertificates.Count131072.C053293
import PlattCertificates.Count131072.C053294
import PlattCertificates.Count131072.C053295
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000102
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts53264 : List PrefixCut := [⟨64,233426887,233427020⟩]
theorem checked53264 : checkPrefixCuts (2^48) 6985351169 10 Manual.Count131072.C053264.packed 64 cuts53264 = true := by
 decide +kernel
def cuts53265 : List PrefixCut := [⟨8,28568604,28568620⟩,
⟨64,232536026,232536158⟩]
theorem checked53265 : checkPrefixCuts (2^48) 6985482241 10 Manual.Count131072.C053265.packed 64 cuts53265 = true := by
 decide +kernel
def pointBounds53265 : List (Nat × Nat × Nat) := [(6985498624,112442997617369,112443385186284)]
theorem point_links_checked53265 : (cuts53265.take 1).map (fun c => (6985482241-1+2*2^10*c.k,112442969048765+c.lower,112443356617664+c.upper)) = pointBounds53265 := by
 decide +kernel
def cuts53266 : List PrefixCut := [⟨51,185791991,185792097⟩,
⟨64,233498704,233498837⟩]
theorem checked53266 : checkPrefixCuts (2^48) 6985613313 10 Manual.Count131072.C053266.packed 64 cuts53266 = true := by
 decide +kernel
def pointBounds53266 : List (Nat × Nat × Nat) := [(6985717760,112443387376782,112443774945919)]
theorem point_links_checked53266 : (cuts53266.take 1).map (fun c => (6985613313-1+2*2^10*c.k,112443201584791+c.lower,112443589153822+c.upper)) = pointBounds53266 := by
 decide +kernel
def cuts53267 : List PrefixCut := [⟨64,229948617,229948746⟩]
theorem checked53267 : checkPrefixCuts (2^48) 6985744385 10 Manual.Count131072.C053267.packed 64 cuts53267 = true := by
 decide +kernel
def cuts53268 : List PrefixCut := [⟨30,108828217,108828279⟩,
⟨64,231596252,231596382⟩]
theorem checked53268 : checkPrefixCuts (2^48) 6985875457 10 Manual.Count131072.C053268.packed 64 cuts53268 = true := by
 decide +kernel
def pointBounds53268 : List (Nat × Nat × Nat) := [(6985936896,112443773860329,112444161429684)]
theorem point_links_checked53268 : (cuts53268.take 1).map (fun c => (6985875457-1+2*2^10*c.k,112443665032112+c.lower,112444052601405+c.upper)) = pointBounds53268 := by
 decide +kernel
def cuts53269 : List PrefixCut := [⟨64,236507383,236507517⟩]
theorem checked53269 : checkPrefixCuts (2^48) 6986006529 10 Manual.Count131072.C053269.packed 64 cuts53269 = true := by
 decide +kernel
def cuts53270 : List PrefixCut := [⟨9,32514383,32514401⟩,
⟨64,230056529,230056661⟩]
theorem checked53270 : checkPrefixCuts (2^48) 6986137601 10 Manual.Count131072.C053270.packed 64 cuts53270 = true := by
 decide +kernel
def pointBounds53270 : List (Nat × Nat × Nat) := [(6986156032,112444165650130,112444553219705)]
theorem point_links_checked53270 : (cuts53270.take 1).map (fun c => (6986137601-1+2*2^10*c.k,112444133135747+c.lower,112444520705304+c.upper)) = pointBounds53270 := by
 decide +kernel
def cuts53271 : List PrefixCut := [⟨52,190689849,190689957⟩,
⟨64,235128668,235128800⟩]
theorem checked53271 : checkPrefixCuts (2^48) 6986268673 10 Manual.Count131072.C053271.packed 64 cuts53271 = true := by
 decide +kernel
def pointBounds53271 : List (Nat × Nat × Nat) := [(6986375168,112444553882125,112444941451922)]
theorem point_links_checked53271 : (cuts53271.take 1).map (fun c => (6986268673-1+2*2^10*c.k,112444363192276+c.lower,112444750761965+c.upper)) = pointBounds53271 := by
 decide +kernel
def cuts53272 : List PrefixCut := [⟨64,236453780,236453914⟩]
theorem checked53272 : checkPrefixCuts (2^48) 6986399745 10 Manual.Count131072.C053272.packed 64 cuts53272 = true := by
 decide +kernel
def cuts53273 : List PrefixCut := [⟨31,112645349,112645411⟩,
⟨64,233709766,233709895⟩]
theorem checked53273 : checkPrefixCuts (2^48) 6986530817 10 Manual.Count131072.C053273.packed 64 cuts53273 = true := by
 decide +kernel
def pointBounds53273 : List (Nat × Nat × Nat) := [(6986594304,112444947420073,112445334990090)]
theorem point_links_checked53273 : (cuts53273.take 1).map (fun c => (6986530817-1+2*2^10*c.k,112444834774724+c.lower,112445222344679+c.upper)) = pointBounds53273 := by
 decide +kernel
def cuts53274 : List PrefixCut := [⟨64,232013336,232013468⟩]
theorem checked53274 : checkPrefixCuts (2^48) 6986661889 10 Manual.Count131072.C053274.packed 64 cuts53274 = true := by
 decide +kernel
def cuts53275 : List PrefixCut := [⟨10,37627730,37627751⟩,
⟨64,235675049,235675180⟩]
theorem checked53275 : checkPrefixCuts (2^48) 6986792961 10 Manual.Count131072.C053275.packed 64 cuts53275 = true := by
 decide +kernel
def pointBounds53275 : List (Nat × Nat × Nat) := [(6986813440,112445338125556,112445725695793)]
theorem point_links_checked53275 : (cuts53275.take 1).map (fun c => (6986792961-1+2*2^10*c.k,112445300497826+c.lower,112445688068042+c.upper)) = pointBounds53275 := by
 decide +kernel
def cuts53276 : List PrefixCut := [⟨53,193250203,193250310⟩,
⟨64,233253469,233253599⟩]
theorem checked53276 : checkPrefixCuts (2^48) 6986924033 10 Manual.Count131072.C053276.packed 64 cuts53276 = true := by
 decide +kernel
def pointBounds53276 : List (Nat × Nat × Nat) := [(6987032576,112445729423078,112446116993532)]
theorem point_links_checked53276 : (cuts53276.take 1).map (fun c => (6986924033-1+2*2^10*c.k,112445536172875+c.lower,112445923743222+c.upper)) = pointBounds53276 := by
 decide +kernel
def cuts53277 : List PrefixCut := [⟨64,234336800,234336934⟩]
theorem checked53277 : checkPrefixCuts (2^48) 6987055105 10 Manual.Count131072.C053277.packed 64 cuts53277 = true := by
 decide +kernel
def cuts53278 : List PrefixCut := [⟨32,115938077,115938143⟩,
⟨64,231069396,231069529⟩]
theorem checked53278 : checkPrefixCuts (2^48) 6987186177 10 Manual.Count131072.C053278.packed 64 cuts53278 = true := by
 decide +kernel
def pointBounds53278 : List (Nat × Nat × Nat) := [(6987251712,112446119701221,112446507271898)]
theorem point_links_checked53278 : (cuts53278.take 1).map (fun c => (6987186177-1+2*2^10*c.k,112446003763144+c.lower,112446391333755+c.upper)) = pointBounds53278 := by
 decide +kernel
def cuts53279 : List PrefixCut := [⟨64,231991580,231991714⟩]
theorem checked53279 : checkPrefixCuts (2^48) 6987317249 10 Manual.Count131072.C053279.packed 64 cuts53279 = true := by
 decide +kernel
def cuts53280 : List PrefixCut := [⟨11,39880038,39880060⟩,
⟨64,233034574,233034709⟩]
theorem checked53280 : checkPrefixCuts (2^48) 6987448321 10 Manual.Count131072.C053280.packed 64 cuts53280 = true := by
 decide +kernel
def pointBounds53280 : List (Nat × Nat × Nat) := [(6987470848,112446506704158,112446894275058)]
theorem point_links_checked53280 : (cuts53280.take 1).map (fun c => (6987448321-1+2*2^10*c.k,112446466824120+c.lower,112446854394998+c.upper)) = pointBounds53280 := by
 decide +kernel
def cuts53281 : List PrefixCut := [⟨54,198267294,198267408⟩,
⟨64,233473307,233473442⟩]
theorem checked53281 : checkPrefixCuts (2^48) 6987579393 10 Manual.Count131072.C053281.packed 64 cuts53281 = true := by
 decide +kernel
def pointBounds53281 : List (Nat × Nat × Nat) := [(6987689984,112446898125988,112447285697115)]
theorem point_links_checked53281 : (cuts53281.take 1).map (fun c => (6987579393-1+2*2^10*c.k,112446699858694+c.lower,112447087429707+c.upper)) = pointBounds53281 := by
 decide +kernel
def cuts53282 : List PrefixCut := [⟨64,231213184,231213315⟩]
theorem checked53282 : checkPrefixCuts (2^48) 6987710465 10 Manual.Count131072.C053282.packed 64 cuts53282 = true := by
 decide +kernel
def cuts53283 : List PrefixCut := [⟨33,120398327,120398397⟩,
⟨64,234028461,234028596⟩]
theorem checked53283 : checkPrefixCuts (2^48) 6987841537 10 Manual.Count131072.C053283.packed 64 cuts53283 = true := by
 decide +kernel
def pointBounds53283 : List (Nat × Nat × Nat) := [(6987909120,112447284943512,112447672514861)]
theorem point_links_checked53283 : (cuts53283.take 1).map (fun c => (6987841537-1+2*2^10*c.k,112447164545185+c.lower,112447552116464+c.upper)) = pointBounds53283 := by
 decide +kernel
def cuts53284 : List PrefixCut := [⟨64,235715795,235715924⟩]
theorem checked53284 : checkPrefixCuts (2^48) 6987972609 10 Manual.Count131072.C053284.packed 64 cuts53284 = true := by
 decide +kernel
def cuts53285 : List PrefixCut := [⟨12,44508386,44508411⟩,
⟨64,234865530,234865663⟩]
theorem checked53285 : checkPrefixCuts (2^48) 6988103681 10 Manual.Count131072.C053285.packed 64 cuts53285 = true := by
 decide +kernel
def pointBounds53285 : List (Nat × Nat × Nat) := [(6988128256,112447678797827,112448066369395)]
theorem point_links_checked53285 : (cuts53285.take 1).map (fun c => (6988103681-1+2*2^10*c.k,112447634289441+c.lower,112448021860984+c.upper)) = pointBounds53285 := by
 decide +kernel
def cuts53286 : List PrefixCut := [⟨55,196556983,196557095⟩,
⟨64,228497191,228497324⟩]
theorem checked53286 : checkPrefixCuts (2^48) 6988234753 10 Manual.Count131072.C053286.packed 64 cuts53286 = true := by
 decide +kernel
def pointBounds53286 : List (Nat × Nat × Nat) := [(6988347392,112448065711954,112448453283742)]
theorem point_links_checked53286 : (cuts53286.take 1).map (fun c => (6988234753-1+2*2^10*c.k,112447869154971+c.lower,112448256726647+c.upper)) = pointBounds53286 := by
 decide +kernel
def cuts53287 : List PrefixCut := [⟨64,235702548,235702683⟩]
theorem checked53287 : checkPrefixCuts (2^48) 6988365825 10 Manual.Count131072.C053287.packed 64 cuts53287 = true := by
 decide +kernel
def cuts53288 : List PrefixCut := [⟨34,123931363,123931431⟩,
⟨64,233039880,233040009⟩]
theorem checked53288 : checkPrefixCuts (2^48) 6988496897 10 Manual.Count131072.C053288.packed 64 cuts53288 = true := by
 decide +kernel
def pointBounds53288 : List (Nat × Nat × Nat) := [(6988566528,112448457286073,112448844858085)]
theorem point_links_checked53288 : (cuts53288.take 1).map (fun c => (6988496897-1+2*2^10*c.k,112448333354710+c.lower,112448720926654+c.upper)) = pointBounds53288 := by
 decide +kernel
def cuts53289 : List PrefixCut := [⟨64,234042401,234042532⟩]
theorem checked53289 : checkPrefixCuts (2^48) 6988627969 10 Manual.Count131072.C053289.packed 64 cuts53289 = true := by
 decide +kernel
def cuts53290 : List PrefixCut := [⟨13,45873562,45873588⟩,
⟨64,230131321,230131452⟩]
theorem checked53290 : checkPrefixCuts (2^48) 6988759041 10 Manual.Count131072.C053290.packed 64 cuts53290 = true := by
 decide +kernel
def pointBounds53290 : List (Nat × Nat × Nat) := [(6988785664,112448846310553,112449233882783)]
theorem point_links_checked53290 : (cuts53290.take 1).map (fun c => (6988759041-1+2*2^10*c.k,112448800436991+c.lower,112449188009195+c.upper)) = pointBounds53290 := by
 decide +kernel
def cuts53291 : List PrefixCut := [⟨56,202297754,202297874⟩,
⟨64,231375519,231375656⟩]
theorem checked53291 : checkPrefixCuts (2^48) 6988890113 10 Manual.Count131072.C053291.packed 64 cuts53291 = true := by
 decide +kernel
def pointBounds53291 : List (Nat × Nat × Nat) := [(6989004800,112449232866066,112449620438521)]
theorem point_links_checked53291 : (cuts53291.take 1).map (fun c => (6988890113-1+2*2^10*c.k,112449030568312+c.lower,112449418140647+c.upper)) = pointBounds53291 := by
 decide +kernel
def cuts53292 : List PrefixCut := [⟨64,234512510,234512638⟩]
theorem checked53292 : checkPrefixCuts (2^48) 6989021185 10 Manual.Count131072.C053292.packed 64 cuts53292 = true := by
 decide +kernel
def cuts53293 : List PrefixCut := [⟨35,125087632,125087704⟩,
⟨64,229353202,229353335⟩]
theorem checked53293 : checkPrefixCuts (2^48) 6989152257 10 Manual.Count131072.C053293.packed 64 cuts53293 = true := by
 decide +kernel
def pointBounds53293 : List (Nat × Nat × Nat) := [(6989223936,112449621543973,112450009116645)]
theorem point_links_checked53293 : (cuts53293.take 1).map (fun c => (6989152257-1+2*2^10*c.k,112449496456341+c.lower,112449884028941+c.upper)) = pointBounds53293 := by
 decide +kernel
def cuts53294 : List PrefixCut := [⟨64,235671591,235671723⟩]
theorem checked53294 : checkPrefixCuts (2^48) 6989283329 10 Manual.Count131072.C053294.packed 64 cuts53294 = true := by
 decide +kernel
def cuts53295 : List PrefixCut := [⟨14,51265639,51265668⟩,
⟨64,230915193,230915325⟩]
theorem checked53295 : checkPrefixCuts (2^48) 6989414401 10 Manual.Count131072.C053295.packed 64 cuts53295 = true := by
 decide +kernel
def pointBounds53295 : List (Nat × Nat × Nat) := [(6989443072,112450012746773,112450400319667)]
theorem point_links_checked53295 : (cuts53295.take 1).map (fun c => (6989414401-1+2*2^10*c.k,112449961481134+c.lower,112450349053999+c.upper)) = pointBounds53295 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000102
