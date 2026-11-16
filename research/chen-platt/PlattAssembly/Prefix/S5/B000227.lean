import PlattAssemblyKernel
import PlattCertificates.Count131072.C047264
import PlattCertificates.Count131072.C047265
import PlattCertificates.Count131072.C047266
import PlattCertificates.Count131072.C047267
import PlattCertificates.Count131072.C047268
import PlattCertificates.Count131072.C047269
import PlattCertificates.Count131072.C047270
import PlattCertificates.Count131072.C047271
import PlattCertificates.Count131072.C047272
import PlattCertificates.Count131072.C047273
import PlattCertificates.Count131072.C047274
import PlattCertificates.Count131072.C047275
import PlattCertificates.Count131072.C047276
import PlattCertificates.Count131072.C047277
import PlattCertificates.Count131072.C047278
import PlattCertificates.Count131072.C047279
import PlattCertificates.Count131072.C047280
import PlattCertificates.Count131072.C047281
import PlattCertificates.Count131072.C047282
import PlattCertificates.Count131072.C047283
import PlattCertificates.Count131072.C047284
import PlattCertificates.Count131072.C047285
import PlattCertificates.Count131072.C047286
import PlattCertificates.Count131072.C047287
import PlattCertificates.Count131072.C047288
import PlattCertificates.Count131072.C047289
import PlattCertificates.Count131072.C047290
import PlattCertificates.Count131072.C047291
import PlattCertificates.Count131072.C047292
import PlattCertificates.Count131072.C047293
import PlattCertificates.Count131072.C047294
import PlattCertificates.Count131072.C047295
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000227
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts47264 : List PrefixCut := [⟨64,260089087,260089230⟩]
theorem checked47264 : checkPrefixCuts (2^48) 6198919169 10 Manual.Count131072.C047264.packed 64 cuts47264 = true := by
 decide +kernel
def cuts47265 : List PrefixCut := [⟨26,106522325,106522384⟩,
⟨64,263579792,263579939⟩]
theorem checked47265 : checkPrefixCuts (2^48) 6199050241 10 Manual.Count131072.C047265.packed 64 cuts47265 = true := by
 decide +kernel
def pointBounds47265 : List (Nat × Nat × Nat) := [(6199103488,110956087247750,110956473969484)]
theorem point_links_checked47265 : (cuts47265.take 1).map (fun c => (6199050241-1+2*2^10*c.k,110955980725425+c.lower,110956367447100+c.upper)) = pointBounds47265 := by
 decide +kernel
def cuts47266 : List PrefixCut := [⟨57,239737057,239737190⟩,
⟨64,268387149,268387299⟩]
theorem checked47266 : checkPrefixCuts (2^48) 6199181313 10 Manual.Count131072.C047266.packed 64 cuts47266 = true := by
 decide +kernel
def pointBounds47266 : List (Nat × Nat × Nat) := [(6199298048,110956484042274,110956870764229)]
theorem point_links_checked47266 : (cuts47266.take 1).map (fun c => (6199181313-1+2*2^10*c.k,110956244305217+c.lower,110956631027039+c.upper)) = pointBounds47266 := by
 decide +kernel
def cuts47267 : List PrefixCut := [⟨64,260889845,260889991⟩]
theorem checked47267 : checkPrefixCuts (2^48) 6199312385 10 Manual.Count131072.C047267.packed 64 cuts47267 = true := by
 decide +kernel
def cuts47268 : List PrefixCut := [⟨24,99205709,99205769⟩,
⟨64,262337221,262337371⟩]
theorem checked47268 : checkPrefixCuts (2^48) 6199443457 10 Manual.Count131072.C047268.packed 64 cuts47268 = true := by
 decide +kernel
def pointBounds47268 : List (Nat × Nat × Nat) := [(6199492608,110956872787920,110957259510098)]
theorem point_links_checked47268 : (cuts47268.take 1).map (fun c => (6199443457-1+2*2^10*c.k,110956773582211+c.lower,110957160304329+c.upper)) = pointBounds47268 := by
 decide +kernel
def cuts47269 : List PrefixCut := [⟨55,229188691,229188819⟩,
⟨64,267189661,267189812⟩]
theorem checked47269 : checkPrefixCuts (2^48) 6199574529 10 Manual.Count131072.C047269.packed 64 cuts47269 = true := by
 decide +kernel
def pointBounds47269 : List (Nat × Nat × Nat) := [(6199687168,110957265108123,110957651830519)]
theorem point_links_checked47269 : (cuts47269.take 1).map (fun c => (6199574529-1+2*2^10*c.k,110957035919432+c.lower,110957422641700+c.upper)) = pointBounds47269 := by
 decide +kernel
def cuts47270 : List PrefixCut := [⟨64,263688121,263688275⟩]
theorem checked47270 : checkPrefixCuts (2^48) 6199705601 10 Manual.Count131072.C047270.packed 64 cuts47270 = true := by
 decide +kernel
def cuts47271 : List PrefixCut := [⟨22,90936618,90936672⟩,
⟨64,264772183,264772331⟩]
theorem checked47271 : checkPrefixCuts (2^48) 6199836673 10 Manual.Count131072.C047271.packed 64 cuts47271 = true := by
 decide +kernel
def pointBounds47271 : List (Nat × Nat × Nat) := [(6199881728,110957657733832,110958044456459)]
theorem point_links_checked47271 : (cuts47271.take 1).map (fun c => (6199836673-1+2*2^10*c.k,110957566797214+c.lower,110957953519787+c.upper)) = pointBounds47271 := by
 decide +kernel
def cuts47272 : List PrefixCut := [⟨53,221864970,221865096⟩,
⟨64,266991115,266991266⟩]
theorem checked47272 : checkPrefixCuts (2^48) 6199967745 10 Manual.Count131072.C047272.packed 64 cuts47272 = true := by
 decide +kernel
def pointBounds47272 : List (Nat × Nat × Nat) := [(6200076288,110958053434367,110958440157214)]
theorem point_links_checked47272 : (cuts47272.take 1).map (fun c => (6199967745-1+2*2^10*c.k,110957831569397+c.lower,110958218292118+c.upper)) = pointBounds47272 := by
 decide +kernel
def cuts47273 : List PrefixCut := [⟨64,262037121,262037275⟩]
theorem checked47273 : checkPrefixCuts (2^48) 6200098817 10 Manual.Count131072.C047273.packed 64 cuts47273 = true := by
 decide +kernel
def cuts47274 : List PrefixCut := [⟨20,83985081,83985128⟩,
⟨64,263575079,263575232⟩]
theorem checked47274 : checkPrefixCuts (2^48) 6200229889 10 Manual.Count131072.C047274.packed 64 cuts47274 = true := by
 decide +kernel
def pointBounds47274 : List (Nat × Nat × Nat) := [(6200270848,110958444582714,110958831305787)]
theorem point_links_checked47274 : (cuts47274.take 1).map (fun c => (6200229889-1+2*2^10*c.k,110958360597633+c.lower,110958747320659+c.upper)) = pointBounds47274 := by
 decide +kernel
def cuts47275 : List PrefixCut := [⟨51,207188035,207188153⟩,
⟨64,261163488,261163637⟩]
theorem checked47275 : checkPrefixCuts (2^48) 6200360961 10 Manual.Count131072.C047275.packed 64 cuts47275 = true := by
 decide +kernel
def pointBounds47275 : List (Nat × Nat × Nat) := [(6200465408,110958831360747,110959218084044)]
theorem point_links_checked47275 : (cuts47275.take 1).map (fun c => (6200360961-1+2*2^10*c.k,110958624172712+c.lower,110959010895891+c.upper)) = pointBounds47275 := by
 decide +kernel
def cuts47276 : List PrefixCut := [⟨64,262882993,262883144⟩]
theorem checked47276 : checkPrefixCuts (2^48) 6200492033 10 Manual.Count131072.C047276.packed 64 cuts47276 = true := by
 decide +kernel
def cuts47277 : List PrefixCut := [⟨18,74265369,74265413⟩,
⟨64,264647799,264647950⟩]
theorem checked47277 : checkPrefixCuts (2^48) 6200623105 10 Manual.Count131072.C047277.packed 64 cuts47277 = true := by
 decide +kernel
def pointBounds47277 : List (Nat × Nat × Nat) := [(6200659968,110959222484562,110959609208085)]
theorem point_links_checked47277 : (cuts47277.take 1).map (fun c => (6200623105-1+2*2^10*c.k,110959148219193+c.lower,110959534942672+c.upper)) = pointBounds47277 := by
 decide +kernel
def cuts47278 : List PrefixCut := [⟨49,199912028,199912144⟩,
⟨64,261691641,261691793⟩]
theorem checked47278 : checkPrefixCuts (2^48) 6200754177 10 Manual.Count131072.C047278.packed 64 cuts47278 = true := by
 decide +kernel
def pointBounds47278 : List (Nat × Nat × Nat) := [(6200854528,110959612779020,110959999502766)]
theorem point_links_checked47278 : (cuts47278.take 1).map (fun c => (6200754177-1+2*2^10*c.k,110959412866992+c.lower,110959799590622+c.upper)) = pointBounds47278 := by
 decide +kernel
def cuts47279 : List PrefixCut := [⟨64,264863600,264863750⟩]
theorem checked47279 : checkPrefixCuts (2^48) 6200885249 10 Manual.Count131072.C047279.packed 64 cuts47279 = true := by
 decide +kernel
def cuts47280 : List PrefixCut := [⟨16,65318535,65318569⟩,
⟨64,264994152,264994300⟩]
theorem checked47280 : checkPrefixCuts (2^48) 6201016321 10 Manual.Count131072.C047280.packed 64 cuts47280 = true := by
 decide +kernel
def pointBounds47280 : List (Nat × Nat × Nat) := [(6201049088,110960004740768,110960391464734)]
theorem point_links_checked47280 : (cuts47280.take 1).map (fun c => (6201016321-1+2*2^10*c.k,110959939422233+c.lower,110960326146165+c.upper)) = pointBounds47280 := by
 decide +kernel
def cuts47281 : List PrefixCut := [⟨47,194271028,194271133⟩,
⟨64,264171543,264171687⟩]
theorem checked47281 : checkPrefixCuts (2^48) 6201147393 10 Manual.Count131072.C047281.packed 64 cuts47281 = true := by
 decide +kernel
def pointBounds47281 : List (Nat × Nat × Nat) := [(6201243648,110960398687413,110960785411598)]
theorem point_links_checked47281 : (cuts47281.take 1).map (fun c => (6201147393-1+2*2^10*c.k,110960204416385+c.lower,110960591140465+c.upper)) = pointBounds47281 := by
 decide +kernel
def cuts47282 : List PrefixCut := [⟨64,265890757,265890910⟩]
theorem checked47282 : checkPrefixCuts (2^48) 6201278465 10 Manual.Count131072.C047282.packed 64 cuts47282 = true := by
 decide +kernel
def cuts47283 : List PrefixCut := [⟨14,58687662,58687693⟩,
⟨64,262707939,262708094⟩]
theorem checked47283 : checkPrefixCuts (2^48) 6201409537 10 Manual.Count131072.C047283.packed 64 cuts47283 = true := by
 decide +kernel
def pointBounds47283 : List (Nat × Nat × Nat) := [(6201438208,110960793166347,110961179890755)]
theorem point_links_checked47283 : (cuts47283.take 1).map (fun c => (6201409537-1+2*2^10*c.k,110960734478685+c.lower,110961121203062+c.upper)) = pointBounds47283 := by
 decide +kernel
def cuts47284 : List PrefixCut := [⟨45,186497489,186497588⟩,
⟨64,266106433,266106578⟩]
theorem checked47284 : checkPrefixCuts (2^48) 6201540609 10 Manual.Count131072.C047284.packed 64 cuts47284 = true := by
 decide +kernel
def pointBounds47284 : List (Nat × Nat × Nat) := [(6201632768,110961183684113,110961570408744)]
theorem point_links_checked47284 : (cuts47284.take 1).map (fun c => (6201540609-1+2*2^10*c.k,110960997186624+c.lower,110961383911156+c.upper)) = pointBounds47284 := by
 decide +kernel
def cuts47285 : List PrefixCut := [⟨64,261607549,261607700⟩]
theorem checked47285 : checkPrefixCuts (2^48) 6201671681 10 Manual.Count131072.C047285.packed 64 cuts47285 = true := by
 decide +kernel
def cuts47286 : List PrefixCut := [⟨12,50877584,50877613⟩,
⟨64,263008999,263009148⟩]
theorem checked47286 : checkPrefixCuts (2^48) 6201802753 10 Manual.Count131072.C047286.packed 64 cuts47286 = true := by
 decide +kernel
def pointBounds47286 : List (Nat × Nat × Nat) := [(6201827328,110961575778190,110961962503047)]
theorem point_links_checked47286 : (cuts47286.take 1).map (fun c => (6201802753-1+2*2^10*c.k,110961524900606+c.lower,110961911625434+c.upper)) = pointBounds47286 := by
 decide +kernel
def cuts47287 : List PrefixCut := [⟨43,177635709,177635810⟩,
⟨64,262277280,262277430⟩]
theorem checked47287 : checkPrefixCuts (2^48) 6201933825 10 Manual.Count131072.C047287.packed 64 cuts47287 = true := by
 decide +kernel
def pointBounds47287 : List (Nat × Nat × Nat) := [(6202021888,110961965545314,110962352270392)]
theorem point_links_checked47287 : (cuts47287.take 1).map (fun c => (6201933825-1+2*2^10*c.k,110961787909605+c.lower,110962174634582+c.upper)) = pointBounds47287 := by
 decide +kernel
def cuts47288 : List PrefixCut := [⟨64,261863271,261863423⟩]
theorem checked47288 : checkPrefixCuts (2^48) 6202064897 10 Manual.Count131072.C047288.packed 64 cuts47288 = true := by
 decide +kernel
def cuts47289 : List PrefixCut := [⟨10,40708575,40708601⟩,
⟨64,264036088,264036240⟩]
theorem checked47289 : checkPrefixCuts (2^48) 6202195969 10 Manual.Count131072.C047289.packed 64 cuts47289 = true := by
 decide +kernel
def pointBounds47289 : List (Nat × Nat × Nat) := [(6202216448,110962352758731,110962739484036)]
theorem point_links_checked47289 : (cuts47289.take 1).map (fun c => (6202195969-1+2*2^10*c.k,110962312050156+c.lower,110962698775435+c.upper)) = pointBounds47289 := by
 decide +kernel
def cuts47290 : List PrefixCut := [⟨41,167822038,167822133⟩,
⟨64,263440562,263440711⟩]
theorem checked47290 : checkPrefixCuts (2^48) 6202327041 10 Manual.Count131072.C047290.packed 64 cuts47290 = true := by
 decide +kernel
def pointBounds47290 : List (Nat × Nat × Nat) := [(6202411008,110962743908282,110963130633808)]
theorem point_links_checked47290 : (cuts47290.take 1).map (fun c => (6202327041-1+2*2^10*c.k,110962576086244+c.lower,110962962811675+c.upper)) = pointBounds47290 := by
 decide +kernel
def cuts47291 : List PrefixCut := [⟨64,263571123,263571272⟩]
theorem checked47291 : checkPrefixCuts (2^48) 6202458113 10 Manual.Count131072.C047291.packed 64 cuts47291 = true := by
 decide +kernel
def cuts47292 : List PrefixCut := [⟨8,33399802,33399822⟩,
⟨64,266242974,266243122⟩]
theorem checked47292 : checkPrefixCuts (2^48) 6202589185 10 Manual.Count131072.C047292.packed 64 cuts47292 = true := by
 decide +kernel
def pointBounds47292 : List (Nat × Nat × Nat) := [(6202605568,110963136497731,110963523223480)]
theorem point_links_checked47292 : (cuts47292.take 1).map (fun c => (6202589185-1+2*2^10*c.k,110963103097929+c.lower,110963489823658+c.upper)) = pointBounds47292 := by
 decide +kernel
def cuts47293 : List PrefixCut := [⟨39,159960885,159960980⟩,
⟨64,262697795,262697949⟩]
theorem checked47293 : checkPrefixCuts (2^48) 6202720257 10 Manual.Count131072.C047293.packed 64 cuts47293 = true := by
 decide +kernel
def pointBounds47293 : List (Nat × Nat × Nat) := [(6202800128,110963529301788,110963916027760)]
theorem point_links_checked47293 : (cuts47293.take 1).map (fun c => (6202720257-1+2*2^10*c.k,110963369340903+c.lower,110963756066780+c.upper)) = pointBounds47293 := by
 decide +kernel
def cuts47294 : List PrefixCut := [⟨64,262737608,262737762⟩]
theorem checked47294 : checkPrefixCuts (2^48) 6202851329 10 Manual.Count131072.C047294.packed 64 cuts47294 = true := by
 decide +kernel
def cuts47295 : List PrefixCut := [⟨6,25093649,25093663⟩,
⟨64,265908467,265908614⟩]
theorem checked47295 : checkPrefixCuts (2^48) 6202982401 10 Manual.Count131072.C047295.packed 64 cuts47295 = true := by
 decide +kernel
def pointBounds47295 : List (Nat × Nat × Nat) := [(6202994688,110963919869955,110964306596154)]
theorem point_links_checked47295 : (cuts47295.take 1).map (fun c => (6202982401-1+2*2^10*c.k,110963894776306+c.lower,110964281502491+c.upper)) = pointBounds47295 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000227
