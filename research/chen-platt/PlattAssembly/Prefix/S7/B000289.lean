import PlattAssemblyKernel
import PlattCertificates.Count131072.C069248
import PlattCertificates.Count131072.C069249
import PlattCertificates.Count131072.C069250
import PlattCertificates.Count131072.C069251
import PlattCertificates.Count131072.C069252
import PlattCertificates.Count131072.C069253
import PlattCertificates.Count131072.C069254
import PlattCertificates.Count131072.C069255
import PlattCertificates.Count131072.C069256
import PlattCertificates.Count131072.C069257
import PlattCertificates.Count131072.C069258
import PlattCertificates.Count131072.C069259
import PlattCertificates.Count131072.C069260
import PlattCertificates.Count131072.C069261
import PlattCertificates.Count131072.C069262
import PlattCertificates.Count131072.C069263
import PlattCertificates.Count131072.C069264
import PlattCertificates.Count131072.C069265
import PlattCertificates.Count131072.C069266
import PlattCertificates.Count131072.C069267
import PlattCertificates.Count131072.C069268
import PlattCertificates.Count131072.C069269
import PlattCertificates.Count131072.C069270
import PlattCertificates.Count131072.C069271
import PlattCertificates.Count131072.C069272
import PlattCertificates.Count131072.C069273
import PlattCertificates.Count131072.C069274
import PlattCertificates.Count131072.C069275
import PlattCertificates.Count131072.C069276
import PlattCertificates.Count131072.C069277
import PlattCertificates.Count131072.C069278
import PlattCertificates.Count131072.C069279
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000289
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69248 : List PrefixCut := [⟨29,80842654,80842699⟩,
⟨64,175013748,175013852⟩]
theorem checked69248 : checkPrefixCuts (2^48) 9080406017 10 Manual.Count131072.C069248.packed 64 cuts69248 = true := by
 decide +kernel
def pointBounds69248 : List (Nat × Nat × Nat) := [(9080465408,115681338486748,115681727914078)]
theorem point_links_checked69248 : (cuts69248.take 1).map (fun c => (9080406017-1+2*2^10*c.k,115681257644094+c.lower,115681647071379+c.upper)) = pointBounds69248 := by
 decide +kernel
def cuts69249 : List PrefixCut := [⟨64,176809052,176809156⟩]
theorem checked69249 : checkPrefixCuts (2^48) 9080537089 10 Manual.Count131072.C069249.packed 64 cuts69249 = true := by
 decide +kernel
def cuts69250 : List PrefixCut := [⟨40,109853436,109853498⟩,
⟨64,175659629,175659729⟩]
theorem checked69250 : checkPrefixCuts (2^48) 9080668161 10 Manual.Count131072.C069250.packed 64 cuts69250 = true := by
 decide +kernel
def pointBounds69250 : List (Nat × Nat × Nat) := [(9080750080,115681719320330,115682108747885)]
theorem point_links_checked69250 : (cuts69250.take 1).map (fun c => (9080668161-1+2*2^10*c.k,115681609466894+c.lower,115681998894387+c.upper)) = pointBounds69250 := by
 decide +kernel
def cuts69251 : List PrefixCut := [⟨64,178229801,178229903⟩]
theorem checked69251 : checkPrefixCuts (2^48) 9080799233 10 Manual.Count131072.C069251.packed 64 cuts69251 = true := by
 decide +kernel
def cuts69252 : List PrefixCut := [⟨51,142396011,142396092⟩,
⟨64,178444196,178444299⟩]
theorem checked69252 : checkPrefixCuts (2^48) 9080930305 10 Manual.Count131072.C069252.packed 64 cuts69252 = true := by
 decide +kernel
def pointBounds69252 : List (Nat × Nat × Nat) := [(9081034752,115682105752335,115682495180111)]
theorem point_links_checked69252 : (cuts69252.take 1).map (fun c => (9080930305-1+2*2^10*c.k,115681963356324+c.lower,115682352784019+c.upper)) = pointBounds69252 := by
 decide +kernel
def cuts69253 : List PrefixCut := [⟨64,179185505,179185609⟩]
theorem checked69253 : checkPrefixCuts (2^48) 9081061377 10 Manual.Count131072.C069253.packed 64 cuts69253 = true := by
 decide +kernel
def cuts69254 : List PrefixCut := [⟨62,169171515,169171618⟩,
⟨64,174626622,174626728⟩]
theorem checked69254 : checkPrefixCuts (2^48) 9081192449 10 Manual.Count131072.C069254.packed 64 cuts69254 = true := by
 decide +kernel
def pointBounds69254 : List (Nat × Nat × Nat) := [(9081319424,115682490157540,115682879585545)]
theorem point_links_checked69254 : (cuts69254.take 1).map (fun c => (9081192449-1+2*2^10*c.k,115682320986025+c.lower,115682710413927+c.upper)) = pointBounds69254 := by
 decide +kernel
def cuts69255 : List PrefixCut := [⟨64,177227665,177227772⟩]
theorem checked69255 : checkPrefixCuts (2^48) 9081323521 10 Manual.Count131072.C069255.packed 64 cuts69255 = true := by
 decide +kernel
def cuts69256 : List PrefixCut := [⟨64,175458448,175458553⟩]
theorem checked69256 : checkPrefixCuts (2^48) 9081454593 10 Manual.Count131072.C069256.packed 64 cuts69256 = true := by
 decide +kernel
def cuts69257 : List PrefixCut := [⟨9,25074142,25074155⟩,
⟨64,178090390,178090487⟩]
theorem checked69257 : checkPrefixCuts (2^48) 9081585665 10 Manual.Count131072.C069257.packed 64 cuts69257 = true := by
 decide +kernel
def pointBounds69257 : List (Nat × Nat × Nat) := [(9081604096,115682873372902,115683262801135)]
theorem point_links_checked69257 : (cuts69257.take 1).map (fun c => (9081585665-1+2*2^10*c.k,115682848298760+c.lower,115683237726980+c.upper)) = pointBounds69257 := by
 decide +kernel
def cuts69258 : List PrefixCut := [⟨64,178273779,178273883⟩]
theorem checked69258 : checkPrefixCuts (2^48) 9081716737 10 Manual.Count131072.C069258.packed 64 cuts69258 = true := by
 decide +kernel
def cuts69259 : List PrefixCut := [⟨20,55353608,55353637⟩,
⟨64,176814541,176814642⟩]
theorem checked69259 : checkPrefixCuts (2^48) 9081847809 10 Manual.Count131072.C069259.packed 64 cuts69259 = true := by
 decide +kernel
def pointBounds69259 : List (Nat × Nat × Nat) := [(9081888768,115683260016537,115683649444987)]
theorem point_links_checked69259 : (cuts69259.take 1).map (fun c => (9081847809-1+2*2^10*c.k,115683204662929+c.lower,115683594091350+c.upper)) = pointBounds69259 := by
 decide +kernel
def cuts69260 : List PrefixCut := [⟨64,176595044,176595150⟩]
theorem checked69260 : checkPrefixCuts (2^48) 9081978881 10 Manual.Count131072.C069260.packed 64 cuts69260 = true := by
 decide +kernel
def cuts69261 : List PrefixCut := [⟨31,85755219,85755270⟩,
⟨64,178823907,178824009⟩]
theorem checked69261 : checkPrefixCuts (2^48) 9082109953 10 Manual.Count131072.C069261.packed 64 cuts69261 = true := by
 decide +kernel
def pointBounds69261 : List (Nat × Nat × Nat) := [(9082173440,115683643827733,115684033256412)]
theorem point_links_checked69261 : (cuts69261.take 1).map (fun c => (9082109953-1+2*2^10*c.k,115683558072514+c.lower,115683947501142+c.upper)) = pointBounds69261 := by
 decide +kernel
def cuts69262 : List PrefixCut := [⟨64,177333741,177333851⟩]
theorem checked69262 : checkPrefixCuts (2^48) 9082241025 10 Manual.Count131072.C069262.packed 64 cuts69262 = true := by
 decide +kernel
def cuts69263 : List PrefixCut := [⟨42,117828523,117828594⟩,
⟨64,179159655,179159762⟩]
theorem checked69263 : checkPrefixCuts (2^48) 9082372097 10 Manual.Count131072.C069263.packed 64 cuts69263 = true := by
 decide +kernel
def pointBounds69263 : List (Nat × Nat × Nat) := [(9082458112,115684032058685,115684421487596)]
theorem point_links_checked69263 : (cuts69263.take 1).map (fun c => (9082372097-1+2*2^10*c.k,115683914230162+c.lower,115684303659002+c.upper)) = pointBounds69263 := by
 decide +kernel
def cuts69264 : List PrefixCut := [⟨64,176553847,176553954⟩]
theorem checked69264 : checkPrefixCuts (2^48) 9082503169 10 Manual.Count131072.C069264.packed 64 cuts69264 = true := by
 decide +kernel
def cuts69265 : List PrefixCut := [⟨53,144352636,144352723⟩,
⟨64,175032773,175032880⟩]
theorem checked69265 : checkPrefixCuts (2^48) 9082634241 10 Manual.Count131072.C069265.packed 64 cuts69265 = true := by
 decide +kernel
def pointBounds69265 : List (Nat × Nat × Nat) := [(9082742784,115684414296300,115684803725441)]
theorem point_links_checked69265 : (cuts69265.take 1).map (fun c => (9082634241-1+2*2^10*c.k,115684269943664+c.lower,115684659372718+c.upper)) = pointBounds69265 := by
 decide +kernel
def cuts69266 : List PrefixCut := [⟨64,174968288,174968393⟩]
theorem checked69266 : checkPrefixCuts (2^48) 9082765313 10 Manual.Count131072.C069266.packed 64 cuts69266 = true := by
 decide +kernel
def cuts69267 : List PrefixCut := [⟨64,177135005,177135107⟩]
theorem checked69267 : checkPrefixCuts (2^48) 9082896385 10 Manual.Count131072.C069267.packed 64 cuts69267 = true := by
 decide +kernel
def pointBounds69267 : List (Nat × Nat × Nat) := [(9083027456,115684797079730,115685186509098)]
theorem point_links_checked69267 : (cuts69267.take 1).map (fun c => (9082896385-1+2*2^10*c.k,115684619944725+c.lower,115685009373991+c.upper)) = pointBounds69267 := by
 decide +kernel
def cuts69268 : List PrefixCut := [⟨64,177411349,177411454⟩]
theorem checked69268 : checkPrefixCuts (2^48) 9083027457 10 Manual.Count131072.C069268.packed 64 cuts69268 = true := by
 decide +kernel
def cuts69269 : List PrefixCut := [⟨64,175394538,175394638⟩]
theorem checked69269 : checkPrefixCuts (2^48) 9083158529 10 Manual.Count131072.C069269.packed 64 cuts69269 = true := by
 decide +kernel
def cuts69270 : List PrefixCut := [⟨11,28880976,28880993⟩,
⟨64,175980770,175980870⟩]
theorem checked69270 : checkPrefixCuts (2^48) 9083289601 10 Manual.Count131072.C069270.packed 64 cuts69270 = true := by
 decide +kernel
def pointBounds69270 : List (Nat × Nat × Nat) := [(9083312128,115685178766593,115685568196183)]
theorem point_links_checked69270 : (cuts69270.take 1).map (fun c => (9083289601-1+2*2^10*c.k,115685149885617+c.lower,115685539315190+c.upper)) = pointBounds69270 := by
 decide +kernel
def cuts69271 : List PrefixCut := [⟨64,178209354,178209460⟩]
theorem checked69271 : checkPrefixCuts (2^48) 9083420673 10 Manual.Count131072.C069271.packed 64 cuts69271 = true := by
 decide +kernel
def cuts69272 : List PrefixCut := [⟨22,60270181,60270213⟩,
⟨64,176502484,176502582⟩]
theorem checked69272 : checkPrefixCuts (2^48) 9083551745 10 Manual.Count131072.C069272.packed 64 cuts69272 = true := by
 decide +kernel
def pointBounds69272 : List (Nat × Nat × Nat) := [(9083596800,115685564345922,115685953775733)]
theorem point_links_checked69272 : (cuts69272.take 1).map (fun c => (9083551745-1+2*2^10*c.k,115685504075741+c.lower,115685893505520+c.upper)) = pointBounds69272 := by
 decide +kernel
def cuts69273 : List PrefixCut := [⟨64,176035133,176035236⟩]
theorem checked69273 : checkPrefixCuts (2^48) 9083682817 10 Manual.Count131072.C069273.packed 64 cuts69273 = true := by
 decide +kernel
def cuts69274 : List PrefixCut := [⟨33,90449031,90449087⟩,
⟨64,176745274,176745385⟩]
theorem checked69274 : checkPrefixCuts (2^48) 9083813889 10 Manual.Count131072.C069274.packed 64 cuts69274 = true := by
 decide +kernel
def pointBounds69274 : List (Nat × Nat × Nat) := [(9083881472,115685947062389,115686336492425)]
theorem point_links_checked69274 : (cuts69274.take 1).map (fun c => (9083813889-1+2*2^10*c.k,115685856613358+c.lower,115686246043338+c.upper)) = pointBounds69274 := by
 decide +kernel
def cuts69275 : List PrefixCut := [⟨64,176587802,176587905⟩]
theorem checked69275 : checkPrefixCuts (2^48) 9083944961 10 Manual.Count131072.C069275.packed 64 cuts69275 = true := by
 decide +kernel
def cuts69276 : List PrefixCut := [⟨44,123011937,123012010⟩,
⟨64,179497868,179497975⟩]
theorem checked69276 : checkPrefixCuts (2^48) 9084076033 10 Manual.Count131072.C069276.packed 64 cuts69276 = true := by
 decide +kernel
def pointBounds69276 : List (Nat × Nat × Nat) := [(9084166144,115686332958371,115686722388638)]
theorem point_links_checked69276 : (cuts69276.take 1).map (fun c => (9084076033-1+2*2^10*c.k,115686209946434+c.lower,115686599376628+c.upper)) = pointBounds69276 := by
 decide +kernel
def cuts69277 : List PrefixCut := [⟨64,178410816,178410919⟩]
theorem checked69277 : checkPrefixCuts (2^48) 9084207105 10 Manual.Count131072.C069277.packed 64 cuts69277 = true := by
 decide +kernel
def cuts69278 : List PrefixCut := [⟨55,153589873,153589960⟩,
⟨64,178284297,178284396⟩]
theorem checked69278 : checkPrefixCuts (2^48) 9084338177 10 Manual.Count131072.C069278.packed 64 cuts69278 = true := by
 decide +kernel
def pointBounds69278 : List (Nat × Nat × Nat) := [(9084450816,115686721444991,115687110875482)]
theorem point_links_checked69278 : (cuts69278.take 1).map (fun c => (9084338177-1+2*2^10*c.k,115686567855118+c.lower,115686957285522+c.upper)) = pointBounds69278 := by
 decide +kernel
def cuts69279 : List PrefixCut := [⟨64,175710073,175710172⟩]
theorem checked69279 : checkPrefixCuts (2^48) 9084469249 10 Manual.Count131072.C069279.packed 64 cuts69279 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000289
