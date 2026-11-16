import PlattAssemblyKernel
import PlattCertificates.Count131072.C064256
import PlattCertificates.Count131072.C064257
import PlattCertificates.Count131072.C064258
import PlattCertificates.Count131072.C064259
import PlattCertificates.Count131072.C064260
import PlattCertificates.Count131072.C064261
import PlattCertificates.Count131072.C064262
import PlattCertificates.Count131072.C064263
import PlattCertificates.Count131072.C064264
import PlattCertificates.Count131072.C064265
import PlattCertificates.Count131072.C064266
import PlattCertificates.Count131072.C064267
import PlattCertificates.Count131072.C064268
import PlattCertificates.Count131072.C064269
import PlattCertificates.Count131072.C064270
import PlattCertificates.Count131072.C064271
import PlattCertificates.Count131072.C064272
import PlattCertificates.Count131072.C064273
import PlattCertificates.Count131072.C064274
import PlattCertificates.Count131072.C064275
import PlattCertificates.Count131072.C064276
import PlattCertificates.Count131072.C064277
import PlattCertificates.Count131072.C064278
import PlattCertificates.Count131072.C064279
import PlattCertificates.Count131072.C064280
import PlattCertificates.Count131072.C064281
import PlattCertificates.Count131072.C064282
import PlattCertificates.Count131072.C064283
import PlattCertificates.Count131072.C064284
import PlattCertificates.Count131072.C064285
import PlattCertificates.Count131072.C064286
import PlattCertificates.Count131072.C064287
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000133
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64256 : List PrefixCut := [⟨62,187702078,187702191⟩,
⟨64,193982149,193982266⟩]
theorem checked64256 : checkPrefixCuts (2^48) 8426094593 10 Manual.Count131072.C064256.packed 64 cuts64256 = true := by
 decide +kernel
def pointBounds64256 : List (Nat × Nat × Nat) := [(8426221568,114761927956126,114762316848376)]
theorem point_links_checked64256 : (cuts64256.take 1).map (fun c => (8426094593-1+2*2^10*c.k,114761740254048+c.lower,114762129146185+c.upper)) = pointBounds64256 := by
 decide +kernel
def cuts64257 : List PrefixCut := [⟨64,193244243,193244358⟩]
theorem checked64257 : checkPrefixCuts (2^48) 8426225665 10 Manual.Count131072.C064257.packed 64 cuts64257 = true := by
 decide +kernel
def cuts64258 : List PrefixCut := [⟨63,190201500,190201610⟩,
⟨64,193575262,193575374⟩]
theorem checked64258 : checkPrefixCuts (2^48) 8426356737 10 Manual.Count131072.C064258.packed 64 cuts64258 = true := by
 decide +kernel
def pointBounds64258 : List (Nat × Nat × Nat) := [(8426485760,114762317681940,114762706574419)]
theorem point_links_checked64258 : (cuts64258.take 1).map (fun c => (8426356737-1+2*2^10*c.k,114762127480440+c.lower,114762516372809+c.upper)) = pointBounds64258 := by
 decide +kernel
def cuts64259 : List PrefixCut := [⟨64,190900011,190900119⟩]
theorem checked64259 : checkPrefixCuts (2^48) 8426487809 10 Manual.Count131072.C064259.packed 64 cuts64259 = true := by
 decide +kernel
def cuts64260 : List PrefixCut := [⟨64,191665290,191665408⟩]
theorem checked64260 : checkPrefixCuts (2^48) 8426618881 10 Manual.Count131072.C064260.packed 64 cuts64260 = true := by
 decide +kernel
def pointBounds64260 : List (Nat × Nat × Nat) := [(8426749952,114762703621003,114763092513710)]
theorem point_links_checked64260 : (cuts64260.take 1).map (fun c => (8426618881-1+2*2^10*c.k,114762511955713+c.lower,114762900848302+c.upper)) = pointBounds64260 := by
 decide +kernel
def cuts64261 : List PrefixCut := [⟨64,190159203,190159317⟩]
theorem checked64261 : checkPrefixCuts (2^48) 8426749953 10 Manual.Count131072.C064261.packed 64 cuts64261 = true := by
 decide +kernel
def cuts64262 : List PrefixCut := [⟨64,186983078,186983188⟩]
theorem checked64262 : checkPrefixCuts (2^48) 8426881025 10 Manual.Count131072.C064262.packed 64 cuts64262 = true := by
 decide +kernel
def cuts64263 : List PrefixCut := [⟨1,2839128,2839129⟩,
⟨64,192023758,192023868⟩]
theorem checked64263 : checkPrefixCuts (2^48) 8427012097 10 Manual.Count131072.C064263.packed 64 cuts64263 = true := by
 decide +kernel
def pointBounds64263 : List (Nat × Nat × Nat) := [(8427014144,114763083602412,114763472495344)]
theorem point_links_checked64263 : (cuts64263.take 1).map (fun c => (8427012097-1+2*2^10*c.k,114763080763284+c.lower,114763469656215+c.upper)) = pointBounds64263 := by
 decide +kernel
def cuts64264 : List PrefixCut := [⟨64,193390203,193390318⟩]
theorem checked64264 : checkPrefixCuts (2^48) 8427143169 10 Manual.Count131072.C064264.packed 64 cuts64264 = true := by
 decide +kernel
def cuts64265 : List PrefixCut := [⟨2,6012082,6012086⟩,
⟨64,192218180,192218292⟩]
theorem checked64265 : checkPrefixCuts (2^48) 8427274241 10 Manual.Count131072.C064265.packed 64 cuts64265 = true := by
 decide +kernel
def pointBounds64265 : List (Nat × Nat × Nat) := [(8427278336,114763472189327,114763861082487)]
theorem point_links_checked64265 : (cuts64265.take 1).map (fun c => (8427274241-1+2*2^10*c.k,114763466177245+c.lower,114763855070401+c.upper)) = pointBounds64265 := by
 decide +kernel
def cuts64266 : List PrefixCut := [⟨64,192949980,192950090⟩]
theorem checked64266 : checkPrefixCuts (2^48) 8427405313 10 Manual.Count131072.C064266.packed 64 cuts64266 = true := by
 decide +kernel
def cuts64267 : List PrefixCut := [⟨3,8483451,8483457⟩,
⟨64,191577634,191577744⟩]
theorem checked64267 : checkPrefixCuts (2^48) 8427536385 10 Manual.Count131072.C064267.packed 64 cuts64267 = true := by
 decide +kernel
def pointBounds64267 : List (Nat × Nat × Nat) := [(8427542528,114763859828856,114764248722240)]
theorem point_links_checked64267 : (cuts64267.take 1).map (fun c => (8427536385-1+2*2^10*c.k,114763851345405+c.lower,114764240238783+c.upper)) = pointBounds64267 := by
 decide +kernel
def cuts64268 : List PrefixCut := [⟨64,194981305,194981417⟩]
theorem checked64268 : checkPrefixCuts (2^48) 8427667457 10 Manual.Count131072.C064268.packed 64 cuts64268 = true := by
 decide +kernel
def cuts64269 : List PrefixCut := [⟨4,11856423,11856429⟩,
⟨64,189300597,189300706⟩]
theorem checked64269 : checkPrefixCuts (2^48) 8427798529 10 Manual.Count131072.C064269.packed 64 cuts64269 = true := by
 decide +kernel
def pointBounds64269 : List (Nat × Nat × Nat) := [(8427806720,114764249760767,114764638654373)]
theorem point_links_checked64269 : (cuts64269.take 1).map (fun c => (8427798529-1+2*2^10*c.k,114764237904344+c.lower,114764626797944+c.upper)) = pointBounds64269 := by
 decide +kernel
def cuts64270 : List PrefixCut := [⟨64,193038201,193038307⟩]
theorem checked64270 : checkPrefixCuts (2^48) 8427929601 10 Manual.Count131072.C064270.packed 64 cuts64270 = true := by
 decide +kernel
def cuts64271 : List PrefixCut := [⟨5,14828415,14828422⟩,
⟨64,193669733,193669843⟩]
theorem checked64271 : checkPrefixCuts (2^48) 8428060673 10 Manual.Count131072.C064271.packed 64 cuts64271 = true := by
 decide +kernel
def pointBounds64271 : List (Nat × Nat × Nat) := [(8428070912,114764635071557,114765023965379)]
theorem point_links_checked64271 : (cuts64271.take 1).map (fun c => (8428060673-1+2*2^10*c.k,114764620243142+c.lower,114765009136957+c.upper)) = pointBounds64271 := by
 decide +kernel
def cuts64272 : List PrefixCut := [⟨64,190861399,190861510⟩]
theorem checked64272 : checkPrefixCuts (2^48) 8428191745 10 Manual.Count131072.C064272.packed 64 cuts64272 = true := by
 decide +kernel
def cuts64273 : List PrefixCut := [⟨6,17933808,17933817⟩,
⟨64,192661824,192661932⟩]
theorem checked64273 : checkPrefixCuts (2^48) 8428322817 10 Manual.Count131072.C064273.packed 64 cuts64273 = true := by
 decide +kernel
def pointBounds64273 : List (Nat × Nat × Nat) := [(8428335104,114765022708082,114765411602127)]
theorem point_links_checked64273 : (cuts64273.take 1).map (fun c => (8428322817-1+2*2^10*c.k,114765004774274+c.lower,114765393668310+c.upper)) = pointBounds64273 := by
 decide +kernel
def cuts64274 : List PrefixCut := [⟨64,191122641,191122753⟩]
theorem checked64274 : checkPrefixCuts (2^48) 8428453889 10 Manual.Count131072.C064274.packed 64 cuts64274 = true := by
 decide +kernel
def cuts64275 : List PrefixCut := [⟨7,21506537,21506550⟩,
⟨64,192355284,192355396⟩]
theorem checked64275 : checkPrefixCuts (2^48) 8428584961 10 Manual.Count131072.C064275.packed 64 cuts64275 = true := by
 decide +kernel
def pointBounds64275 : List (Nat × Nat × Nat) := [(8428599296,114765410065276,114765798959545)]
theorem point_links_checked64275 : (cuts64275.take 1).map (fun c => (8428584961-1+2*2^10*c.k,114765388558739+c.lower,114765777452995+c.upper)) = pointBounds64275 := by
 decide +kernel
def cuts64276 : List PrefixCut := [⟨64,191183473,191183580⟩]
theorem checked64276 : checkPrefixCuts (2^48) 8428716033 10 Manual.Count131072.C064276.packed 64 cuts64276 = true := by
 decide +kernel
def cuts64277 : List PrefixCut := [⟨8,24544738,24544750⟩,
⟨64,192416086,192416195⟩]
theorem checked64277 : checkPrefixCuts (2^48) 8428847105 10 Manual.Count131072.C064277.packed 64 cuts64277 = true := by
 decide +kernel
def pointBounds64277 : List (Nat × Nat × Nat) := [(8428863488,114765796642234,114766185536721)]
theorem point_links_checked64277 : (cuts64277.take 1).map (fun c => (8428847105-1+2*2^10*c.k,114765772097496+c.lower,114766160991971+c.upper)) = pointBounds64277 := by
 decide +kernel
def cuts64278 : List PrefixCut := [⟨64,191444672,191444788⟩]
theorem checked64278 : checkPrefixCuts (2^48) 8428978177 10 Manual.Count131072.C064278.packed 64 cuts64278 = true := by
 decide +kernel
def cuts64279 : List PrefixCut := [⟨9,26647741,26647756⟩,
⟨64,192042768,192042878⟩]
theorem checked64279 : checkPrefixCuts (2^48) 8429109249 10 Manual.Count131072.C064279.packed 64 cuts64279 = true := by
 decide +kernel
def pointBounds64279 : List (Nat × Nat × Nat) := [(8429127680,114766182605995,114766571500710)]
theorem point_links_checked64279 : (cuts64279.take 1).map (fun c => (8429109249-1+2*2^10*c.k,114766155958254+c.lower,114766544852954+c.upper)) = pointBounds64279 := by
 decide +kernel
def cuts64280 : List PrefixCut := [⟨64,187598608,187598715⟩]
theorem checked64280 : checkPrefixCuts (2^48) 8429240321 10 Manual.Count131072.C064280.packed 64 cuts64280 = true := by
 decide +kernel
def cuts64281 : List PrefixCut := [⟨10,30153081,30153100⟩,
⟨64,191903238,191903347⟩]
theorem checked64281 : checkPrefixCuts (2^48) 8429371393 10 Manual.Count131072.C064281.packed 64 cuts64281 = true := by
 decide +kernel
def pointBounds64281 : List (Nat × Nat × Nat) := [(8429391872,114766565752711,114766954647647)]
theorem point_links_checked64281 : (cuts64281.take 1).map (fun c => (8429371393-1+2*2^10*c.k,114766535599630+c.lower,114766924494547+c.upper)) = pointBounds64281 := by
 decide +kernel
def cuts64282 : List PrefixCut := [⟨64,189729811,189729919⟩]
theorem checked64282 : checkPrefixCuts (2^48) 8429502465 10 Manual.Count131072.C064282.packed 64 cuts64282 = true := by
 decide +kernel
def cuts64283 : List PrefixCut := [⟨11,32589687,32589709⟩,
⟨64,190261103,190261221⟩]
theorem checked64283 : checkPrefixCuts (2^48) 8429633537 10 Manual.Count131072.C064283.packed 64 cuts64283 = true := by
 decide +kernel
def pointBounds64283 : List (Nat × Nat × Nat) := [(8429656064,114766949822366,114767338717522)]
theorem point_links_checked64283 : (cuts64283.take 1).map (fun c => (8429633537-1+2*2^10*c.k,114766917232679+c.lower,114767306127813+c.upper)) = pointBounds64283 := by
 decide +kernel
def cuts64284 : List PrefixCut := [⟨64,193363452,193363566⟩]
theorem checked64284 : checkPrefixCuts (2^48) 8429764609 10 Manual.Count131072.C064284.packed 64 cuts64284 = true := by
 decide +kernel
def cuts64285 : List PrefixCut := [⟨12,34925972,34925994⟩,
⟨64,190756040,190756151⟩]
theorem checked64285 : checkPrefixCuts (2^48) 8429895681 10 Manual.Count131072.C064285.packed 64 cuts64285 = true := by
 decide +kernel
def pointBounds64285 : List (Nat × Nat × Nat) := [(8429920256,114767335783206,114767724678594)]
theorem point_links_checked64285 : (cuts64285.take 1).map (fun c => (8429895681-1+2*2^10*c.k,114767300857234+c.lower,114767689752600+c.upper)) = pointBounds64285 := by
 decide +kernel
def cuts64286 : List PrefixCut := [⟨64,191654587,191654699⟩]
theorem checked64286 : checkPrefixCuts (2^48) 8430026753 10 Manual.Count131072.C064286.packed 64 cuts64286 = true := by
 decide +kernel
def cuts64287 : List PrefixCut := [⟨13,38697838,38697859⟩,
⟨64,191250950,191251054⟩]
theorem checked64287 : checkPrefixCuts (2^48) 8430157825 10 Manual.Count131072.C064287.packed 64 cuts64287 = true := by
 decide +kernel
def pointBounds64287 : List (Nat × Nat × Nat) := [(8430184448,114767721965699,114768110861309)]
theorem point_links_checked64287 : (cuts64287.take 1).map (fun c => (8430157825-1+2*2^10*c.k,114767683267861+c.lower,114768072163450+c.upper)) = pointBounds64287 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000133
