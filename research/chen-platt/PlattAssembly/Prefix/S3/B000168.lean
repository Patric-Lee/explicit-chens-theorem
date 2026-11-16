import PlattAssemblyKernel
import PlattCertificates.Count131072.C025376
import PlattCertificates.Count131072.C025377
import PlattCertificates.Count131072.C025378
import PlattCertificates.Count131072.C025379
import PlattCertificates.Count131072.C025380
import PlattCertificates.Count131072.C025381
import PlattCertificates.Count131072.C025382
import PlattCertificates.Count131072.C025383
import PlattCertificates.Count131072.C025384
import PlattCertificates.Count131072.C025385
import PlattCertificates.Count131072.C025386
import PlattCertificates.Count131072.C025387
import PlattCertificates.Count131072.C025388
import PlattCertificates.Count131072.C025389
import PlattCertificates.Count131072.C025390
import PlattCertificates.Count131072.C025391
import PlattCertificates.Count131072.C025392
import PlattCertificates.Count131072.C025393
import PlattCertificates.Count131072.C025394
import PlattCertificates.Count131072.C025395
import PlattCertificates.Count131072.C025396
import PlattCertificates.Count131072.C025397
import PlattCertificates.Count131072.C025398
import PlattCertificates.Count131072.C025399
import PlattCertificates.Count131072.C025400
import PlattCertificates.Count131072.C025401
import PlattCertificates.Count131072.C025402
import PlattCertificates.Count131072.C025403
import PlattCertificates.Count131072.C025404
import PlattCertificates.Count131072.C025405
import PlattCertificates.Count131072.C025406
import PlattCertificates.Count131072.C025407
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000168
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25376 : List PrefixCut := [⟨2,7607392,7607397⟩,
⟨104,415779811,415780049⟩,
⟨128,510192664,510192952⟩]
theorem checked25376 : checkPrefixCuts (2^48) 3330015233 9 Manual.Count131072.C025376.packed 128 cuts25376 = true := by
 decide +kernel
def pointBounds25376 : List (Nat × Nat × Nat) := [(3330017280,103089506083553,103089888207441),(3330121728,103089914255972,103090296380093)]
theorem point_links_checked25376 : (cuts25376.take 2).map (fun c => (3330015233-1+2*2^9*c.k,103089498476161+c.lower,103089880600044+c.upper)) = pointBounds25376 := by
 decide +kernel
def cuts25377 : List PrefixCut := [⟨78,304702744,304702914⟩,
⟨128,504171385,504171666⟩]
theorem checked25377 : checkPrefixCuts (2^48) 3330146305 9 Manual.Count131072.C025377.packed 128 cuts25377 = true := by
 decide +kernel
def pointBounds25377 : List (Nat × Nat × Nat) := [(3330226176,103090313371569,103090695495910)]
theorem point_links_checked25377 : (cuts25377.take 1).map (fun c => (3330146305-1+2*2^9*c.k,103090008668825+c.lower,103090390792996+c.upper)) = pointBounds25377 := by
 decide +kernel
def cuts25378 : List PrefixCut := [⟨52,201747545,201747655⟩,
⟨128,505081287,505081572⟩]
theorem checked25378 : checkPrefixCuts (2^48) 3330277377 9 Manual.Count131072.C025378.packed 128 cuts25378 = true := by
 decide +kernel
def pointBounds25378 : List (Nat × Nat × Nat) := [(3330330624,103090714587755,103091096712317)]
theorem point_links_checked25378 : (cuts25378.take 1).map (fun c => (3330277377-1+2*2^9*c.k,103090512840210+c.lower,103090894964662+c.upper)) = pointBounds25378 := by
 decide +kernel
def cuts25379 : List PrefixCut := [⟨26,103109864,103109924⟩,
⟨128,499145421,499145702⟩]
theorem checked25379 : checkPrefixCuts (2^48) 3330408449 9 Manual.Count131072.C025379.packed 128 cuts25379 = true := by
 decide +kernel
def pointBounds25379 : List (Nat × Nat × Nat) := [(3330435072,103091121031361,103091503156158),(3330539520,103091517066918,103091899191936)]
theorem point_links_checked25379 : (cuts25379.take 2).map (fun c => (3330408449-1+2*2^9*c.k,103091017921497+c.lower,103091400046234+c.upper)) = pointBounds25379 := by
 decide +kernel
def cuts25380 : List PrefixCut := [⟨102,405319479,405319710⟩,
⟨128,510872847,510873138⟩]
theorem checked25380 : checkPrefixCuts (2^48) 3330539521 9 Manual.Count131072.C025380.packed 128 cuts25380 = true := by
 decide +kernel
def pointBounds25380 : List (Nat × Nat × Nat) := [(3330643968,103091922386397,103092304511646)]
theorem point_links_checked25380 : (cuts25380.take 1).map (fun c => (3330539521-1+2*2^9*c.k,103091517066918+c.lower,103091899191936+c.upper)) = pointBounds25380 := by
 decide +kernel
def cuts25381 : List PrefixCut := [⟨76,298823824,298823989⟩,
⟨128,508993550,508993829⟩]
theorem checked25381 : checkPrefixCuts (2^48) 3330670593 9 Manual.Count131072.C025381.packed 128 cuts25381 = true := by
 decide +kernel
def pointBounds25381 : List (Nat × Nat × Nat) := [(3330748416,103092326763589,103092708889063)]
theorem point_links_checked25381 : (cuts25381.take 1).map (fun c => (3330670593-1+2*2^9*c.k,103092027939765+c.lower,103092410065074+c.upper)) = pointBounds25381 := by
 decide +kernel
def cuts25382 : List PrefixCut := [⟨50,201969337,201969451⟩,
⟨128,505086371,505086652⟩]
theorem checked25382 : checkPrefixCuts (2^48) 3330801665 9 Manual.Count131072.C025382.packed 128 cuts25382 = true := by
 decide +kernel
def pointBounds25382 : List (Nat × Nat × Nat) := [(3330852864,103092738902652,103093121028354)]
theorem point_links_checked25382 : (cuts25382.take 1).map (fun c => (3330801665-1+2*2^9*c.k,103092536933315+c.lower,103092919058903+c.upper)) = pointBounds25382 := by
 decide +kernel
def cuts25383 : List PrefixCut := [⟨24,94981388,94981442⟩,
⟨126,495179951,495180229⟩,
⟨128,502277953,502278235⟩]
theorem checked25383 : checkPrefixCuts (2^48) 3330932737 9 Manual.Count131072.C025383.packed 128 cuts25383 = true := by
 decide +kernel
def pointBounds25383 : List (Nat × Nat × Nat) := [(3330957312,103093137001074,103093519126997),(3331061760,103093537199637,103093919325784)]
theorem point_links_checked25383 : (cuts25383.take 2).map (fun c => (3330932737-1+2*2^9*c.k,103093042019686+c.lower,103093424145555+c.upper)) = pointBounds25383 := by
 decide +kernel
def cuts25384 : List PrefixCut := [⟨100,396129866,396130088⟩,
⟨128,506905486,506905770⟩]
theorem checked25384 : checkPrefixCuts (2^48) 3331063809 9 Manual.Count131072.C025384.packed 128 cuts25384 = true := by
 decide +kernel
def pointBounds25384 : List (Nat × Nat × Nat) := [(3331166208,103093940427505,103094322553878)]
theorem point_links_checked25384 : (cuts25384.take 1).map (fun c => (3331063809-1+2*2^9*c.k,103093544297639+c.lower,103093926423790+c.upper)) = pointBounds25384 := by
 decide +kernel
def cuts25385 : List PrefixCut := [⟨74,291003193,291003358⟩,
⟨128,503674746,503675031⟩]
theorem checked25385 : checkPrefixCuts (2^48) 3331194881 9 Manual.Count131072.C025385.packed 128 cuts25385 = true := by
 decide +kernel
def pointBounds25385 : List (Nat × Nat × Nat) := [(3331270656,103094342206318,103094724332918)]
theorem point_links_checked25385 : (cuts25385.take 1).map (fun c => (3331194881-1+2*2^9*c.k,103094051203125+c.lower,103094433329560+c.upper)) = pointBounds25385 := by
 decide +kernel
def cuts25386 : List PrefixCut := [⟨48,188587787,188587892⟩,
⟨128,504837866,504838153⟩]
theorem checked25386 : checkPrefixCuts (2^48) 3331325953 9 Manual.Count131072.C025386.packed 128 cuts25386 = true := by
 decide +kernel
def pointBounds25386 : List (Nat × Nat × Nat) := [(3331375104,103094743465658,103095125592483)]
theorem point_links_checked25386 : (cuts25386.take 1).map (fun c => (3331325953-1+2*2^9*c.k,103094554877871+c.lower,103094937004591+c.upper)) = pointBounds25386 := by
 decide +kernel
def cuts25387 : List PrefixCut := [⟨22,88460752,88460800⟩,
⟨124,496622946,496623222⟩,
⟨128,512421968,512422254⟩]
theorem checked25387 : checkPrefixCuts (2^48) 3331457025 9 Manual.Count131072.C025387.packed 128 cuts25387 = true := by
 decide +kernel
def pointBounds25387 : List (Nat × Nat × Nat) := [(3331479552,103095148176489,103095530303544),(3331584000,103095556338683,103095938465966)]
theorem point_links_checked25387 : (cuts25387.take 2).map (fun c => (3331457025-1+2*2^9*c.k,103095059715737+c.lower,103095441842744+c.upper)) = pointBounds25387 := by
 decide +kernel
def cuts25388 : List PrefixCut := [⟨98,388041649,388041867⟩,
⟨128,503784413,503784694⟩]
theorem checked25388 : checkPrefixCuts (2^48) 3331588097 9 Manual.Count131072.C025388.packed 128 cuts25388 = true := by
 decide +kernel
def pointBounds25388 : List (Nat × Nat × Nat) := [(3331688448,103095960179354,103096342306865)]
theorem point_links_checked25388 : (cuts25388.take 1).map (fun c => (3331588097-1+2*2^9*c.k,103095572137705+c.lower,103095954264998+c.upper)) = pointBounds25388 := by
 decide +kernel
def cuts25389 : List PrefixCut := [⟨72,289521349,289521511⟩,
⟨128,509509303,509509591⟩]
theorem checked25389 : checkPrefixCuts (2^48) 3331719169 9 Manual.Count131072.C025389.packed 128 cuts25389 = true := by
 decide +kernel
def pointBounds25389 : List (Nat × Nat × Nat) := [(3331792896,103096365443467,103096747571203)]
theorem point_links_checked25389 : (cuts25389.take 1).map (fun c => (3331719169-1+2*2^9*c.k,103096075922118+c.lower,103096458049692+c.upper)) = pointBounds25389 := by
 decide +kernel
def cuts25390 : List PrefixCut := [⟨46,183911781,183911884⟩,
⟨128,508644400,508644680⟩]
theorem checked25390 : checkPrefixCuts (2^48) 3331850241 9 Manual.Count131072.C025390.packed 128 cuts25390 = true := by
 decide +kernel
def pointBounds25390 : List (Nat × Nat × Nat) := [(3331897344,103096769343202,103097151471167)]
theorem point_links_checked25390 : (cuts25390.take 1).map (fun c => (3331850241-1+2*2^9*c.k,103096585431421+c.lower,103096967559283+c.upper)) = pointBounds25390 := by
 decide +kernel
def cuts25391 : List PrefixCut := [⟨20,78140741,78140788⟩,
⟨122,485732037,485732314⟩,
⟨128,508455406,508455695⟩]
theorem checked25391 : checkPrefixCuts (2^48) 3331981313 9 Manual.Count131072.C025391.packed 128 cuts25391 = true := by
 decide +kernel
def pointBounds25391 : List (Nat × Nat × Nat) := [(3332001792,103097172216562,103097554344751),(3332106240,103097579807858,103097961936277)]
theorem point_links_checked25391 : (cuts25391.take 2).map (fun c => (3331981313-1+2*2^9*c.k,103097094075821+c.lower,103097476203963+c.upper)) = pointBounds25391 := by
 decide +kernel
def cuts25392 : List PrefixCut := [⟨96,370156928,370157141⟩,
⟨128,502015378,502015663⟩]
theorem checked25392 : checkPrefixCuts (2^48) 3332112385 9 Manual.Count131072.C025392.packed 128 cuts25392 = true := by
 decide +kernel
def pointBounds25392 : List (Nat × Nat × Nat) := [(3332210688,103097972688155,103098354816799)]
theorem point_links_checked25392 : (cuts25392.take 1).map (fun c => (3332112385-1+2*2^9*c.k,103097602531227+c.lower,103097984659658+c.upper)) = pointBounds25392 := by
 decide +kernel
def cuts25393 : List PrefixCut := [⟨70,277481261,277481418⟩,
⟨128,504192054,504192344⟩]
theorem checked25393 : checkPrefixCuts (2^48) 3332243457 9 Manual.Count131072.C025393.packed 128 cuts25393 = true := by
 decide +kernel
def pointBounds25393 : List (Nat × Nat × Nat) := [(3332315136,103098382027866,103098764156739)]
theorem point_links_checked25393 : (cuts25393.take 1).map (fun c => (3332243457-1+2*2^9*c.k,103098104546605+c.lower,103098486675321+c.upper)) = pointBounds25393 := by
 decide +kernel
def cuts25394 : List PrefixCut := [⟨44,173831421,173831522⟩,
⟨128,509324493,509324776⟩]
theorem checked25394 : checkPrefixCuts (2^48) 3332374529 9 Manual.Count131072.C025394.packed 128 cuts25394 = true := by
 decide +kernel
def pointBounds25394 : List (Nat × Nat × Nat) := [(3332419584,103098782570080,103099164699187)]
theorem point_links_checked25394 : (cuts25394.take 1).map (fun c => (3332374529-1+2*2^9*c.k,103098608738659+c.lower,103098990867665+c.upper)) = pointBounds25394 := by
 decide +kernel
def cuts25395 : List PrefixCut := [⟨18,71624808,71624848⟩,
⟨120,469608077,469608344⟩,
⟨128,500520519,500520803⟩]
theorem checked25395 : checkPrefixCuts (2^48) 3332505601 9 Manual.Count131072.C025395.packed 128 cuts25395 = true := by
 decide +kernel
def pointBounds25395 : List (Nat × Nat × Nat) := [(3332524032,103099189687960,103099571817289),(3332628480,103099587671229,103099969800785)]
theorem point_links_checked25395 : (cuts25395.take 2).map (fun c => (3332505601-1+2*2^9*c.k,103099118063152+c.lower,103099500192441+c.upper)) = pointBounds25395 := by
 decide +kernel
def cuts25396 : List PrefixCut := [⟨94,361230677,361230885⟩,
⟨128,497882492,497882776⟩]
theorem checked25396 : checkPrefixCuts (2^48) 3332636673 9 Manual.Count131072.C025396.packed 128 cuts25396 = true := by
 decide +kernel
def pointBounds25396 : List (Nat × Nat × Nat) := [(3332732928,103099979814348,103100361944129)]
theorem point_links_checked25396 : (cuts25396.take 1).map (fun c => (3332636673-1+2*2^9*c.k,103099618583671+c.lower,103100000713244+c.upper)) = pointBounds25396 := by
 decide +kernel
def cuts25397 : List PrefixCut := [⟨68,272877037,272877194⟩,
⟨128,508673291,508673583⟩]
theorem checked25397 : checkPrefixCuts (2^48) 3332767745 9 Manual.Count131072.C025397.packed 128 cuts25397 = true := by
 decide +kernel
def pointBounds25397 : List (Nat × Nat × Nat) := [(3332837376,103100389343200,103100771473214)]
theorem point_links_checked25397 : (cuts25397.take 1).map (fun c => (3332767745-1+2*2^9*c.k,103100116466163+c.lower,103100498596020+c.upper)) = pointBounds25397 := by
 decide +kernel
def cuts25398 : List PrefixCut := [⟨42,163923144,163923235⟩,
⟨128,511440114,511440409⟩]
theorem checked25398 : checkPrefixCuts (2^48) 3332898817 9 Manual.Count131072.C025398.packed 128 cuts25398 = true := by
 decide +kernel
def pointBounds25398 : List (Nat × Nat × Nat) := [(3332941824,103100789062598,103101171192838)]
theorem point_links_checked25398 : (cuts25398.take 1).map (fun c => (3332898817-1+2*2^9*c.k,103100625139454+c.lower,103101007269603+c.upper)) = pointBounds25398 := by
 decide +kernel
def cuts25399 : List PrefixCut := [⟨16,62070713,62070748⟩,
⟨118,463707388,463707648⟩,
⟨128,502890780,502891062⟩]
theorem checked25399 : checkPrefixCuts (2^48) 3333029889 9 Manual.Count131072.C025399.packed 128 cuts25399 = true := by
 decide +kernel
def pointBounds25399 : List (Nat × Nat × Nat) := [(3333046272,103101198650281,103101580780760),(3333150720,103101600286956,103101982417660)]
theorem point_links_checked25399 : (cuts25399.take 2).map (fun c => (3333029889-1+2*2^9*c.k,103101136579568+c.lower,103101518710012+c.upper)) = pointBounds25399 := by
 decide +kernel
def cuts25400 : List PrefixCut := [⟨92,359822931,359823131⟩,
⟨128,501435489,501435771⟩]
theorem checked25400 : checkPrefixCuts (2^48) 3333160961 9 Manual.Count131072.C025400.packed 128 cuts25400 = true := by
 decide +kernel
def pointBounds25400 : List (Nat × Nat × Nat) := [(3333255168,103101999293279,103102381424205)]
theorem point_links_checked25400 : (cuts25400.take 1).map (fun c => (3333160961-1+2*2^9*c.k,103101639470348+c.lower,103102021601074+c.upper)) = pointBounds25400 := by
 decide +kernel
def cuts25401 : List PrefixCut := [⟨66,263630014,263630163⟩,
⟨128,504202410,504202694⟩]
theorem checked25401 : checkPrefixCuts (2^48) 3333292033 9 Manual.Count131072.C025401.packed 128 cuts25401 = true := by
 decide +kernel
def pointBounds25401 : List (Nat × Nat × Nat) := [(3333359616,103102404535851,103102786667008)]
theorem point_links_checked25401 : (cuts25401.take 1).map (fun c => (3333292033-1+2*2^9*c.k,103102140905837+c.lower,103102523036845+c.upper)) = pointBounds25401 := by
 decide +kernel
def cuts25402 : List PrefixCut := [⟨40,158915473,158915559⟩,
⟨128,506462332,506462615⟩]
theorem checked25402 : checkPrefixCuts (2^48) 3333423105 9 Manual.Count131072.C025402.packed 128 cuts25402 = true := by
 decide +kernel
def pointBounds25402 : List (Nat × Nat × Nat) := [(3333464064,103102804023720,103103186155098)]
theorem point_links_checked25402 : (cuts25402.take 1).map (fun c => (3333423105-1+2*2^9*c.k,103102645108247+c.lower,103103027239539+c.upper)) = pointBounds25402 := by
 decide +kernel
def cuts25403 : List PrefixCut := [⟨14,54461666,54461700⟩,
⟨116,457048617,457048873⟩,
⟨128,506273470,506273751⟩]
theorem checked25403 : checkPrefixCuts (2^48) 3333554177 9 Manual.Count131072.C025403.packed 128 cuts25403 = true := by
 decide +kernel
def pointBounds25403 : List (Nat × Nat × Nat) := [(3333568512,103103206032245,103103588163854),(3333672960,103103608619196,103103990751027)]
theorem point_links_checked25403 : (cuts25403.take 2).map (fun c => (3333554177-1+2*2^9*c.k,103103151570579+c.lower,103103533702154+c.upper)) = pointBounds25403 := by
 decide +kernel
def cuts25404 : List PrefixCut := [⟨90,355207010,355207205⟩,
⟨128,503382943,503383219⟩]
theorem checked25404 : checkPrefixCuts (2^48) 3333685249 9 Manual.Count131072.C025404.packed 128 cuts25404 = true := by
 decide +kernel
def pointBounds25404 : List (Nat × Nat × Nat) := [(3333777408,103104013051059,103104395183110)]
theorem point_links_checked25404 : (cuts25404.take 1).map (fun c => (3333685249-1+2*2^9*c.k,103103657844049+c.lower,103104039975905+c.upper)) = pointBounds25404 := by
 decide +kernel
def cuts25405 : List PrefixCut := [⟨64,252359506,252359648⟩,
⟨128,501168049,501168329⟩]
theorem checked25405 : checkPrefixCuts (2^48) 3333816321 9 Manual.Count131072.C025405.packed 128 cuts25405 = true := by
 decide +kernel
def pointBounds25405 : List (Nat × Nat × Nat) := [(3333881856,103104413586498,103104795718772)]
theorem point_links_checked25405 : (cuts25405.take 1).map (fun c => (3333816321-1+2*2^9*c.k,103104161226992+c.lower,103104543359124+c.upper)) = pointBounds25405 := by
 decide +kernel
def cuts25406 : List PrefixCut := [⟨38,148590545,148590625⟩,
⟨128,510772798,510773080⟩]
theorem checked25406 : checkPrefixCuts (2^48) 3333947393 9 Manual.Count131072.C025406.packed 128 cuts25406 = true := by
 decide +kernel
def pointBounds25406 : List (Nat × Nat × Nat) := [(3333986304,103104810985586,103105193118078)]
theorem point_links_checked25406 : (cuts25406.take 1).map (fun c => (3333947393-1+2*2^9*c.k,103104662395041+c.lower,103105044527453+c.upper)) = pointBounds25406 := by
 decide +kernel
def cuts25407 : List PrefixCut := [⟨12,46855009,46855035⟩,
⟨114,441443222,441443474⟩,
⟨128,496147678,496147959⟩]
theorem checked25407 : checkPrefixCuts (2^48) 3334078465 9 Manual.Count131072.C025407.packed 128 cuts25407 = true := by
 decide +kernel
def pointBounds25407 : List (Nat × Nat × Nat) := [(3334090752,103105220022848,103105602155568),(3334195200,103105614611061,103105996744007)]
theorem point_links_checked25407 : (cuts25407.take 2).map (fun c => (3334078465-1+2*2^9*c.k,103105173167839+c.lower,103105555300533+c.upper)) = pointBounds25407 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000168
