import PlattAssemblyKernel
import PlattCertificates.Count131072.C019280
import PlattCertificates.Count131072.C019281
import PlattCertificates.Count131072.C019282
import PlattCertificates.Count131072.C019283
import PlattCertificates.Count131072.C019284
import PlattCertificates.Count131072.C019285
import PlattCertificates.Count131072.C019286
import PlattCertificates.Count131072.C019287
import PlattCertificates.Count131072.C019288
import PlattCertificates.Count131072.C019289
import PlattCertificates.Count131072.C019290
import PlattCertificates.Count131072.C019291
import PlattCertificates.Count131072.C019292
import PlattCertificates.Count131072.C019293
import PlattCertificates.Count131072.C019294
import PlattCertificates.Count131072.C019295
import PlattCertificates.Count131072.C019296
import PlattCertificates.Count131072.C019297
import PlattCertificates.Count131072.C019298
import PlattCertificates.Count131072.C019299
import PlattCertificates.Count131072.C019300
import PlattCertificates.Count131072.C019301
import PlattCertificates.Count131072.C019302
import PlattCertificates.Count131072.C019303
import PlattCertificates.Count131072.C019304
import PlattCertificates.Count131072.C019305
import PlattCertificates.Count131072.C019306
import PlattCertificates.Count131072.C019307
import PlattCertificates.Count131072.C019308
import PlattCertificates.Count131072.C019309
import PlattCertificates.Count131072.C019310
import PlattCertificates.Count131072.C019311
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000290
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19280 : List PrefixCut := [⟨34,178269896,178270002⟩,
⟨112,594075232,594075583⟩,
⟨128,676033706,676034105⟩]
theorem checked19280 : checkPrefixCuts (2^48) 2531000321 9 Manual.Count131072.C019280.packed 128 cuts19280 = true := by
 decide +kernel
def pointBounds19280 : List (Nat × Nat × Nat) := [(2531035136,99545428400414,99545808488959),(2531115008,99545844205750,99546224294540)]
theorem point_links_checked19280 : (cuts19280.take 2).map (fun c => (2531000321-1+2*2^9*c.k,99545250130518+c.lower,99545630218957+c.upper)) = pointBounds19280 := by
 decide +kernel
def cuts19281 : List PrefixCut := [⟨62,332276890,332277084⟩,
⟨128,681781322,681781726⟩]
theorem checked19281 : checkPrefixCuts (2^48) 2531131393 9 Manual.Count131072.C019281.packed 128 cuts19281 = true := by
 decide +kernel
def pointBounds19281 : List (Nat × Nat × Nat) := [(2531194880,99546258441114,99546638530146)]
theorem point_links_checked19281 : (cuts19281.take 1).map (fun c => (2531131393-1+2*2^9*c.k,99545926164224+c.lower,99546306253062+c.upper)) = pointBounds19281 := by
 decide +kernel
def cuts19282 : List PrefixCut := [⟨12,64050709,64050748⟩,
⟨90,474256931,474257212⟩,
⟨128,672405550,672405950⟩]
theorem checked19282 : checkPrefixCuts (2^48) 2531262465 9 Manual.Count131072.C019282.packed 128 cuts19282 = true := by
 decide +kernel
def pointBounds19282 : List (Nat × Nat × Nat) := [(2531274752,99546671996255,99547052085536),(2531354624,99547082202477,99547462292000)]
theorem point_links_checked19282 : (cuts19282.take 2).map (fun c => (2531262465-1+2*2^9*c.k,99546607945546+c.lower,99546988034788+c.upper)) = pointBounds19282 := by
 decide +kernel
def cuts19283 : List PrefixCut := [⟨40,206929734,206929856⟩,
⟨118,613107194,613107558⟩,
⟨128,664809667,664810063⟩]
theorem checked19283 : checkPrefixCuts (2^48) 2531393537 9 Manual.Count131072.C019283.packed 128 cuts19283 = true := by
 decide +kernel
def pointBounds19283 : List (Nat × Nat × Nat) := [(2531434496,99547487280830,99547867370594),(2531514368,99547893458290,99548273548296)]
theorem point_links_checked19283 : (cuts19283.take 2).map (fun c => (2531393537-1+2*2^9*c.k,99547280351096+c.lower,99547660440738+c.upper)) = pointBounds19283 := by
 decide +kernel
def cuts19284 : List PrefixCut := [⟨68,357352979,357353190⟩,
⟨128,682564681,682565085⟩]
theorem checked19284 : checkPrefixCuts (2^48) 2531524609 9 Manual.Count131072.C019284.packed 128 cuts19284 = true := by
 decide +kernel
def pointBounds19284 : List (Nat × Nat × Nat) := [(2531594240,99548302513742,99548682603991)]
theorem point_links_checked19284 : (cuts19284.take 1).map (fun c => (2531524609-1+2*2^9*c.k,99547945160763+c.lower,99548325250801+c.upper)) = pointBounds19284 := by
 decide +kernel
def cuts19285 : List PrefixCut := [⟨18,96728104,96728163⟩,
⟨96,505535399,505535708⟩,
⟨128,677748735,677749146⟩]
theorem checked19285 : checkPrefixCuts (2^48) 2531655681 9 Manual.Count131072.C019285.packed 128 cuts19285 = true := by
 decide +kernel
def pointBounds19285 : List (Nat × Nat × Nat) := [(2531674112,99548724453548,99549104544049),(2531753984,99549133260843,99549513351594)]
theorem point_links_checked19285 : (cuts19285.take 2).map (fun c => (2531655681-1+2*2^9*c.k,99548627725444+c.lower,99549007815886+c.upper)) = pointBounds19285 := by
 decide +kernel
def cuts19286 : List PrefixCut := [⟨46,235469404,235469546⟩,
⟨124,646585506,646585894⟩,
⟨128,668041454,668041855⟩]
theorem checked19286 : checkPrefixCuts (2^48) 2531786753 9 Manual.Count131072.C019286.packed 128 cuts19286 = true := by
 decide +kernel
def pointBounds19286 : List (Nat × Nat × Nat) := [(2531833856,99549540943583,99549921034578),(2531913728,99549952059685,99550332150926)]
theorem point_links_checked19286 : (cuts19286.take 2).map (fun c => (2531786753-1+2*2^9*c.k,99549305474179+c.lower,99549685565032+c.upper)) = pointBounds19286 := by
 decide +kernel
def cuts19287 : List PrefixCut := [⟨74,395427979,395428206⟩,
⟨128,680346649,680347045⟩]
theorem checked19287 : checkPrefixCuts (2^48) 2531917825 9 Manual.Count131072.C019287.packed 128 cuts19287 = true := by
 decide +kernel
def pointBounds19287 : List (Nat × Nat × Nat) := [(2531993600,99550368943612,99550749035093)]
theorem point_links_checked19287 : (cuts19287.take 1).map (fun c => (2531917825-1+2*2^9*c.k,99549973515633+c.lower,99550353606887+c.upper)) = pointBounds19287 := by
 decide +kernel
def cuts19288 : List PrefixCut := [⟨24,127727829,127727903⟩,
⟨102,535803699,535804017⟩,
⟨128,668973021,668973420⟩]
theorem checked19288 : checkPrefixCuts (2^48) 2532048897 9 Manual.Count131072.C019288.packed 128 cuts19288 = true := by
 decide +kernel
def pointBounds19288 : List (Nat × Nat × Nat) := [(2532073472,99550781590111,99551161681835),(2532153344,99551189665981,99551569757949)]
theorem point_links_checked19288 : (cuts19288.take 2).map (fun c => (2532048897-1+2*2^9*c.k,99550653862282+c.lower,99551033953932+c.upper)) = pointBounds19288 := by
 decide +kernel
def cuts19289 : List PrefixCut := [⟨52,275560608,275560774⟩,
⟨128,669160729,669161134⟩]
theorem checked19289 : checkPrefixCuts (2^48) 2532179969 9 Manual.Count131072.C019289.packed 128 cuts19289 = true := by
 decide +kernel
def pointBounds19289 : List (Nat × Nat × Nat) := [(2532233216,99551598395911,99551978488126)]
theorem point_links_checked19289 : (cuts19289.take 1).map (fun c => (2532179969-1+2*2^9*c.k,99551322835303+c.lower,99551702927352+c.upper)) = pointBounds19289 := by
 decide +kernel
def cuts19290 : List PrefixCut := [⟨2,11671099,11671105⟩,
⟨80,419152585,419152832⟩,
⟨128,670682068,670682467⟩]
theorem checked19290 : checkPrefixCuts (2^48) 2532311041 9 Manual.Count131072.C019290.packed 128 cuts19290 = true := by
 decide +kernel
def pointBounds19290 : List (Nat × Nat × Nat) := [(2532313088,99552003667131,99552383759591),(2532392960,99552411148617,99552791241318)]
theorem point_links_checked19290 : (cuts19290.take 2).map (fun c => (2532311041-1+2*2^9*c.k,99551991996032+c.lower,99552372088486+c.upper)) = pointBounds19290 := by
 decide +kernel
def cuts19291 : List PrefixCut := [⟨30,157495211,157495304⟩,
⟨108,574731724,574732069⟩,
⟨128,679538921,679539328⟩]
theorem checked19291 : checkPrefixCuts (2^48) 2532442113 9 Manual.Count131072.C019291.packed 128 cuts19291 = true := by
 decide +kernel
def pointBounds19291 : List (Nat × Nat × Nat) := [(2532472832,99552820173311,99553200266257),(2532552704,99553237409824,99553617503022)]
theorem point_links_checked19291 : (cuts19291.take 2).map (fun c => (2532442113-1+2*2^9*c.k,99552662678100+c.lower,99553042770953+c.upper)) = pointBounds19291 := by
 decide +kernel
def cuts19292 : List PrefixCut := [⟨58,307748197,307748374⟩,
⟨128,681615376,681615774⟩]
theorem checked19292 : checkPrefixCuts (2^48) 2532573185 9 Manual.Count131072.C019292.packed 128 cuts19292 = true := by
 decide +kernel
def pointBounds19292 : List (Nat × Nat × Nat) := [(2532632576,99553649965218,99554030058655)]
theorem point_links_checked19292 : (cuts19292.take 1).map (fun c => (2532573185-1+2*2^9*c.k,99553342217021+c.lower,99553722310281+c.upper)) = pointBounds19292 := by
 decide +kernel
def cuts19293 : List PrefixCut := [⟨8,39564388,39564414⟩,
⟨86,455205526,455205795⟩,
⟨128,672356098,672356499⟩]
theorem checked19293 : checkPrefixCuts (2^48) 2532704257 9 Manual.Count131072.C019293.packed 128 cuts19293 = true := by
 decide +kernel
def pointBounds19293 : List (Nat × Nat × Nat) := [(2532712448,99554063396785,99554443490469),(2532792320,99554479037923,99554859131850)]
theorem point_links_checked19293 : (cuts19293.take 2).map (fun c => (2532704257-1+2*2^9*c.k,99554023832397+c.lower,99554403926055+c.upper)) = pointBounds19293 := by
 decide +kernel
def cuts19294 : List PrefixCut := [⟨36,185030707,185030817⟩,
⟨114,600089973,600090321⟩,
⟨128,672543422,672543814⟩]
theorem checked19294 : checkPrefixCuts (2^48) 2532835329 9 Manual.Count131072.C019294.packed 128 cuts19294 = true := by
 decide +kernel
def pointBounds19294 : List (Nat × Nat × Nat) := [(2532872192,99554881219202,99555261313371),(2532952064,99555296278468,99555676372875)]
theorem point_links_checked19294 : (cuts19294.take 2).map (fun c => (2532835329-1+2*2^9*c.k,99554696188495+c.lower,99555076282554+c.upper)) = pointBounds19294 := by
 decide +kernel
def cuts19295 : List PrefixCut := [⟨64,339370163,339370362⟩,
⟨128,680176137,680176538⟩]
theorem checked19295 : checkPrefixCuts (2^48) 2532966401 9 Manual.Count131072.C019295.packed 128 cuts19295 = true := by
 decide +kernel
def pointBounds19295 : List (Nat × Nat × Nat) := [(2533031936,99555708102080,99556088196730)]
theorem point_links_checked19295 : (cuts19295.take 1).map (fun c => (2532966401-1+2*2^9*c.k,99555368731917+c.lower,99555748826368+c.upper)) = pointBounds19295 := by
 decide +kernel
def cuts19296 : List PrefixCut := [⟨14,74560538,74560584⟩,
⟨92,486136022,486136314⟩,
⟨128,673029639,673030044⟩]
theorem checked19296 : checkPrefixCuts (2^48) 2533097473 9 Manual.Count131072.C019296.packed 128 cuts19296 = true := by
 decide +kernel
def pointBounds19296 : List (Nat × Nat × Nat) := [(2533111808,99556123468592,99556503563490),(2533191680,99556535044076,99556915139220)]
theorem point_links_checked19296 : (cuts19296.take 2).map (fun c => (2533097473-1+2*2^9*c.k,99556048908054+c.lower,99556429002906+c.upper)) = pointBounds19296 := by
 decide +kernel
def cuts19297 : List PrefixCut := [⟨42,220335443,220335573⟩,
⟨120,637662613,637662992⟩,
⟨128,679439047,679439451⟩]
theorem checked19297 : checkPrefixCuts (2^48) 2533228545 9 Manual.Count131072.C019297.packed 128 cuts19297 = true := by
 decide +kernel
def pointBounds19297 : List (Nat × Nat × Nat) := [(2533271552,99556942273136,99557322368523),(2533351424,99557359600306,99557739695942)]
theorem point_links_checked19297 : (cuts19297.take 2).map (fun c => (2533228545-1+2*2^9*c.k,99556721937693+c.lower,99557102032950+c.upper)) = pointBounds19297 := by
 decide +kernel
def cuts19298 : List PrefixCut := [⟨70,373982071,373982293⟩,
⟨128,676070850,676071254⟩]
theorem checked19298 : checkPrefixCuts (2^48) 2533359617 9 Manual.Count131072.C019298.packed 128 cuts19298 = true := by
 decide +kernel
def pointBounds19298 : List (Nat × Nat × Nat) := [(2533431296,99557775358811,99558155454694)]
theorem point_links_checked19298 : (cuts19298.take 1).map (fun c => (2533359617-1+2*2^9*c.k,99557401376740+c.lower,99557781472401+c.upper)) = pointBounds19298 := by
 decide +kernel
def cuts19299 : List PrefixCut := [⟨20,106657112,106657178⟩,
⟨98,511946140,511946447⟩,
⟨128,670258702,670259106⟩]
theorem checked19299 : checkPrefixCuts (2^48) 2533490689 9 Manual.Count131072.C019299.packed 128 cuts19299 = true := by
 decide +kernel
def pointBounds19299 : List (Nat × Nat × Nat) := [(2533511168,99558184104702,99558564200833),(2533591040,99558589393730,99558969490102)]
theorem point_links_checked19299 : (cuts19299.take 2).map (fun c => (2533490689-1+2*2^9*c.k,99558077447590+c.lower,99558457543655+c.upper)) = pointBounds19299 := by
 decide +kernel
def cuts19300 : List PrefixCut := [⟨48,250740966,250741115⟩,
⟨126,660225869,660226260⟩,
⟨128,671668156,671668554⟩]
theorem checked19300 : checkPrefixCuts (2^48) 2533621761 9 Manual.Count131072.C019300.packed 128 cuts19300 = true := by
 decide +kernel
def pointBounds19300 : List (Nat × Nat × Nat) := [(2533670912,99558998447258,99559378543876),(2533750784,99559407932161,99559788029021)]
theorem point_links_checked19300 : (cuts19300.take 2).map (fun c => (2533621761-1+2*2^9*c.k,99558747706292+c.lower,99559127802761+c.upper)) = pointBounds19300 := by
 decide +kernel
def cuts19301 : List PrefixCut := [⟨76,398696264,398696497⟩,
⟨128,674521616,674522010⟩]
theorem checked19301 : checkPrefixCuts (2^48) 2533752833 9 Manual.Count131072.C019301.packed 128 cuts19301 = true := by
 decide +kernel
def pointBounds19301 : List (Nat × Nat × Nat) := [(2533830656,99559818070712,99560198167812)]
theorem point_links_checked19301 : (cuts19301.take 1).map (fun c => (2533752833-1+2*2^9*c.k,99559419374448+c.lower,99559799471315+c.upper)) = pointBounds19301 := by
 decide +kernel
def cuts19302 : List PrefixCut := [⟨26,137521722,137521806⟩,
⟨104,542191450,542191773⟩,
⟨128,667377656,667378054⟩]
theorem checked19302 : checkPrefixCuts (2^48) 2533883905 9 Manual.Count131072.C019302.packed 128 cuts19302 = true := by
 decide +kernel
def pointBounds19302 : List (Nat × Nat × Nat) := [(2533910528,99560231417786,99560611515131),(2533990400,99560636087514,99561016185098)]
theorem point_links_checked19302 : (cuts19302.take 2).map (fun c => (2533883905-1+2*2^9*c.k,99560093896064+c.lower,99560473993325+c.upper)) = pointBounds19302 := by
 decide +kernel
def cuts19303 : List PrefixCut := [⟨54,284024892,284025064⟩,
⟨128,676562242,676562644⟩]
theorem checked19303 : checkPrefixCuts (2^48) 2534014977 9 Manual.Count131072.C019303.packed 128 cuts19303 = true := by
 decide +kernel
def pointBounds19303 : List (Nat × Nat × Nat) := [(2534070272,99561045298612,99561425396443)]
theorem point_links_checked19303 : (cuts19303.take 1).map (fun c => (2534014977-1+2*2^9*c.k,99560761273720+c.lower,99561141371379+c.upper)) = pointBounds19303 := by
 decide +kernel
def cuts19304 : List PrefixCut := [⟨4,20548464,20548477⟩,
⟨82,430733529,430733789⟩,
⟨128,671751424,671751827⟩]
theorem checked19304 : checkPrefixCuts (2^48) 2534146049 9 Manual.Count131072.C019304.packed 128 cuts19304 = true := by
 decide +kernel
def pointBounds19304 : List (Nat × Nat × Nat) := [(2534150144,99561458384426,99561838482500),(2534230016,99561868569491,99562248667812)]
theorem point_links_checked19304 : (cuts19304.take 2).map (fun c => (2534146049-1+2*2^9*c.k,99561437835962+c.lower,99561817934023+c.upper)) = pointBounds19304 := by
 decide +kernel
def cuts19305 : List PrefixCut := [⟨32,170375888,170375990⟩,
⟨110,582978372,582978723⟩,
⟨128,674271161,674271565⟩]
theorem checked19305 : checkPrefixCuts (2^48) 2534277121 9 Manual.Count131072.C019305.packed 128 cuts19305 = true := by
 decide +kernel
def pointBounds19305 : List (Nat × Nat × Nat) := [(2534309888,99562279963274,99562660061840),(2534389760,99562692565758,99563072664573)]
theorem point_links_checked19305 : (cuts19305.take 2).map (fun c => (2534277121-1+2*2^9*c.k,99562109587386+c.lower,99562489685850+c.upper)) = pointBounds19305 := by
 decide +kernel
def cuts19306 : List PrefixCut := [⟨60,317187453,317187640⟩,
⟨128,669460814,669461212⟩]
theorem checked19306 : checkPrefixCuts (2^48) 2534408193 9 Manual.Count131072.C019306.packed 128 cuts19306 = true := by
 decide +kernel
def pointBounds19306 : List (Nat × Nat × Nat) := [(2534469632,99563101046000,99563481145055)]
theorem point_links_checked19306 : (cuts19306.take 1).map (fun c => (2534408193-1+2*2^9*c.k,99562783858547+c.lower,99563163957415+c.upper)) = pointBounds19306 := by
 decide +kernel
def cuts19307 : List PrefixCut := [⟨10,53417652,53417685⟩,
⟨88,458318528,458318806⟩,
⟨128,666649800,666650199⟩]
theorem checked19307 : checkPrefixCuts (2^48) 2534539265 9 Manual.Count131072.C019307.packed 128 cuts19307 = true := by
 decide +kernel
def pointBounds19307 : List (Nat × Nat × Nat) := [(2534549504,99563506737013,99563886836312),(2534629376,99563911637889,99564291737433)]
theorem point_links_checked19307 : (cuts19307.take 2).map (fun c => (2534539265-1+2*2^9*c.k,99563453319361+c.lower,99563833418627+c.upper)) = pointBounds19307 := by
 decide +kernel
def cuts19308 : List PrefixCut := [⟨38,200554571,200554687⟩,
⟨116,607872885,607873252⟩,
⟨128,671945523,671945929⟩]
theorem checked19308 : checkPrefixCuts (2^48) 2534670337 9 Manual.Count131072.C019308.packed 128 cuts19308 = true := by
 decide +kernel
def pointBounds19308 : List (Nat × Nat × Nat) := [(2534709248,99564320523732,99564700623513),(2534789120,99564727842046,99565107942078)]
theorem point_links_checked19308 : (cuts19308.take 2).map (fun c => (2534670337-1+2*2^9*c.k,99564119969161+c.lower,99564500068826+c.upper)) = pointBounds19308 := by
 decide +kernel
def cuts19309 : List PrefixCut := [⟨66,352782633,352782845⟩,
⟨128,679350718,679351120⟩]
theorem checked19309 : checkPrefixCuts (2^48) 2534801409 9 Manual.Count131072.C019309.packed 128 cuts19309 = true := by
 decide +kernel
def pointBounds19309 : List (Nat × Nat × Nat) := [(2534868992,99565144697317,99565524797600)]
theorem point_links_checked19309 : (cuts19309.take 1).map (fun c => (2534801409-1+2*2^9*c.k,99564791914684+c.lower,99565172014755+c.upper)) = pointBounds19309 := by
 decide +kernel
def cuts19310 : List PrefixCut := [⟨16,84499968,84500019⟩,
⟨94,502217141,502217444⟩,
⟨128,677761020,677761429⟩]
theorem checked19310 : checkPrefixCuts (2^48) 2534932481 9 Manual.Count131072.C019310.packed 128 cuts19310 = true := by
 decide +kernel
def pointBounds19310 : List (Nat × Nat × Nat) := [(2534948864,99565555765370,99565935865894),(2535028736,99565973482543,99566353583319)]
theorem point_links_checked19310 : (cuts19310.take 2).map (fun c => (2534932481-1+2*2^9*c.k,99565471265402+c.lower,99565851365875+c.upper)) = pointBounds19310 := by
 decide +kernel
def cuts19311 : List PrefixCut := [⟨44,228281175,228281311⟩,
⟨122,636867737,636868120⟩,
⟨128,668066343,668066743⟩]
theorem checked19311 : checkPrefixCuts (2^48) 2535063553 9 Manual.Count131072.C019311.packed 128 cuts19311 = true := by
 decide +kernel
def pointBounds19311 : List (Nat × Nat × Nat) := [(2535108608,99566377307597,99566757408615),(2535188480,99566785894159,99567165995424)]
theorem point_links_checked19311 : (cuts19311.take 2).map (fun c => (2535063553-1+2*2^9*c.k,99566149026422+c.lower,99566529127304+c.upper)) = pointBounds19311 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000290
