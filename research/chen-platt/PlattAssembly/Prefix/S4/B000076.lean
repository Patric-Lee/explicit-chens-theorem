import PlattAssemblyKernel
import PlattCertificates.Count131072.C032432
import PlattCertificates.Count131072.C032433
import PlattCertificates.Count131072.C032434
import PlattCertificates.Count131072.C032435
import PlattCertificates.Count131072.C032436
import PlattCertificates.Count131072.C032437
import PlattCertificates.Count131072.C032438
import PlattCertificates.Count131072.C032439
import PlattCertificates.Count131072.C032440
import PlattCertificates.Count131072.C032441
import PlattCertificates.Count131072.C032442
import PlattCertificates.Count131072.C032443
import PlattCertificates.Count131072.C032444
import PlattCertificates.Count131072.C032445
import PlattCertificates.Count131072.C032446
import PlattCertificates.Count131072.C032447
import PlattCertificates.Count131072.C032448
import PlattCertificates.Count131072.C032449
import PlattCertificates.Count131072.C032450
import PlattCertificates.Count131072.C032451
import PlattCertificates.Count131072.C032452
import PlattCertificates.Count131072.C032453
import PlattCertificates.Count131072.C032454
import PlattCertificates.Count131072.C032455
import PlattCertificates.Count131072.C032456
import PlattCertificates.Count131072.C032457
import PlattCertificates.Count131072.C032458
import PlattCertificates.Count131072.C032459
import PlattCertificates.Count131072.C032460
import PlattCertificates.Count131072.C032461
import PlattCertificates.Count131072.C032462
import PlattCertificates.Count131072.C032463
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000076
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts32432 : List PrefixCut := [⟨128,394468727,394468953⟩]
theorem checked32432 : checkPrefixCuts (2^48) 4254859265 9 Manual.Count131072.C032432.packed 128 cuts32432 = true := by
 decide +kernel
def cuts32433 : List PrefixCut := [⟨1,3109130,3109132⟩,
⟨128,386121593,386121814⟩]
theorem checked32433 : checkPrefixCuts (2^48) 4254990337 9 Manual.Count131072.C032433.packed 128 cuts32433 = true := by
 decide +kernel
def pointBounds32433 : List (Nat × Nat × Nat) := [(4254991360,106218669890134,106219053770396)]
theorem point_links_checked32433 : (cuts32433.take 1).map (fun c => (4254990337-1+2*2^9*c.k,106218666781004+c.lower,106219050661264+c.upper)) = pointBounds32433 := by
 decide +kernel
def cuts32434 : List PrefixCut := [⟨3,8136407,8136413⟩,
⟨128,383794485,383794705⟩]
theorem checked32434 : checkPrefixCuts (2^48) 4255121409 9 Manual.Count131072.C032434.packed 128 cuts32434 = true := by
 decide +kernel
def pointBounds32434 : List (Nat × Nat × Nat) := [(4255124480,106219061039004,106219444919491)]
theorem point_links_checked32434 : (cuts32434.take 1).map (fun c => (4255121409-1+2*2^9*c.k,106219052902597+c.lower,106219436783078+c.upper)) = pointBounds32434 := by
 decide +kernel
def cuts32435 : List PrefixCut := [⟨5,14883208,14883217⟩,
⟨128,385237917,385238132⟩]
theorem checked32435 : checkPrefixCuts (2^48) 4255252481 9 Manual.Count131072.C032435.packed 128 cuts32435 = true := by
 decide +kernel
def pointBounds32435 : List (Nat × Nat × Nat) := [(4255257600,106219451580290,106219835461000)]
theorem point_links_checked32435 : (cuts32435.take 1).map (fun c => (4255252481-1+2*2^9*c.k,106219436697082+c.lower,106219820577783+c.upper)) = pointBounds32435 := by
 decide +kernel
def cuts32436 : List PrefixCut := [⟨7,23349377,23349389⟩,
⟨128,398454968,398455199⟩]
theorem checked32436 : checkPrefixCuts (2^48) 4255383553 9 Manual.Count131072.C032436.packed 128 cuts32436 = true := by
 decide +kernel
def pointBounds32436 : List (Nat × Nat × Nat) := [(4255390720,106219845284376,106220229165304)]
theorem point_links_checked32436 : (cuts32436.take 1).map (fun c => (4255383553-1+2*2^9*c.k,106219821934999+c.lower,106220205815915+c.upper)) = pointBounds32436 := by
 decide +kernel
def cuts32437 : List PrefixCut := [⟨9,27052688,27052703⟩,
⟨128,395532392,395532615⟩]
theorem checked32437 : checkPrefixCuts (2^48) 4255514625 9 Manual.Count131072.C032437.packed 128 cuts32437 = true := by
 decide +kernel
def pointBounds32437 : List (Nat × Nat × Nat) := [(4255523840,106220247442655,106220631323817)]
theorem point_links_checked32437 : (cuts32437.take 1).map (fun c => (4255514625-1+2*2^9*c.k,106220220389967+c.lower,106220604271114+c.upper)) = pointBounds32437 := by
 decide +kernel
def cuts32438 : List PrefixCut := [⟨11,33599849,33599868⟩,
⟨128,388377067,388377290⟩]
theorem checked32438 : checkPrefixCuts (2^48) 4255645697 9 Manual.Count131072.C032438.packed 128 cuts32438 = true := by
 decide +kernel
def pointBounds32438 : List (Nat × Nat × Nat) := [(4255656960,106220649522208,106221033403597)]
theorem point_links_checked32438 : (cuts32438.take 1).map (fun c => (4255645697-1+2*2^9*c.k,106220615922359+c.lower,106220999803729+c.upper)) = pointBounds32438 := by
 decide +kernel
def cuts32439 : List PrefixCut := [⟨13,39749771,39749795⟩,
⟨128,388828088,388828309⟩]
theorem checked32439 : checkPrefixCuts (2^48) 4255776769 9 Manual.Count131072.C032439.packed 128 cuts32439 = true := by
 decide +kernel
def pointBounds32439 : List (Nat × Nat × Nat) := [(4255790080,106221044049197,106221427930814)]
theorem point_links_checked32439 : (cuts32439.take 1).map (fun c => (4255776769-1+2*2^9*c.k,106221004299426+c.lower,106221388181019+c.upper)) = pointBounds32439 := by
 decide +kernel
def cuts32440 : List PrefixCut := [⟨15,48081839,48081864⟩,
⟨128,392784348,392784568⟩]
theorem checked32440 : checkPrefixCuts (2^48) 4255907841 9 Manual.Count131072.C032440.packed 128 cuts32440 = true := by
 decide +kernel
def pointBounds32440 : List (Nat × Nat × Nat) := [(4255923200,106221441209353,106221825091192)]
theorem point_links_checked32440 : (cuts32440.take 1).map (fun c => (4255907841-1+2*2^9*c.k,106221393127514+c.lower,106221777009328+c.upper)) = pointBounds32440 := by
 decide +kernel
def cuts32441 : List PrefixCut := [⟨17,51320979,51321007⟩,
⟨128,389796148,389796367⟩]
theorem checked32441 : checkPrefixCuts (2^48) 4256038913 9 Manual.Count131072.C032441.packed 128 cuts32441 = true := by
 decide +kernel
def pointBounds32441 : List (Nat × Nat × Nat) := [(4256056320,106221837232841,106222221114903)]
theorem point_links_checked32441 : (cuts32441.take 1).map (fun c => (4256038913-1+2*2^9*c.k,106221785911862+c.lower,106222169793896+c.upper)) = pointBounds32441 := by
 decide +kernel
def cuts32442 : List PrefixCut := [⟨19,57668172,57668204⟩,
⟨128,387866284,387866500⟩]
theorem checked32442 : checkPrefixCuts (2^48) 4256169985 9 Manual.Count131072.C032442.packed 128 cuts32442 = true := by
 decide +kernel
def pointBounds32442 : List (Nat × Nat × Nat) := [(4256189440,106222233376182,106222617258467)]
theorem point_links_checked32442 : (cuts32442.take 1).map (fun c => (4256169985-1+2*2^9*c.k,106222175708010+c.lower,106222559590263+c.upper)) = pointBounds32442 := by
 decide +kernel
def cuts32443 : List PrefixCut := [⟨21,64411760,64411797⟩,
⟨128,388515654,388515865⟩]
theorem checked32443 : checkPrefixCuts (2^48) 4256301057 9 Manual.Count131072.C032443.packed 128 cuts32443 = true := by
 decide +kernel
def pointBounds32443 : List (Nat × Nat × Nat) := [(4256322560,106222627986054,106223011868560)]
theorem point_links_checked32443 : (cuts32443.take 1).map (fun c => (4256301057-1+2*2^9*c.k,106222563574294+c.lower,106222947456763+c.upper)) = pointBounds32443 := by
 decide +kernel
def cuts32444 : List PrefixCut := [⟨23,70096863,70096902⟩,
⟨128,391545593,391545814⟩]
theorem checked32444 : checkPrefixCuts (2^48) 4256432129 9 Manual.Count131072.C032444.packed 128 cuts32444 = true := by
 decide +kernel
def pointBounds32444 : List (Nat × Nat × Nat) := [(4256455680,106223022186811,106223406069530)]
theorem point_links_checked32444 : (cuts32444.take 1).map (fun c => (4256432129-1+2*2^9*c.k,106222952089948+c.lower,106223335972628+c.upper)) = pointBounds32444 := by
 decide +kernel
def cuts32445 : List PrefixCut := [⟨25,76442890,76442936⟩,
⟨128,389880388,389880608⟩]
theorem checked32445 : checkPrefixCuts (2^48) 4256563201 9 Manual.Count131072.C032445.packed 128 cuts32445 = true := by
 decide +kernel
def pointBounds32445 : List (Nat × Nat × Nat) := [(4256588800,106223420078431,106223803961378)]
theorem point_links_checked32445 : (cuts32445.take 1).map (fun c => (4256563201-1+2*2^9*c.k,106223343635541+c.lower,106223727518442+c.upper)) = pointBounds32445 := by
 decide +kernel
def cuts32446 : List PrefixCut := [⟨27,83648145,83648191⟩,
⟨128,396084055,396084281⟩]
theorem checked32446 : checkPrefixCuts (2^48) 4256694273 9 Manual.Count131072.C032446.packed 128 cuts32446 = true := by
 decide +kernel
def pointBounds32446 : List (Nat × Nat × Nat) := [(4256721920,106223817164074,106224201047241)]
theorem point_links_checked32446 : (cuts32446.take 1).map (fun c => (4256694273-1+2*2^9*c.k,106223733515929+c.lower,106224117399050+c.upper)) = pointBounds32446 := by
 decide +kernel
def cuts32447 : List PrefixCut := [⟨29,86554961,86555013⟩,
⟨128,388467743,388467965⟩]
theorem checked32447 : checkPrefixCuts (2^48) 4256825345 9 Manual.Count131072.C032447.packed 128 cuts32447 = true := by
 decide +kernel
def pointBounds32447 : List (Nat × Nat × Nat) := [(4256855040,106224216154945,106224600038344)]
theorem point_links_checked32447 : (cuts32447.take 1).map (fun c => (4256825345-1+2*2^9*c.k,106224129599984+c.lower,106224513483331+c.upper)) = pointBounds32447 := by
 decide +kernel
def cuts32448 : List PrefixCut := [⟨31,95676968,95677020⟩,
⟨128,389117067,389117290⟩]
theorem checked32448 : checkPrefixCuts (2^48) 4256956417 9 Manual.Count131072.C032448.packed 128 cuts32448 = true := by
 decide +kernel
def pointBounds32448 : List (Nat × Nat × Nat) := [(4256988160,106224613744695,106224997628316)]
theorem point_links_checked32448 : (cuts32448.take 1).map (fun c => (4256956417-1+2*2^9*c.k,106224518067727+c.lower,106224901951296+c.upper)) = pointBounds32448 := by
 decide +kernel
def cuts32449 : List PrefixCut := [⟨33,99574998,99575058⟩,
⟨128,388311608,388311834⟩]
theorem checked32449 : checkPrefixCuts (2^48) 4257087489 9 Manual.Count131072.C032449.packed 128 cuts32449 = true := by
 decide +kernel
def pointBounds32449 : List (Nat × Nat × Nat) := [(4257121280,106225006759792,106225390643644)]
theorem point_links_checked32449 : (cuts32449.take 1).map (fun c => (4257087489-1+2*2^9*c.k,106224907184794+c.lower,106225291068586+c.upper)) = pointBounds32449 := by
 decide +kernel
def cuts32450 : List PrefixCut := [⟨35,107836521,107836580⟩,
⟨128,393258412,393258631⟩]
theorem checked32450 : checkPrefixCuts (2^48) 4257218561 9 Manual.Count131072.C032450.packed 128 cuts32450 = true := by
 decide +kernel
def pointBounds32450 : List (Nat × Nat × Nat) := [(4257254400,106225403332923,106225787217000)]
theorem point_links_checked32450 : (cuts32450.take 1).map (fun c => (4257218561-1+2*2^9*c.k,106225295496402+c.lower,106225679380420+c.upper)) = pointBounds32450 := by
 decide +kernel
def cuts32451 : List PrefixCut := [⟨37,112659550,112659615⟩,
⟨128,392452906,392453129⟩]
theorem checked32451 : checkPrefixCuts (2^48) 4257349633 9 Manual.Count131072.C032451.packed 128 cuts32451 = true := by
 decide +kernel
def pointBounds32451 : List (Nat × Nat × Nat) := [(4257387520,106225801414364,106226185298666)]
theorem point_links_checked32451 : (cuts32451.take 1).map (fun c => (4257349633-1+2*2^9*c.k,106225688754814+c.lower,106226072639051+c.upper)) = pointBounds32451 := by
 decide +kernel
def cuts32452 : List PrefixCut := [⟨39,120126789,120126857⟩,
⟨128,389928607,389928819⟩]
theorem checked32452 : checkPrefixCuts (2^48) 4257480705 9 Manual.Count131072.C032452.packed 128 cuts32452 = true := by
 decide +kernel
def pointBounds32452 : List (Nat × Nat × Nat) := [(4257520640,106226201334509,106226585219037)]
theorem point_links_checked32452 : (cuts32452.take 1).map (fun c => (4257480705-1+2*2^9*c.k,106226081207720+c.lower,106226465092180+c.upper)) = pointBounds32452 := by
 decide +kernel
def cuts32453 : List PrefixCut := [⟨41,125940808,125940881⟩,
⟨128,393684852,393685077⟩]
theorem checked32453 : checkPrefixCuts (2^48) 4257611777 9 Manual.Count131072.C032453.packed 128 cuts32453 = true := by
 decide +kernel
def pointBounds32453 : List (Nat × Nat × Nat) := [(4257653760,106226597077135,106226980961880)]
theorem point_links_checked32453 : (cuts32453.take 1).map (fun c => (4257611777-1+2*2^9*c.k,106226471136327+c.lower,106226855020999+c.upper)) = pointBounds32453 := by
 decide +kernel
def cuts32454 : List PrefixCut := [⟨43,133274960,133275033⟩,
⟨128,388979120,388979331⟩]
theorem checked32454 : checkPrefixCuts (2^48) 4257742849 9 Manual.Count131072.C032454.packed 128 cuts32454 = true := by
 decide +kernel
def pointBounds32454 : List (Nat × Nat × Nat) := [(4257786880,106226998096139,106227381981109)]
theorem point_links_checked32454 : (cuts32454.take 1).map (fun c => (4257742849-1+2*2^9*c.k,106226864821179+c.lower,106227248706076+c.upper)) = pointBounds32454 := by
 decide +kernel
def cuts32455 : List PrefixCut := [⟨45,140939169,140939244⟩,
⟨128,393131794,393132012⟩]
theorem checked32455 : checkPrefixCuts (2^48) 4257873921 9 Manual.Count131072.C032455.packed 128 cuts32455 = true := by
 decide +kernel
def pointBounds32455 : List (Nat × Nat × Nat) := [(4257920000,106227394739468,106227778624651)]
theorem point_links_checked32455 : (cuts32455.take 1).map (fun c => (4257873921-1+2*2^9*c.k,106227253800299+c.lower,106227637685407+c.upper)) = pointBounds32455 := by
 decide +kernel
def cuts32456 : List PrefixCut := [⟨47,147809662,147809745⟩,
⟨128,394045156,394045377⟩]
theorem checked32456 : checkPrefixCuts (2^48) 4258004993 9 Manual.Count131072.C032456.packed 128 cuts32456 = true := by
 decide +kernel
def pointBounds32456 : List (Nat × Nat × Nat) := [(4258053120,106227794741755,106228178627164)]
theorem point_links_checked32456 : (cuts32456.take 1).map (fun c => (4258004993-1+2*2^9*c.k,106227646932093+c.lower,106228030817419+c.upper)) = pointBounds32456 := by
 decide +kernel
def cuts32457 : List PrefixCut := [⟨49,152101735,152101819⟩,
⟨128,391388942,391389158⟩]
theorem checked32457 : checkPrefixCuts (2^48) 4258136065 9 Manual.Count131072.C032457.packed 128 cuts32457 = true := by
 decide +kernel
def pointBounds32457 : List (Nat × Nat × Nat) := [(4258186240,106228193078984,106228576964615)]
theorem point_links_checked32457 : (cuts32457.take 1).map (fun c => (4258136065-1+2*2^9*c.k,106228040977249+c.lower,106228424862796+c.upper)) = pointBounds32457 := by
 decide +kernel
def cuts32458 : List PrefixCut := [⟨51,156459663,156459750⟩,
⟨128,390914152,390914377⟩]
theorem checked32458 : checkPrefixCuts (2^48) 4258267137 9 Manual.Count131072.C032458.packed 128 cuts32458 = true := by
 decide +kernel
def pointBounds32458 : List (Nat × Nat × Nat) := [(4258319360,106228588825854,106228972711704)]
theorem point_links_checked32458 : (cuts32458.take 1).map (fun c => (4258267137-1+2*2^9*c.k,106228432366191+c.lower,106228816251954+c.upper)) = pointBounds32458 := by
 decide +kernel
def cuts32459 : List PrefixCut := [⟨53,165113695,165113784⟩,
⟨128,393678281,393678502⟩]
theorem checked32459 : checkPrefixCuts (2^48) 4258398209 9 Manual.Count131072.C032459.packed 128 cuts32459 = true := by
 decide +kernel
def pointBounds32459 : List (Nat × Nat × Nat) := [(4258452480,106228988394038,106229372280115)]
theorem point_links_checked32459 : (cuts32459.take 1).map (fun c => (4258398209-1+2*2^9*c.k,106228823280343+c.lower,106229207166331+c.upper)) = pointBounds32459 := by
 decide +kernel
def cuts32460 : List PrefixCut := [⟨55,164910286,164910377⟩,
⟨128,390096929,390097145⟩]
theorem checked32460 : checkPrefixCuts (2^48) 4258529281 9 Manual.Count131072.C032460.packed 128 cuts32460 = true := by
 decide +kernel
def pointBounds32460 : List (Nat × Nat × Nat) := [(4258585600,106229381868910,106229765755210)]
theorem point_links_checked32460 : (cuts32460.take 1).map (fun c => (4258529281-1+2*2^9*c.k,106229216958624+c.lower,106229600844833+c.upper)) = pointBounds32460 := by
 decide +kernel
def cuts32461 : List PrefixCut := [⟨57,167879409,167879510⟩,
⟨128,382418045,382418268⟩]
theorem checked32461 : checkPrefixCuts (2^48) 4258660353 9 Manual.Count131072.C032461.packed 128 cuts32461 = true := by
 decide +kernel
def pointBounds32461 : List (Nat × Nat × Nat) := [(4258718720,106229774934962,106230158821488)]
theorem point_links_checked32461 : (cuts32461.take 1).map (fun c => (4258660353-1+2*2^9*c.k,106229607055553+c.lower,106229990941978+c.upper)) = pointBounds32461 := by
 decide +kernel
def cuts32462 : List PrefixCut := [⟨59,178779415,178779512⟩,
⟨128,386041374,386041592⟩]
theorem checked32462 : checkPrefixCuts (2^48) 4258791425 9 Manual.Count131072.C032462.packed 128 cuts32462 = true := by
 decide +kernel
def pointBounds32462 : List (Nat × Nat × Nat) := [(4258851840,106230168253013,106230552139758)]
theorem point_links_checked32462 : (cuts32462.take 1).map (fun c => (4258791425-1+2*2^9*c.k,106229989473598+c.lower,106230373360246+c.upper)) = pointBounds32462 := by
 decide +kernel
def cuts32463 : List PrefixCut := [⟨61,184788051,184788157⟩,
⟨128,389069590,389069809⟩]
theorem checked32463 : checkPrefixCuts (2^48) 4258922497 9 Manual.Count131072.C032463.packed 128 cuts32463 = true := by
 decide +kernel
def pointBounds32463 : List (Nat × Nat × Nat) := [(4258984960,106230560303023,106230944189995)]
theorem point_links_checked32463 : (cuts32463.take 1).map (fun c => (4258922497-1+2*2^9*c.k,106230375514972+c.lower,106230759401838+c.upper)) = pointBounds32463 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000076
