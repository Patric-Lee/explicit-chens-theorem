import PlattAssemblyKernel
import PlattCertificates.Count131072.C024384
import PlattCertificates.Count131072.C024385
import PlattCertificates.Count131072.C024386
import PlattCertificates.Count131072.C024387
import PlattCertificates.Count131072.C024388
import PlattCertificates.Count131072.C024389
import PlattCertificates.Count131072.C024390
import PlattCertificates.Count131072.C024391
import PlattCertificates.Count131072.C024392
import PlattCertificates.Count131072.C024393
import PlattCertificates.Count131072.C024394
import PlattCertificates.Count131072.C024395
import PlattCertificates.Count131072.C024396
import PlattCertificates.Count131072.C024397
import PlattCertificates.Count131072.C024398
import PlattCertificates.Count131072.C024399
import PlattCertificates.Count131072.C024400
import PlattCertificates.Count131072.C024401
import PlattCertificates.Count131072.C024402
import PlattCertificates.Count131072.C024403
import PlattCertificates.Count131072.C024404
import PlattCertificates.Count131072.C024405
import PlattCertificates.Count131072.C024406
import PlattCertificates.Count131072.C024407
import PlattCertificates.Count131072.C024408
import PlattCertificates.Count131072.C024409
import PlattCertificates.Count131072.C024410
import PlattCertificates.Count131072.C024411
import PlattCertificates.Count131072.C024412
import PlattCertificates.Count131072.C024413
import PlattCertificates.Count131072.C024414
import PlattCertificates.Count131072.C024415
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000137
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24384 : List PrefixCut := [⟨20,83035033,83035080⟩,
⟨118,487999094,487999363⟩,
⟨128,530042858,530043150⟩]
theorem checked24384 : checkPrefixCuts (2^48) 3199991809 9 Manual.Count131072.C024384.packed 128 cuts24384 = true := by
 decide +kernel
def pointBounds24384 : List (Nat × Nat × Nat) := [(3200012288,102577848149102,102578229985474),(3200112640,102578253113163,102578634949757)]
theorem point_links_checked24384 : (cuts24384.take 2).map (fun c => (3199991809-1+2*2^9*c.k,102577765114069+c.lower,102578146950394+c.upper)) = pointBounds24384 := by
 decide +kernel
def cuts24385 : List PrefixCut := [⟨88,358861666,358861864⟩,
⟨128,524392007,524392301⟩]
theorem checked24385 : checkPrefixCuts (2^48) 3200122881 9 Manual.Count131072.C024385.packed 128 cuts24385 = true := by
 decide +kernel
def pointBounds24385 : List (Nat × Nat × Nat) := [(3200212992,102578654018593,102579035855408)]
theorem point_links_checked24385 : (cuts24385.take 1).map (fun c => (3200122881-1+2*2^9*c.k,102578295156927+c.lower,102578676993544+c.upper)) = pointBounds24385 := by
 decide +kernel
def cuts24386 : List PrefixCut := [⟨58,240551780,240551919⟩,
⟨128,527624815,527625116⟩]
theorem checked24386 : checkPrefixCuts (2^48) 3200253953 9 Manual.Count131072.C024386.packed 128 cuts24386 = true := by
 decide +kernel
def pointBounds24386 : List (Nat × Nat × Nat) := [(3200313344,102579060100714,102579441937764)]
theorem point_links_checked24386 : (cuts24386.take 1).map (fun c => (3200253953-1+2*2^9*c.k,102578819548934+c.lower,102579201385845+c.upper)) = pointBounds24386 := by
 decide +kernel
def cuts24387 : List PrefixCut := [⟨28,112927705,112927769⟩,
⟨126,518808520,518808808⟩,
⟨128,526547834,526548127⟩]
theorem checked24387 : checkPrefixCuts (2^48) 3200385025 9 Manual.Count131072.C024387.packed 128 cuts24387 = true := by
 decide +kernel
def pointBounds24387 : List (Nat × Nat × Nat) := [(3200413696,102579460101454,102579841938730),(3200514048,102579865982269,102580247819769)]
theorem point_links_checked24387 : (cuts24387.take 2).map (fun c => (3200385025-1+2*2^9*c.k,102579347173749+c.lower,102579729010961+c.upper)) = pointBounds24387 := by
 decide +kernel
def cuts24388 : List PrefixCut := [⟨96,393907305,393907528⟩,
⟨128,522304924,522305222⟩]
theorem checked24388 : checkPrefixCuts (2^48) 3200516097 9 Manual.Count131072.C024388.packed 128 cuts24388 = true := by
 decide +kernel
def pointBounds24388 : List (Nat × Nat × Nat) := [(3200614400,102580267628888,102580649466616)]
theorem point_links_checked24388 : (cuts24388.take 1).map (fun c => (3200516097-1+2*2^9*c.k,102579873721583+c.lower,102580255559088+c.upper)) = pointBounds24388 := by
 decide +kernel
def cuts24389 : List PrefixCut := [⟨66,271917237,271917387⟩,
⟨128,525009645,525009940⟩]
theorem checked24389 : checkPrefixCuts (2^48) 3200647169 9 Manual.Count131072.C024389.packed 128 cuts24389 = true := by
 decide +kernel
def pointBounds24389 : List (Nat × Nat × Nat) := [(3200714752,102580667943744,102581049781697)]
theorem point_links_checked24389 : (cuts24389.take 1).map (fun c => (3200647169-1+2*2^9*c.k,102580396026507+c.lower,102580777864310+c.upper)) = pointBounds24389 := by
 decide +kernel
def cuts24390 : List PrefixCut := [⟨36,150287759,150287842⟩,
⟨128,527098735,527099036⟩]
theorem checked24390 : checkPrefixCuts (2^48) 3200778241 9 Manual.Count131072.C024390.packed 128 cuts24390 = true := by
 decide +kernel
def pointBounds24390 : List (Nat × Nat × Nat) := [(3200815104,102581071323911,102581453162092)]
theorem point_links_checked24390 : (cuts24390.take 1).map (fun c => (3200778241-1+2*2^9*c.k,102580921036152+c.lower,102581302874250+c.upper)) = pointBounds24390 := by
 decide +kernel
def cuts24391 : List PrefixCut := [⟨6,25501391,25501406⟩,
⟨104,424195848,424196083⟩,
⟨128,524351128,524351418⟩]
theorem checked24391 : checkPrefixCuts (2^48) 3200909313 9 Manual.Count131072.C024391.packed 128 cuts24391 = true := by
 decide +kernel
def pointBounds24391 : List (Nat × Nat × Nat) := [(3200915456,102581473636278,102581855474692),(3201015808,102581872330735,102582254169369)]
theorem point_links_checked24391 : (cuts24391.take 2).map (fun c => (3200909313-1+2*2^9*c.k,102581448134887+c.lower,102581829973286+c.upper)) = pointBounds24391 := by
 decide +kernel
def cuts24392 : List PrefixCut := [⟨74,302043916,302044087⟩,
⟨128,526703757,526704050⟩]
theorem checked24392 : checkPrefixCuts (2^48) 3201040385 9 Manual.Count131072.C024392.packed 128 cuts24392 = true := by
 decide +kernel
def pointBounds24392 : List (Nat × Nat × Nat) := [(3201116160,102582274529931,102582656368791)]
theorem point_links_checked24392 : (cuts24392.take 1).map (fun c => (3201040385-1+2*2^9*c.k,102581972486015+c.lower,102582354324704+c.upper)) = pointBounds24392 := by
 decide +kernel
def cuts24393 : List PrefixCut := [⟨44,181659454,181659553⟩,
⟨128,534507709,534507999⟩]
theorem checked24393 : checkPrefixCuts (2^48) 3201171457 9 Manual.Count131072.C024393.packed 128 cuts24393 = true := by
 decide +kernel
def pointBounds24393 : List (Nat × Nat × Nat) := [(3201216512,102582680849226,102583062688307)]
theorem point_links_checked24393 : (cuts24393.take 1).map (fun c => (3201171457-1+2*2^9*c.k,102582499189772+c.lower,102582881028754+c.upper)) = pointBounds24393 := by
 decide +kernel
def cuts24394 : List PrefixCut := [⟨14,58206299,58206329⟩,
⟨112,466170679,466170938⟩,
⟨128,532727436,532727731⟩]
theorem checked24394 : checkPrefixCuts (2^48) 3201302529 9 Manual.Count131072.C024394.packed 128 cuts24394 = true := by
 decide +kernel
def pointBounds24394 : List (Nat × Nat × Nat) := [(3201316864,102583091903780,102583473743082),(3201417216,102583499868160,102583881707691)]
theorem point_links_checked24394 : (cuts24394.take 2).map (fun c => (3201302529-1+2*2^9*c.k,102583033697481+c.lower,102583415536753+c.upper)) = pointBounds24394 := by
 decide +kernel
def cuts24395 : List PrefixCut := [⟨82,332251041,332251229⟩,
⟨128,518022973,518023268⟩]
theorem checked24395 : checkPrefixCuts (2^48) 3201433601 9 Manual.Count131072.C024395.packed 128 cuts24395 = true := by
 decide +kernel
def pointBounds24395 : List (Nat × Nat × Nat) := [(3201517568,102583898675958,102584280515713)]
theorem point_links_checked24395 : (cuts24395.take 1).map (fun c => (3201433601-1+2*2^9*c.k,102583566424917+c.lower,102583948264484+c.upper)) = pointBounds24395 := by
 decide +kernel
def cuts24396 : List PrefixCut := [⟨52,218034618,218034736⟩,
⟨128,525298838,525299132⟩]
theorem checked24396 : checkPrefixCuts (2^48) 3201564673 9 Manual.Count131072.C024396.packed 128 cuts24396 = true := by
 decide +kernel
def pointBounds24396 : List (Nat × Nat × Nat) := [(3201617920,102584302482508,102584684322488)]
theorem point_links_checked24396 : (cuts24396.take 1).map (fun c => (3201564673-1+2*2^9*c.k,102584084447890+c.lower,102584466287752+c.upper)) = pointBounds24396 := by
 decide +kernel
def cuts24397 : List PrefixCut := [⟨22,93452588,93452638⟩,
⟨120,495123955,495124229⟩,
⟨128,528617984,528618275⟩]
theorem checked24397 : checkPrefixCuts (2^48) 3201695745 9 Manual.Count131072.C024397.packed 128 cuts24397 = true := by
 decide +kernel
def pointBounds24397 : List (Nat × Nat × Nat) := [(3201718272,102584703199316,102585085039522),(3201818624,102585104870683,102585486711113)]
theorem point_links_checked24397 : (cuts24397.take 2).map (fun c => (3201695745-1+2*2^9*c.k,102584609746728+c.lower,102584991586884+c.upper)) = pointBounds24397 := by
 decide +kernel
def cuts24398 : List PrefixCut := [⟨90,371944862,371945066⟩,
⟨128,527365594,527365886⟩]
theorem checked24398 : checkPrefixCuts (2^48) 3201826817 9 Manual.Count131072.C024398.packed 128 cuts24398 = true := by
 decide +kernel
def pointBounds24398 : List (Nat × Nat × Nat) := [(3201918976,102585510309574,102585892150225)]
theorem point_links_checked24398 : (cuts24398.take 1).map (fun c => (3201826817-1+2*2^9*c.k,102585138364712+c.lower,102585520205159+c.upper)) = pointBounds24398 := by
 decide +kernel
def cuts24399 : List PrefixCut := [⟨60,240951107,240951245⟩,
⟨128,521190571,521190870⟩]
theorem checked24399 : checkPrefixCuts (2^48) 3201957889 9 Manual.Count131072.C024399.packed 128 cuts24399 = true := by
 decide +kernel
def pointBounds24399 : List (Nat × Nat × Nat) := [(3202019328,102585906681413,102586288522290)]
theorem point_links_checked24399 : (cuts24399.take 1).map (fun c => (3201957889-1+2*2^9*c.k,102585665730306+c.lower,102586047571045+c.upper)) = pointBounds24399 := by
 decide +kernel
def cuts24400 : List PrefixCut := [⟨30,121657892,121657962⟩,
⟨128,528640961,528641261⟩]
theorem checked24400 : checkPrefixCuts (2^48) 3202088961 9 Manual.Count131072.C024400.packed 128 cuts24400 = true := by
 decide +kernel
def pointBounds24400 : List (Nat × Nat × Nat) := [(3202119680,102586308578769,102586690419877),(3202220032,102586715561838,102587097403176)]
theorem point_links_checked24400 : (cuts24400.take 2).map (fun c => (3202088961-1+2*2^9*c.k,102586186920877+c.lower,102586568761915+c.upper)) = pointBounds24400 := by
 decide +kernel
def cuts24401 : List PrefixCut := [⟨98,402663205,402663428⟩,
⟨128,533893052,533893347⟩]
theorem checked24401 : checkPrefixCuts (2^48) 3202220033 9 Manual.Count131072.C024401.packed 128 cuts24401 = true := by
 decide +kernel
def pointBounds24401 : List (Nat × Nat × Nat) := [(3202320384,102587118225043,102587500066604)]
theorem point_links_checked24401 : (cuts24401.take 1).map (fun c => (3202220033-1+2*2^9*c.k,102586715561838+c.lower,102587097403176+c.upper)) = pointBounds24401 := by
 decide +kernel
def cuts24402 : List PrefixCut := [⟨68,275288277,275288440⟩,
⟨128,525521281,525521583⟩]
theorem checked24402 : checkPrefixCuts (2^48) 3202351105 9 Manual.Count131072.C024402.packed 128 cuts24402 = true := by
 decide +kernel
def pointBounds24402 : List (Nat × Nat × Nat) := [(3202420736,102587524743167,102587906584963)]
theorem point_links_checked24402 : (cuts24402.take 1).map (fun c => (3202351105-1+2*2^9*c.k,102587249454890+c.lower,102587631296523+c.upper)) = pointBounds24402 := by
 decide +kernel
def cuts24403 : List PrefixCut := [⟨38,160491154,160491244⟩,
⟨128,532355413,532355716⟩]
theorem checked24403 : checkPrefixCuts (2^48) 3202482177 9 Manual.Count131072.C024403.packed 128 cuts24403 = true := by
 decide +kernel
def pointBounds24403 : List (Nat × Nat × Nat) := [(3202521088,102587935467325,102588317309350)]
theorem point_links_checked24403 : (cuts24403.take 1).map (fun c => (3202482177-1+2*2^9*c.k,102587774976171+c.lower,102588156818106+c.upper)) = pointBounds24403 := by
 decide +kernel
def cuts24404 : List PrefixCut := [⟨8,33749383,33749404⟩,
⟨106,436186414,436186664⟩,
⟨128,526269411,526269709⟩]
theorem checked24404 : checkPrefixCuts (2^48) 3202613249 9 Manual.Count131072.C024404.packed 128 cuts24404 = true := by
 decide +kernel
def pointBounds24404 : List (Nat × Nat × Nat) := [(3202621440,102588341080967,102588722923226),(3202721792,102588743517998,102589125360486)]
theorem point_links_checked24404 : (cuts24404.take 2).map (fun c => (3202613249-1+2*2^9*c.k,102588307331584+c.lower,102588689173822+c.upper)) = pointBounds24404 := by
 decide +kernel
def cuts24405 : List PrefixCut := [⟨76,310935209,310935388⟩,
⟨128,521765754,521766049⟩]
theorem checked24405 : checkPrefixCuts (2^48) 3202744321 9 Manual.Count131072.C024405.packed 128 cuts24405 = true := by
 decide +kernel
def pointBounds24405 : List (Nat × Nat × Nat) := [(3202822144,102589144536204,102589526378919)]
theorem point_links_checked24405 : (cuts24405.take 1).map (fun c => (3202744321-1+2*2^9*c.k,102588833600995+c.lower,102589215443531+c.upper)) = pointBounds24405 := by
 decide +kernel
def cuts24406 : List PrefixCut := [⟨46,186571978,186572083⟩,
⟨128,524292869,524293167⟩]
theorem checked24406 : checkPrefixCuts (2^48) 3202875393 9 Manual.Count131072.C024406.packed 128 cuts24406 = true := by
 decide +kernel
def pointBounds24406 : List (Nat × Nat × Nat) := [(3202922496,102589541938727,102589923781663)]
theorem point_links_checked24406 : (cuts24406.take 1).map (fun c => (3202875393-1+2*2^9*c.k,102589355366749+c.lower,102589737209580+c.upper)) = pointBounds24406 := by
 decide +kernel
def cuts24407 : List PrefixCut := [⟨16,66435856,66435893⟩,
⟨114,470052678,470052942⟩,
⟨128,528577390,528577686⟩]
theorem checked24407 : checkPrefixCuts (2^48) 3203006465 9 Manual.Count131072.C024407.packed 128 cuts24407 = true := by
 decide +kernel
def pointBounds24407 : List (Nat × Nat × Nat) := [(3203022848,102589946095474,102590327938640),(3203123200,102590349712296,102590731555689)]
theorem point_links_checked24407 : (cuts24407.take 2).map (fun c => (3203006465-1+2*2^9*c.k,102589879659618+c.lower,102590261502747+c.upper)) = pointBounds24407 := by
 decide +kernel
def cuts24408 : List PrefixCut := [⟨84,349385318,349385514⟩,
⟨128,527325648,527325945⟩]
theorem checked24408 : checkPrefixCuts (2^48) 3203137537 9 Manual.Count131072.C024408.packed 128 cuts24408 = true := by
 decide +kernel
def pointBounds24408 : List (Nat × Nat × Nat) := [(3203223552,102590757622326,102591139465947)]
theorem point_links_checked24408 : (cuts24408.take 1).map (fun c => (3203137537-1+2*2^9*c.k,102590408237008+c.lower,102590790080433+c.upper)) = pointBounds24408 := by
 decide +kernel
def cuts24409 : List PrefixCut := [⟨54,218709386,218709511⟩,
⟨128,517462624,517462921⟩]
theorem checked24409 : checkPrefixCuts (2^48) 3203268609 9 Manual.Count131072.C024409.packed 128 cuts24409 = true := by
 decide +kernel
def pointBounds24409 : List (Nat × Nat × Nat) := [(3203323904,102591154272042,102591536115889)]
theorem point_links_checked24409 : (cuts24409.take 1).map (fun c => (3203268609-1+2*2^9*c.k,102590935562656+c.lower,102591317406378+c.upper)) = pointBounds24409 := by
 decide +kernel
def cuts24410 : List PrefixCut := [⟨24,97444741,97444797⟩,
⟨122,503822658,503822945⟩,
⟨128,529391095,529391395⟩]
theorem checked24410 : checkPrefixCuts (2^48) 3203399681 9 Manual.Count131072.C024410.packed 128 cuts24410 = true := by
 decide +kernel
def pointBounds24410 : List (Nat × Nat × Nat) := [(3203424256,102591550470021,102591932314096),(3203524608,102591956847938,102592338692244)]
theorem point_links_checked24410 : (cuts24410.take 2).map (fun c => (3203399681-1+2*2^9*c.k,102591453025280+c.lower,102591834869299+c.upper)) = pointBounds24410 := by
 decide +kernel
def cuts24411 : List PrefixCut := [⟨92,376930801,376931017⟩,
⟨128,527612222,527612522⟩]
theorem checked24411 : checkPrefixCuts (2^48) 3203530753 9 Manual.Count131072.C024411.packed 128 cuts24411 = true := by
 decide +kernel
def pointBounds24411 : List (Nat × Nat × Nat) := [(3203624960,102592359347176,102592741191711)]
theorem point_links_checked24411 : (cuts24411.take 1).map (fun c => (3203530753-1+2*2^9*c.k,102591982416375+c.lower,102592364260694+c.upper)) = pointBounds24411 := by
 decide +kernel
def cuts24412 : List PrefixCut := [⟨62,256901140,256901278⟩,
⟨128,526624261,526624553⟩]
theorem checked24412 : checkPrefixCuts (2^48) 3203661825 9 Manual.Count131072.C024412.packed 128 cuts24412 = true := by
 decide +kernel
def pointBounds24412 : List (Nat × Nat × Nat) := [(3203725312,102592766929737,102593148774494)]
theorem point_links_checked24412 : (cuts24412.take 1).map (fun c => (3203661825-1+2*2^9*c.k,102592510028597+c.lower,102592891873216+c.upper)) = pointBounds24412 := by
 decide +kernel
def cuts24413 : List PrefixCut := [⟨32,135913716,135913792⟩,
⟨128,532313355,532313659⟩]
theorem checked24413 : checkPrefixCuts (2^48) 3203792897 9 Manual.Count131072.C024413.packed 128 cuts24413 = true := by
 decide +kernel
def pointBounds24413 : List (Nat × Nat × Nat) := [(3203825664,102593172566574,102593554411561)]
theorem point_links_checked24413 : (cuts24413.take 1).map (fun c => (3203792897-1+2*2^9*c.k,102593036652858+c.lower,102593418497769+c.upper)) = pointBounds24413 := by
 decide +kernel
def cuts24414 : List PrefixCut := [⟨2,8521755,8521760⟩,
⟨100,414748288,414748520⟩,
⟨128,530973801,530974098⟩]
theorem checked24414 : checkPrefixCuts (2^48) 3203923969 9 Manual.Count131072.C024414.packed 128 cuts24414 = true := by
 decide +kernel
def pointBounds24414 : List (Nat × Nat × Nat) := [(3203926016,102593577487968,102593959333188),(3204026368,102593983714501,102594365559948)]
theorem point_links_checked24414 : (cuts24414.take 2).map (fun c => (3203923969-1+2*2^9*c.k,102593568966213+c.lower,102593950811428+c.upper)) = pointBounds24414 := by
 decide +kernel
def cuts24415 : List PrefixCut := [⟨70,289109712,289109874⟩,
⟨128,530864105,530864400⟩]
theorem checked24415 : checkPrefixCuts (2^48) 3204055041 9 Manual.Count131072.C024415.packed 128 cuts24415 = true := by
 decide +kernel
def pointBounds24415 : List (Nat × Nat × Nat) := [(3204126720,102594389049726,102594770895400)]
theorem point_links_checked24415 : (cuts24415.take 1).map (fun c => (3204055041-1+2*2^9*c.k,102594099940014+c.lower,102594481785526+c.upper)) = pointBounds24415 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000137
