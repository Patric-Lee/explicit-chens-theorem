import PlattAssemblyKernel
import PlattCertificates.Count131072.C020512
import PlattCertificates.Count131072.C020513
import PlattCertificates.Count131072.C020514
import PlattCertificates.Count131072.C020515
import PlattCertificates.Count131072.C020516
import PlattCertificates.Count131072.C020517
import PlattCertificates.Count131072.C020518
import PlattCertificates.Count131072.C020519
import PlattCertificates.Count131072.C020520
import PlattCertificates.Count131072.C020521
import PlattCertificates.Count131072.C020522
import PlattCertificates.Count131072.C020523
import PlattCertificates.Count131072.C020524
import PlattCertificates.Count131072.C020525
import PlattCertificates.Count131072.C020526
import PlattCertificates.Count131072.C020527
import PlattCertificates.Count131072.C020528
import PlattCertificates.Count131072.C020529
import PlattCertificates.Count131072.C020530
import PlattCertificates.Count131072.C020531
import PlattCertificates.Count131072.C020532
import PlattCertificates.Count131072.C020533
import PlattCertificates.Count131072.C020534
import PlattCertificates.Count131072.C020535
import PlattCertificates.Count131072.C020536
import PlattCertificates.Count131072.C020537
import PlattCertificates.Count131072.C020538
import PlattCertificates.Count131072.C020539
import PlattCertificates.Count131072.C020540
import PlattCertificates.Count131072.C020541
import PlattCertificates.Count131072.C020542
import PlattCertificates.Count131072.C020543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20512 : List PrefixCut := [⟨38,189845230,189845342⟩,
⟨121,597020518,597020865⟩,
⟨128,633817238,633817606⟩]
theorem checked20512 : checkPrefixCuts (2^48) 2692481025 9 Manual.Count131072.C020512.packed 128 cuts20512 = true := by
 decide +kernel
def pointBounds20512 : List (Nat × Nat × Nat) := [(2692519936,100348404370997,100348784932550),(2692604928,100348811546285,100349192108073)]
theorem point_links_checked20512 : (cuts20512.take 2).map (fun c => (2692481025-1+2*2^9*c.k,100348214525767+c.lower,100348595087208+c.upper)) = pointBounds20512 := by
 decide +kernel
def cuts20513 : List PrefixCut := [⟨76,364093688,364093900⟩,
⟨128,623437438,623437802⟩]
theorem checked20513 : checkPrefixCuts (2^48) 2692612097 9 Manual.Count131072.C020513.packed 128 cuts20513 = true := by
 decide +kernel
def pointBounds20513 : List (Nat × Nat × Nat) := [(2692689920,100349212436693,100349592998714)]
theorem point_links_checked20513 : (cuts20513.take 1).map (fun c => (2692612097-1+2*2^9*c.k,100348848343005+c.lower,100349228904814+c.upper)) = pointBounds20513 := by
 decide +kernel
def cuts20514 : List PrefixCut := [⟨31,149687376,149687465⟩,
⟨114,559646286,559646614⟩,
⟨128,631560241,631560614⟩]
theorem checked20514 : checkPrefixCuts (2^48) 2692743169 9 Manual.Count131072.C020514.packed 128 cuts20514 = true := by
 decide +kernel
def pointBounds20514 : List (Nat × Nat × Nat) := [(2692774912,100349621467819,100350002030081),(2692859904,100350031426729,100350411989230)]
theorem point_links_checked20514 : (cuts20514.take 2).map (fun c => (2692743169-1+2*2^9*c.k,100349471780443+c.lower,100349852342616+c.upper)) = pointBounds20514 := by
 decide +kernel
def cuts20515 : List PrefixCut := [⟨69,336986806,336987002⟩,
⟨128,628289327,628289691⟩]
theorem checked20515 : checkPrefixCuts (2^48) 2692874241 9 Manual.Count131072.C020515.packed 128 cuts20515 = true := by
 decide +kernel
def pointBounds20515 : List (Nat × Nat × Nat) := [(2692944896,100350440327490,100350820890232)]
theorem point_links_checked20515 : (cuts20515.take 1).map (fun c => (2692874241-1+2*2^9*c.k,100350103340684+c.lower,100350483903230+c.upper)) = pointBounds20515 := by
 decide +kernel
def cuts20516 : List PrefixCut := [⟨24,116226514,116226583⟩,
⟨107,528550555,528550871⟩,
⟨128,635261455,635261831⟩]
theorem checked20516 : checkPrefixCuts (2^48) 2693005313 9 Manual.Count131072.C020516.packed 128 cuts20516 = true := by
 decide +kernel
def pointBounds20516 : List (Nat × Nat × Nat) := [(2693029888,100350847856525,100351228419504),(2693114880,100351260180566,100351640743792)]
theorem point_links_checked20516 : (cuts20516.take 2).map (fun c => (2693005313-1+2*2^9*c.k,100350731630011+c.lower,100351112192921+c.upper)) = pointBounds20516 := by
 decide +kernel
def cuts20517 : List PrefixCut := [⟨62,302360232,302360406⟩,
⟨128,624465863,624466229⟩]
theorem checked20517 : checkPrefixCuts (2^48) 2693136385 9 Manual.Count131072.C020517.packed 128 cuts20517 = true := by
 decide +kernel
def pointBounds20517 : List (Nat × Nat × Nat) := [(2693199872,100351669251698,100352049815158)]
theorem point_links_checked20517 : (cuts20517.take 1).map (fun c => (2693136385-1+2*2^9*c.k,100351366891466+c.lower,100351747454752+c.upper)) = pointBounds20517 := by
 decide +kernel
def cuts20518 : List PrefixCut := [⟨17,80472874,80472921⟩,
⟨100,486905385,486905672⟩,
⟨128,619523541,619523908⟩]
theorem checked20518 : checkPrefixCuts (2^48) 2693267457 9 Manual.Count131072.C020518.packed 128 cuts20518 = true := by
 decide +kernel
def pointBounds20518 : List (Nat × Nat × Nat) := [(2693284864,100352071830203,100352452393902),(2693369856,100352478262714,100352858826653)]
theorem point_links_checked20518 : (cuts20518.take 2).map (fun c => (2693267457-1+2*2^9*c.k,100351991357329+c.lower,100352371920981+c.upper)) = pointBounds20518 := by
 decide +kernel
def cuts20519 : List PrefixCut := [⟨55,277981665,277981825⟩,
⟨128,630361910,630362273⟩]
theorem checked20519 : checkPrefixCuts (2^48) 2693398529 9 Manual.Count131072.C020519.packed 128 cuts20519 = true := by
 decide +kernel
def pointBounds20519 : List (Nat × Nat × Nat) := [(2693454848,100352888862535,100353269426714)]
theorem point_links_checked20519 : (cuts20519.take 1).map (fun c => (2693398529-1+2*2^9*c.k,100352610880870+c.lower,100352991444889+c.upper)) = pointBounds20519 := by
 decide +kernel
def cuts20520 : List PrefixCut := [⟨10,49533093,49533120⟩,
⟨93,462092515,462092780⟩,
⟨128,633674950,633675312⟩]
theorem checked20520 : checkPrefixCuts (2^48) 2693529601 9 Manual.Count131072.C020520.packed 128 cuts20520 = true := by
 decide +kernel
def pointBounds20520 : List (Nat × Nat × Nat) := [(2693539840,100353290775873,100353671340282),(2693624832,100353703335295,100354083899942)]
theorem point_links_checked20520 : (cuts20520.take 2).map (fun c => (2693529601-1+2*2^9*c.k,100353241242780+c.lower,100353621807162+c.upper)) = pointBounds20520 := by
 decide +kernel
def cuts20521 : List PrefixCut := [⟨48,233753854,233753991⟩,
⟨128,622881330,622881702⟩]
theorem checked20521 : checkPrefixCuts (2^48) 2693660673 9 Manual.Count131072.C020521.packed 128 cuts20521 = true := by
 decide +kernel
def pointBounds20521 : List (Nat × Nat × Nat) := [(2693709824,100354108671584,100354489236465)]
theorem point_links_checked20521 : (cuts20521.take 1).map (fun c => (2693660673-1+2*2^9*c.k,100353874917730+c.lower,100354255482474+c.upper)) = pointBounds20521 := by
 decide +kernel
def cuts20522 : List PrefixCut := [⟨3,14106172,14106180⟩,
⟨86,426522080,426522332⟩,
⟨128,637897207,637897584⟩]
theorem checked20522 : checkPrefixCuts (2^48) 2693791745 9 Manual.Count131072.C020522.packed 128 cuts20522 = true := by
 decide +kernel
def pointBounds20522 : List (Nat × Nat × Nat) := [(2693794816,100354511905232,100354892470356),(2693879808,100354924321140,100355304886508)]
theorem point_links_checked20522 : (cuts20522.take 2).map (fun c => (2693791745-1+2*2^9*c.k,100354497799060+c.lower,100354878364176+c.upper)) = pointBounds20522 := by
 decide +kernel
def cuts20523 : List PrefixCut := [⟨41,202177176,202177294⟩,
⟨124,605686158,605686514⟩,
⟨128,624074662,624075030⟩]
theorem checked20523 : checkPrefixCuts (2^48) 2693922817 9 Manual.Count131072.C020523.packed 128 cuts20523 = true := by
 decide +kernel
def pointBounds20523 : List (Nat × Nat × Nat) := [(2693964800,100355337873443,100355718439054),(2694049792,100355741382425,100356121948274)]
theorem point_links_checked20523 : (cuts20523.take 2).map (fun c => (2693922817-1+2*2^9*c.k,100355135696267+c.lower,100355516261760+c.upper)) = pointBounds20523 := by
 decide +kernel
def cuts20524 : List PrefixCut := [⟨79,397331692,397331926⟩,
⟨128,635745767,635746140⟩]
theorem checked20524 : checkPrefixCuts (2^48) 2694053889 9 Manual.Count131072.C020524.packed 128 cuts20524 = true := by
 decide +kernel
def pointBounds20524 : List (Nat × Nat × Nat) := [(2694134784,100356157102621,100356537668716)]
theorem point_links_checked20524 : (cuts20524.take 1).map (fun c => (2694053889-1+2*2^9*c.k,100355759770929+c.lower,100356140336790+c.upper)) = pointBounds20524 := by
 decide +kernel
def cuts20525 : List PrefixCut := [⟨34,170502050,170502148⟩,
⟨117,579300867,579301203⟩,
⟨128,632580625,632580994⟩]
theorem checked20525 : checkPrefixCuts (2^48) 2694184961 9 Manual.Count131072.C020525.packed 128 cuts20525 = true := by
 decide +kernel
def pointBounds20525 : List (Nat × Nat × Nat) := [(2694219776,100356566018746,100356946585078),(2694304768,100356974817563,100357355384133)]
theorem point_links_checked20525 : (cuts20525.take 2).map (fun c => (2694184961-1+2*2^9*c.k,100356395516696+c.lower,100356776082930+c.upper)) = pointBounds20525 := by
 decide +kernel
def cuts20526 : List PrefixCut := [⟨72,351118498,351118705⟩,
⟨128,628893392,628893759⟩]
theorem checked20526 : checkPrefixCuts (2^48) 2694316033 9 Manual.Count131072.C020526.packed 128 cuts20526 = true := by
 decide +kernel
def pointBounds20526 : List (Nat × Nat × Nat) := [(2694389760,100357379215819,100357759782629)]
theorem point_links_checked20526 : (cuts20526.take 1).map (fun c => (2694316033-1+2*2^9*c.k,100357028097321+c.lower,100357408663924+c.upper)) = pointBounds20526 := by
 decide +kernel
def cuts20527 : List PrefixCut := [⟨27,129953550,129953629⟩,
⟨110,541951989,541952310⟩,
⟨128,631265364,631265738⟩]
theorem checked20527 : checkPrefixCuts (2^48) 2694447105 9 Manual.Count131072.C020527.packed 128 cuts20527 = true := by
 decide +kernel
def pointBounds20527 : List (Nat × Nat × Nat) := [(2694474752,100357786944263,100358167511312),(2694559744,100358198942702,100358579509993)]
theorem point_links_checked20527 : (cuts20527.take 2).map (fun c => (2694447105-1+2*2^9*c.k,100357656990713+c.lower,100358037557683+c.upper)) = pointBounds20527 := by
 decide +kernel
def cuts20528 : List PrefixCut := [⟨65,331446594,331446787⟩,
⟨128,641889505,641889874⟩]
theorem checked20528 : checkPrefixCuts (2^48) 2694578177 9 Manual.Count131072.C020528.packed 128 cuts20528 = true := by
 decide +kernel
def pointBounds20528 : List (Nat × Nat × Nat) := [(2694644736,100358619702671,100359000270208)]
theorem point_links_checked20528 : (cuts20528.take 1).map (fun c => (2694578177-1+2*2^9*c.k,100358288256077+c.lower,100358668823421+c.upper)) = pointBounds20528 := by
 decide +kernel
def cuts20529 : List PrefixCut := [⟨20,100798352,100798408⟩,
⟨103,509102017,509102316⟩,
⟨128,632666437,632666807⟩]
theorem checked20529 : checkPrefixCuts (2^48) 2694709249 9 Manual.Count131072.C020529.packed 128 cuts20529 = true := by
 decide +kernel
def pointBounds20529 : List (Nat × Nat × Nat) := [(2694729728,100359030943934,100359411511703),(2694814720,100359439247599,100359819815611)]
theorem point_links_checked20529 : (cuts20529.take 2).map (fun c => (2694709249-1+2*2^9*c.k,100358930145582+c.lower,100359310713295+c.upper)) = pointBounds20529 := by
 decide +kernel
def cuts20530 : List PrefixCut := [⟨58,283890795,283890966⟩,
⟨128,627935537,627935906⟩]
theorem checked20530 : checkPrefixCuts (2^48) 2694840321 9 Manual.Count131072.C020530.packed 128 cuts20530 = true := by
 decide +kernel
def pointBounds20530 : List (Nat × Nat × Nat) := [(2694899712,100359846702814,100360227271068)]
theorem point_links_checked20530 : (cuts20530.take 1).map (fun c => (2694840321-1+2*2^9*c.k,100359562812019+c.lower,100359943380102+c.upper)) = pointBounds20530 := by
 decide +kernel
def cuts20531 : List PrefixCut := [⟨13,63919862,63919901⟩,
⟨96,469051623,469051897⟩,
⟨128,625816120,625816484⟩]
theorem checked20531 : checkPrefixCuts (2^48) 2694971393 9 Manual.Count131072.C020531.packed 128 cuts20531 = true := by
 decide +kernel
def pointBounds20531 : List (Nat × Nat × Nat) := [(2694984704,100360254667418,100360635235909),(2695069696,100360659799179,100361040367905)]
theorem point_links_checked20531 : (cuts20531.take 2).map (fun c => (2694971393-1+2*2^9*c.k,100360190747556+c.lower,100360571316008+c.upper)) = pointBounds20531 := by
 decide +kernel
def cuts20532 : List PrefixCut := [⟨51,249921052,249921200⟩,
⟨128,625890127,625890498⟩]
theorem checked20532 : checkPrefixCuts (2^48) 2695102465 9 Manual.Count131072.C020532.packed 128 cuts20532 = true := by
 decide +kernel
def pointBounds20532 : List (Nat × Nat × Nat) := [(2695154688,100361066484728,100361447053692)]
theorem point_links_checked20532 : (cuts20532.take 1).map (fun c => (2695102465-1+2*2^9*c.k,100360816563676+c.lower,100361197132492+c.upper)) = pointBounds20532 := by
 decide +kernel
def cuts20533 : List PrefixCut := [⟨6,29972618,29972635⟩,
⟨89,442898562,442898816⟩,
⟨128,640062438,640062810⟩]
theorem checked20533 : checkPrefixCuts (2^48) 2695233537 9 Manual.Count131072.C020533.packed 128 cuts20533 = true := by
 decide +kernel
def pointBounds20533 : List (Nat × Nat × Nat) := [(2695239680,100361472426421,100361852995625),(2695324672,100361885352365,100362265921806)]
theorem point_links_checked20533 : (cuts20533.take 2).map (fun c => (2695233537-1+2*2^9*c.k,100361442453803+c.lower,100361823022990+c.upper)) = pointBounds20533 := by
 decide +kernel
def cuts20534 : List PrefixCut := [⟨44,212094028,212094153⟩,
⟨127,626038199,626038562⟩,
⟨128,630841712,630842077⟩]
theorem checked20534 : checkPrefixCuts (2^48) 2695364609 9 Manual.Count131072.C020534.packed 128 cuts20534 = true := by
 decide +kernel
def pointBounds20534 : List (Nat × Nat × Nat) := [(2695409664,100362294610269,100362675179953),(2695494656,100362708554440,100363089124362)]
theorem point_links_checked20534 : (cuts20534.take 2).map (fun c => (2695364609-1+2*2^9*c.k,100362082516241+c.lower,100362463085800+c.upper)) = pointBounds20534 := by
 decide +kernel
def cuts20535 : List PrefixCut := [⟨82,407665613,407665849⟩,
⟨128,634570261,634570628⟩]
theorem checked20535 : checkPrefixCuts (2^48) 2695495681 9 Manual.Count131072.C020535.packed 128 cuts20535 = true := by
 decide +kernel
def pointBounds20535 : List (Nat × Nat × Nat) := [(2695579648,100363121023566,100363501593726)]
theorem point_links_checked20535 : (cuts20535.take 1).map (fun c => (2695495681-1+2*2^9*c.k,100362713357953+c.lower,100363093927877+c.upper)) = pointBounds20535 := by
 decide +kernel
def cuts20536 : List PrefixCut := [⟨37,182210042,182210146⟩,
⟨120,591729530,591729875⟩,
⟨128,629631874,629632243⟩]
theorem checked20536 : checkPrefixCuts (2^48) 2695626753 9 Manual.Count131072.C020536.packed 128 cuts20536 = true := by
 decide +kernel
def pointBounds20536 : List (Nat × Nat × Nat) := [(2695664640,100363530138256,100363910708651),(2695749632,100363939657744,100364320228380)]
theorem point_links_checked20536 : (cuts20536.take 2).map (fun c => (2695626753-1+2*2^9*c.k,100363347928214+c.lower,100363728498505+c.upper)) = pointBounds20536 := by
 decide +kernel
def cuts20537 : List PrefixCut := [⟨75,378182147,378182367⟩,
⟨128,640042366,640042739⟩]
theorem checked20537 : checkPrefixCuts (2^48) 2695757825 9 Manual.Count131072.C020537.packed 128 cuts20537 = true := by
 decide +kernel
def pointBounds20537 : List (Nat × Nat × Nat) := [(2695834624,100364355742235,100364736313115)]
theorem point_links_checked20537 : (cuts20537.take 1).map (fun c => (2695757825-1+2*2^9*c.k,100363977560088+c.lower,100364358130748+c.upper)) = pointBounds20537 := by
 decide +kernel
def cuts20538 : List PrefixCut := [⟨30,144918769,144918857⟩,
⟨113,547926319,547926645⟩,
⟨128,623723738,623724108⟩]
theorem checked20538 : checkPrefixCuts (2^48) 2695888897 9 Manual.Count131072.C020538.packed 128 cuts20538 = true := by
 decide +kernel
def pointBounds20538 : List (Nat × Nat × Nat) := [(2695919616,100364762521223,100365143092344),(2696004608,100365165528773,100365546100132)]
theorem point_links_checked20538 : (cuts20538.take 2).map (fun c => (2695888897-1+2*2^9*c.k,100364617602454+c.lower,100364998173487+c.upper)) = pointBounds20538 := by
 decide +kernel
def cuts20539 : List PrefixCut := [⟨68,338264154,338264352⟩,
⟨128,630166454,630166824⟩]
theorem checked20539 : checkPrefixCuts (2^48) 2696019969 9 Manual.Count131072.C020539.packed 128 cuts20539 = true := by
 decide +kernel
def pointBounds20539 : List (Nat × Nat × Nat) := [(2696089600,100365579590346,100365960161947)]
theorem point_links_checked20539 : (cuts20539.take 1).map (fun c => (2696019969-1+2*2^9*c.k,100365241326192+c.lower,100365621897595+c.upper)) = pointBounds20539 := by
 decide +kernel
def cuts20540 : List PrefixCut := [⟨23,115882143,115882210⟩,
⟨106,517703189,517703497⟩,
⟨128,626795066,626795437⟩]
theorem checked20540 : checkPrefixCuts (2^48) 2696151041 9 Manual.Count131072.C020540.packed 128 cuts20540 = true := by
 decide +kernel
def pointBounds20540 : List (Nat × Nat × Nat) := [(2696174592,100365987374789,100366367946629),(2696259584,100366389195835,100366769767916)]
theorem point_links_checked20540 : (cuts20540.take 2).map (fun c => (2696151041-1+2*2^9*c.k,100365871492646+c.lower,100366252064419+c.upper)) = pointBounds20540 := by
 decide +kernel
def cuts20541 : List PrefixCut := [⟨61,305556828,305557005⟩,
⟨128,635011520,635011885⟩]
theorem checked20541 : checkPrefixCuts (2^48) 2696282113 9 Manual.Count131072.C020541.packed 128 cuts20541 = true := by
 decide +kernel
def pointBounds20541 : List (Nat × Nat × Nat) := [(2696344576,100366803844540,100367184416861)]
theorem point_links_checked20541 : (cuts20541.take 1).map (fun c => (2696282113-1+2*2^9*c.k,100366498287712+c.lower,100366878859856+c.upper)) = pointBounds20541 := by
 decide +kernel
def cuts20542 : List PrefixCut := [⟨16,78708793,78708841⟩,
⟨99,492183130,492183420⟩,
⟨128,635711325,635711697⟩]
theorem checked20542 : checkPrefixCuts (2^48) 2696413185 9 Manual.Count131072.C020542.packed 128 cuts20542 = true := by
 decide +kernel
def pointBounds20542 : List (Nat × Nat × Nat) := [(2696429568,100367212008025,100367592580582),(2696514560,100367625482362,100368006055161)]
theorem point_links_checked20542 : (cuts20542.take 2).map (fun c => (2696413185-1+2*2^9*c.k,100367133299232+c.lower,100367513871741+c.upper)) = pointBounds20542 := by
 decide +kernel
def cuts20543 : List PrefixCut := [⟨54,259703594,259703747⟩,
⟨128,618144427,618144792⟩]
theorem checked20543 : checkPrefixCuts (2^48) 2696544257 9 Manual.Count131072.C020543.packed 128 cuts20543 = true := by
 decide +kernel
def pointBounds20543 : List (Nat × Nat × Nat) := [(2696599552,100368028714151,100368409287185)]
theorem point_links_checked20543 : (cuts20543.take 1).map (fun c => (2696544257-1+2*2^9*c.k,100367769010557+c.lower,100368149583438+c.upper)) = pointBounds20543 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000016
