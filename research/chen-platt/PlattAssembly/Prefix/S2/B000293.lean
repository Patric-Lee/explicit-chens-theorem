import PlattAssemblyKernel
import PlattCertificates.Count131072.C019376
import PlattCertificates.Count131072.C019377
import PlattCertificates.Count131072.C019378
import PlattCertificates.Count131072.C019379
import PlattCertificates.Count131072.C019380
import PlattCertificates.Count131072.C019381
import PlattCertificates.Count131072.C019382
import PlattCertificates.Count131072.C019383
import PlattCertificates.Count131072.C019384
import PlattCertificates.Count131072.C019385
import PlattCertificates.Count131072.C019386
import PlattCertificates.Count131072.C019387
import PlattCertificates.Count131072.C019388
import PlattCertificates.Count131072.C019389
import PlattCertificates.Count131072.C019390
import PlattCertificates.Count131072.C019391
import PlattCertificates.Count131072.C019392
import PlattCertificates.Count131072.C019393
import PlattCertificates.Count131072.C019394
import PlattCertificates.Count131072.C019395
import PlattCertificates.Count131072.C019396
import PlattCertificates.Count131072.C019397
import PlattCertificates.Count131072.C019398
import PlattCertificates.Count131072.C019399
import PlattCertificates.Count131072.C019400
import PlattCertificates.Count131072.C019401
import PlattCertificates.Count131072.C019402
import PlattCertificates.Count131072.C019403
import PlattCertificates.Count131072.C019404
import PlattCertificates.Count131072.C019405
import PlattCertificates.Count131072.C019406
import PlattCertificates.Count131072.C019407
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000293
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19376 : List PrefixCut := [⟨70,366835233,366835454⟩,
⟨128,667488568,667488969⟩]
theorem checked19376 : checkPrefixCuts (2^48) 2543583233 9 Manual.Count131072.C019376.packed 128 cuts19376 = true := by
 decide +kernel
def pointBounds19376 : List (Nat × Nat × Nat) := [(2543654912,99610137285709,99610517412732)]
theorem point_links_checked19376 : (cuts19376.take 1).map (fun c => (2543583233-1+2*2^9*c.k,99609770450476+c.lower,99610150577278+c.upper)) = pointBounds19376 := by
 decide +kernel
def cuts19377 : List PrefixCut := [⟨20,102908804,102908868⟩,
⟨98,506236937,506237238⟩,
⟨128,663138697,663139091⟩]
theorem checked19377 : checkPrefixCuts (2^48) 2543714305 9 Manual.Count131072.C019377.packed 128 cuts19377 = true := by
 decide +kernel
def pointBounds19377 : List (Nat × Nat × Nat) := [(2543734784,99610540847848,99610920975115),(2543814656,99610944175981,99611324303485)]
theorem point_links_checked19377 : (cuts19377.take 2).map (fun c => (2543714305-1+2*2^9*c.k,99610437939044+c.lower,99610818066247+c.upper)) = pointBounds19377 := by
 decide +kernel
def cuts19378 : List PrefixCut := [⟨48,250065180,250065332⟩,
⟨126,658789684,658790078⟩,
⟨128,669632768,669633169⟩]
theorem checked19378 : checkPrefixCuts (2^48) 2543845377 9 Manual.Count131072.C019378.packed 128 cuts19378 = true := by
 decide +kernel
def pointBounds19378 : List (Nat × Nat × Nat) := [(2543894528,99611351142921,99611731270670),(2543974400,99611759867425,99612139995416)]
theorem point_links_checked19378 : (cuts19378.take 2).map (fun c => (2543845377-1+2*2^9*c.k,99611101077741+c.lower,99611481205338+c.upper)) = pointBounds19378 := by
 decide +kernel
def cuts19379 : List PrefixCut := [⟨76,393996094,393996327⟩,
⟨128,667827969,667828364⟩]
theorem checked19379 : checkPrefixCuts (2^48) 2543976449 9 Manual.Count131072.C019379.packed 128 cuts19379 = true := by
 decide +kernel
def pointBounds19379 : List (Nat × Nat × Nat) := [(2544054272,99612164706603,99612544834834)]
theorem point_links_checked19379 : (cuts19379.take 1).map (fun c => (2543976449-1+2*2^9*c.k,99611770710509+c.lower,99612150838507+c.upper)) = pointBounds19379 := by
 decide +kernel
def cuts19380 : List PrefixCut := [⟨26,134424425,134424506⟩,
⟨104,542225349,542225673⟩,
⟨128,668789280,668789679⟩]
theorem checked19380 : checkPrefixCuts (2^48) 2544107521 9 Manual.Count131072.C019380.packed 128 cuts19380 = true := by
 decide +kernel
def pointBounds19380 : List (Nat × Nat × Nat) := [(2544134144,99612572962903,99612953091377),(2544214016,99612980763827,99613360892544)]
theorem point_links_checked19380 : (cuts19380.take 2).map (fun c => (2544107521-1+2*2^9*c.k,99612438538478+c.lower,99612818666871+c.upper)) = pointBounds19380 := by
 decide +kernel
def cuts19381 : List PrefixCut := [⟨54,281777313,281777480⟩,
⟨128,667648509,667648901⟩]
theorem checked19381 : checkPrefixCuts (2^48) 2544238593 9 Manual.Count131072.C019381.packed 128 cuts19381 = true := by
 decide +kernel
def pointBounds19381 : List (Nat × Nat × Nat) := [(2544293888,99613389105071,99613769234030)]
theorem point_links_checked19381 : (cuts19381.take 1).map (fun c => (2544238593-1+2*2^9*c.k,99613107327758+c.lower,99613487456550+c.upper)) = pointBounds19381 := by
 decide +kernel
def cuts19382 : List PrefixCut := [⟨4,19580887,19580899⟩,
⟨82,427011528,427011781⟩,
⟨128,662525544,662525937⟩]
theorem checked19382 : checkPrefixCuts (2^48) 2544369665 9 Manual.Count131072.C019382.packed 128 cuts19382 = true := by
 decide +kernel
def pointBounds19382 : List (Nat × Nat × Nat) := [(2544373760,99613794557154,99614174686350),(2544453632,99614201987795,99614582117232)]
theorem point_links_checked19382 : (cuts19382.take 2).map (fun c => (2544369665-1+2*2^9*c.k,99613774976267+c.lower,99614155105451+c.upper)) = pointBounds19382 := by
 decide +kernel
def cuts19383 : List PrefixCut := [⟨32,166040862,166040958⟩,
⟨110,569906077,569906413⟩,
⟨128,661938241,661938631⟩]
theorem checked19383 : checkPrefixCuts (2^48) 2544500737 9 Manual.Count131072.C019383.packed 128 cuts19383 = true := by
 decide +kernel
def pointBounds19383 : List (Nat × Nat × Nat) := [(2544533504,99614603542673,99614983672346),(2544613376,99615007407888,99615387537801)]
theorem point_links_checked19383 : (cuts19383.take 2).map (fun c => (2544500737-1+2*2^9*c.k,99614437501811+c.lower,99614817631388+c.upper)) = pointBounds19383 := by
 decide +kernel
def cuts19384 : List PrefixCut := [⟨60,312594723,312594907⟩,
⟨128,671638003,671638395⟩]
theorem checked19384 : checkPrefixCuts (2^48) 2544631809 9 Manual.Count131072.C019384.packed 128 cuts19384 = true := by
 decide +kernel
def pointBounds19384 : List (Nat × Nat × Nat) := [(2544693248,99615412034775,99615792164926)]
theorem point_links_checked19384 : (cuts19384.take 1).map (fun c => (2544631809-1+2*2^9*c.k,99615099440052+c.lower,99615479570019+c.upper)) = pointBounds19384 := by
 decide +kernel
def cuts19385 : List PrefixCut := [⟨10,53977318,53977349⟩,
⟨88,466100047,466100320⟩,
⟨128,674147430,674147826⟩]
theorem checked19385 : checkPrefixCuts (2^48) 2544762881 9 Manual.Count131072.C019385.packed 128 cuts19385 = true := by
 decide +kernel
def pointBounds19385 : List (Nat × Nat × Nat) := [(2544773120,99615825055373,99616205185763),(2544852992,99616237178102,99616617308734)]
theorem point_links_checked19385 : (cuts19385.take 2).map (fun c => (2544762881-1+2*2^9*c.k,99615771078055+c.lower,99616151208414+c.upper)) = pointBounds19385 := by
 decide +kernel
def cuts19386 : List PrefixCut := [⟨38,198642867,198642984⟩,
⟨116,598131322,598131679⟩,
⟨128,662499561,662499953⟩]
theorem checked19386 : checkPrefixCuts (2^48) 2544893953 9 Manual.Count131072.C019386.packed 128 cuts19386 = true := by
 decide +kernel
def pointBounds19386 : List (Nat × Nat × Nat) := [(2544932864,99616643868352,99617023999224),(2545012736,99617043356807,99617423487919)]
theorem point_links_checked19386 : (cuts19386.take 2).map (fun c => (2544893953-1+2*2^9*c.k,99616445225485+c.lower,99616825356240+c.upper)) = pointBounds19386 := by
 decide +kernel
def cuts19387 : List PrefixCut := [⟨66,344840199,344840405⟩,
⟨128,663903208,663903603⟩]
theorem checked19387 : checkPrefixCuts (2^48) 2545025025 9 Manual.Count131072.C019387.packed 128 cuts19387 = true := by
 decide +kernel
def pointBounds19387 : List (Nat × Nat × Nat) := [(2545092608,99617452565245,99617832696598)]
theorem point_links_checked19387 : (cuts19387.take 1).map (fun c => (2545025025-1+2*2^9*c.k,99617107725046+c.lower,99617487856193+c.upper)) = pointBounds19387 := by
 decide +kernel
def cuts19388 : List PrefixCut := [⟨16,80953354,80953403⟩,
⟨94,488809036,488809327⟩,
⟨128,668624250,668624648⟩]
theorem checked19388 : checkPrefixCuts (2^48) 2545156097 9 Manual.Count131072.C019388.packed 128 cuts19388 = true := by
 decide +kernel
def pointBounds19388 : List (Nat × Nat × Nat) := [(2545172480,99617852581608,99618232713199),(2545252352,99618260437290,99618640569123)]
theorem point_links_checked19388 : (cuts19388.take 2).map (fun c => (2545156097-1+2*2^9*c.k,99617771628254+c.lower,99618151759796+c.upper)) = pointBounds19388 := by
 decide +kernel
def cuts19389 : List PrefixCut := [⟨44,230018296,230018430⟩,
⟨122,632761604,632761976⟩,
⟨128,664719551,664719942⟩]
theorem checked19389 : checkPrefixCuts (2^48) 2545287169 9 Manual.Count131072.C019389.packed 128 cuts19389 = true := by
 decide +kernel
def pointBounds19389 : List (Nat × Nat × Nat) := [(2545332224,99618670270800,99619050402874),(2545412096,99619073014108,99619453146420)]
theorem point_links_checked19389 : (cuts19389.take 2).map (fun c => (2545287169-1+2*2^9*c.k,99618440252504+c.lower,99618820384444+c.upper)) = pointBounds19389 := by
 decide +kernel
def cuts19390 : List PrefixCut := [⟨72,376854625,376854844⟩,
⟨128,674637248,674637641⟩]
theorem checked19390 : checkPrefixCuts (2^48) 2545418241 9 Manual.Count131072.C019390.packed 128 cuts19390 = true := by
 decide +kernel
def pointBounds19390 : List (Nat × Nat × Nat) := [(2545491968,99619481826680,99619861959230)]
theorem point_links_checked19390 : (cuts19390.take 1).map (fun c => (2545418241-1+2*2^9*c.k,99619104972055+c.lower,99619485104386+c.upper)) = pointBounds19390 := by
 decide +kernel
def cuts19391 : List PrefixCut := [⟨22,118978507,118978576⟩,
⟨100,522236793,522237104⟩,
⟨128,669295228,669295624⟩]
theorem checked19391 : checkPrefixCuts (2^48) 2545549313 9 Manual.Count131072.C019391.packed 128 cuts19391 = true := by
 decide +kernel
def pointBounds19391 : List (Nat × Nat × Nat) := [(2545571840,99619898587810,99620278720603),(2545651712,99620301846096,99620681979131)]
theorem point_links_checked19391 : (cuts19391.take 2).map (fun c => (2545549313-1+2*2^9*c.k,99619779609303+c.lower,99620159742027+c.upper)) = pointBounds19391 := by
 decide +kernel
def cuts19392 : List PrefixCut := [⟨50,263484724,263484886⟩,
⟨128,667270439,667270839⟩]
theorem checked19392 : checkPrefixCuts (2^48) 2545680385 9 Manual.Count131072.C019392.packed 128 cuts19392 = true := by
 decide +kernel
def pointBounds19392 : List (Nat × Nat × Nat) := [(2545731584,99620712389255,99621092522537),(2545811456,99621116174970,99621496308490)]
theorem point_links_checked19392 : (cuts19392.take 2).map (fun c => (2545680385-1+2*2^9*c.k,99620448904531+c.lower,99620829037651+c.upper)) = pointBounds19392 := by
 decide +kernel
def cuts19393 : List PrefixCut := [⟨78,418367340,418367590⟩,
⟨128,684262578,684262984⟩]
theorem checked19393 : checkPrefixCuts (2^48) 2545811457 9 Manual.Count131072.C019393.packed 128 cuts19393 = true := by
 decide +kernel
def pointBounds19393 : List (Nat × Nat × Nat) := [(2545891328,99621534542310,99621914676080)]
theorem point_links_checked19393 : (cuts19393.take 1).map (fun c => (2545811457-1+2*2^9*c.k,99621116174970+c.lower,99621496308490+c.upper)) = pointBounds19393 := by
 decide +kernel
def cuts19394 : List PrefixCut := [⟨28,152901169,152901261⟩,
⟨106,553995585,553995917⟩,
⟨128,667422990,667423391⟩]
theorem checked19394 : checkPrefixCuts (2^48) 2545942529 9 Manual.Count131072.C019394.packed 128 cuts19394 = true := by
 decide +kernel
def pointBounds19394 : List (Nat × Nat × Nat) := [(2545971200,99621953338717,99622333472735),(2546051072,99622354433133,99622734567391)]
theorem point_links_checked19394 : (cuts19394.take 2).map (fun c => (2545942529-1+2*2^9*c.k,99621800437548+c.lower,99622180571474+c.upper)) = pointBounds19394 := by
 decide +kernel
def cuts19395 : List PrefixCut := [⟨56,292408174,292408345⟩,
⟨128,671478848,671479240⟩]
theorem checked19395 : checkPrefixCuts (2^48) 2546073601 9 Manual.Count131072.C019395.packed 128 cuts19395 = true := by
 decide +kernel
def pointBounds19395 : List (Nat × Nat × Nat) := [(2546130944,99622760268712,99623140403210)]
theorem point_links_checked19395 : (cuts19395.take 1).map (fun c => (2546073601-1+2*2^9*c.k,99622467860538+c.lower,99622847994865+c.upper)) = pointBounds19395 := by
 decide +kernel
def cuts19396 : List PrefixCut := [⟨6,30510894,30510912⟩,
⟨84,441295455,441295713⟩,
⟨128,665695972,665696364⟩]
theorem checked19396 : checkPrefixCuts (2^48) 2546204673 9 Manual.Count131072.C019396.packed 128 cuts19396 = true := by
 decide +kernel
def pointBounds19396 : List (Nat × Nat × Nat) := [(2546210816,99623169850280,99623549985017),(2546290688,99623580634841,99623960769818)]
theorem point_links_checked19396 : (cuts19396.take 2).map (fun c => (2546204673-1+2*2^9*c.k,99623139339386+c.lower,99623519474105+c.upper)) = pointBounds19396 := by
 decide +kernel
def cuts19397 : List PrefixCut := [⟨34,177527895,177527999⟩,
⟨112,583091432,583091779⟩,
⟨128,667651338,667651734⟩]
theorem checked19397 : checkPrefixCuts (2^48) 2546335745 9 Manual.Count131072.C019397.packed 128 cuts19397 = true := by
 decide +kernel
def pointBounds19397 : List (Nat × Nat × Nat) := [(2546370560,99623982563253,99624362698468),(2546450432,99624388126790,99624768262248)]
theorem point_links_checked19397 : (cuts19397.take 2).map (fun c => (2546335745-1+2*2^9*c.k,99623805035358+c.lower,99624185170469+c.upper)) = pointBounds19397 := by
 decide +kernel
def cuts19398 : List PrefixCut := [⟨62,326407161,326407355⟩,
⟨128,672480511,672480904⟩]
theorem checked19398 : checkPrefixCuts (2^48) 2546466817 9 Manual.Count131072.C019398.packed 128 cuts19398 = true := by
 decide +kernel
def pointBounds19398 : List (Nat × Nat × Nat) := [(2546530304,99624799093857,99625179229558)]
theorem point_links_checked19398 : (cuts19398.take 1).map (fun c => (2546466817-1+2*2^9*c.k,99624472686696+c.lower,99624852822203+c.upper)) = pointBounds19398 := by
 decide +kernel
def cuts19399 : List PrefixCut := [⟨12,64991360,64991397⟩,
⟨90,466648355,466648625⟩,
⟨128,665261649,665262036⟩]
theorem checked19399 : checkPrefixCuts (2^48) 2546597889 9 Manual.Count131072.C019399.packed 128 cuts19399 = true := by
 decide +kernel
def pointBounds19399 : List (Nat × Nat × Nat) := [(2546610176,99625210158567,99625590294504),(2546690048,99625611815562,99625991951732)]
theorem point_links_checked19399 : (cuts19399.take 2).map (fun c => (2546597889-1+2*2^9*c.k,99625145167207+c.lower,99625525303107+c.upper)) = pointBounds19399 := by
 decide +kernel
def cuts19400 : List PrefixCut := [⟨40,209772998,209773121⟩,
⟨118,620135928,620136295⟩,
⟨128,672742790,672743188⟩]
theorem checked19400 : checkPrefixCuts (2^48) 2546728961 9 Manual.Count131072.C019400.packed 128 cuts19400 = true := by
 decide +kernel
def pointBounds19400 : List (Nat × Nat × Nat) := [(2546769920,99626020201854,99626400338264),(2546849792,99626430564784,99626810701438)]
theorem point_links_checked19400 : (cuts19400.take 2).map (fun c => (2546728961-1+2*2^9*c.k,99625810428856+c.lower,99626190565143+c.upper)) = pointBounds19400 := by
 decide +kernel
def cuts19401 : List PrefixCut := [⟨68,350670067,350670283⟩,
⟨128,668508479,668508886⟩]
theorem checked19401 : checkPrefixCuts (2^48) 2546860033 9 Manual.Count131072.C019401.packed 128 cuts19401 = true := by
 decide +kernel
def pointBounds19401 : List (Nat × Nat × Nat) := [(2546929664,99626833841713,99627213978614)]
theorem point_links_checked19401 : (cuts19401.take 1).map (fun c => (2546860033-1+2*2^9*c.k,99626483171646+c.lower,99626863308331+c.upper)) = pointBounds19401 := by
 decide +kernel
def cuts19402 : List PrefixCut := [⟨18,88299345,88299401⟩,
⟨96,498402661,498402953⟩,
⟨128,667368977,667369372⟩]
theorem checked19402 : checkPrefixCuts (2^48) 2546991105 9 Manual.Count131072.C019402.packed 128 cuts19402 = true := by
 decide +kernel
def pointBounds19402 : List (Nat × Nat × Nat) := [(2547009536,99627239979470,99627620116618),(2547089408,99627650082786,99628030220170)]
theorem point_links_checked19402 : (cuts19402.take 2).map (fun c => (2546991105-1+2*2^9*c.k,99627151680125+c.lower,99627531817217+c.upper)) = pointBounds19402 := by
 decide +kernel
def cuts19403 : List PrefixCut := [⟨46,236151305,236151442⟩,
⟨124,642692766,642693139⟩,
⟨128,663467035,663467420⟩]
theorem checked19403 : checkPrefixCuts (2^48) 2547122177 9 Manual.Count131072.C019403.packed 128 cuts19403 = true := by
 decide +kernel
def pointBounds19403 : List (Nat × Nat × Nat) := [(2547169280,99628055200407,99628435338031),(2547249152,99628461741868,99628841879728)]
theorem point_links_checked19403 : (cuts19403.take 2).map (fun c => (2547122177-1+2*2^9*c.k,99627819049102+c.lower,99628199186589+c.upper)) = pointBounds19403 := by
 decide +kernel
def cuts19404 : List PrefixCut := [⟨74,390395400,390395629⟩,
⟨128,670725901,670726301⟩]
theorem checked19404 : checkPrefixCuts (2^48) 2547253249 9 Manual.Count131072.C019404.packed 128 cuts19404 = true := by
 decide +kernel
def pointBounds19404 : List (Nat × Nat × Nat) := [(2547329024,99628872911537,99629253049638)]
theorem point_links_checked19404 : (cuts19404.take 1).map (fun c => (2547253249-1+2*2^9*c.k,99628482516137+c.lower,99628862654009+c.upper)) = pointBounds19404 := by
 decide +kernel
def cuts19405 : List PrefixCut := [⟨24,126737892,126737969⟩,
⟨102,533572566,533572888⟩,
⟨128,672680153,672680554⟩]
theorem checked19405 : checkPrefixCuts (2^48) 2547384321 9 Manual.Count131072.C019405.packed 128 cuts19405 = true := by
 decide +kernel
def pointBounds19405 : List (Nat × Nat × Nat) := [(2547408896,99629279979930,99629660118279),(2547488768,99629686814604,99630066953198)]
theorem point_links_checked19405 : (cuts19405.take 2).map (fun c => (2547384321-1+2*2^9*c.k,99629153242038+c.lower,99629533380310+c.upper)) = pointBounds19405 := by
 decide +kernel
def cuts19406 : List PrefixCut := [⟨52,276111511,276111672⟩,
⟨128,674413415,674413810⟩]
theorem checked19406 : checkPrefixCuts (2^48) 2547515393 9 Manual.Count131072.C019406.packed 128 cuts19406 = true := by
 decide +kernel
def pointBounds19406 : List (Nat × Nat × Nat) := [(2547568640,99630102033702,99630482172536)]
theorem point_links_checked19406 : (cuts19406.take 1).map (fun c => (2547515393-1+2*2^9*c.k,99629825922191+c.lower,99630206060864+c.upper)) = pointBounds19406 := by
 decide +kernel
def cuts19407 : List PrefixCut := [⟨2,9612129,9612135⟩,
⟨80,412873134,412873381⟩,
⟨128,661452372,661452770⟩]
theorem checked19407 : checkPrefixCuts (2^48) 2547646465 9 Manual.Count131072.C019407.packed 128 cuts19407 = true := by
 decide +kernel
def pointBounds19407 : List (Nat × Nat × Nat) := [(2547648512,99630509947735,99630890086809),(2547728384,99630913208740,99631293348055)]
theorem point_links_checked19407 : (cuts19407.take 2).map (fun c => (2547646465-1+2*2^9*c.k,99630500335606+c.lower,99630880474674+c.upper)) = pointBounds19407 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000293
