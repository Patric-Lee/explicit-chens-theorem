import PlattAssemblyKernel
import PlattCertificates.Count131072.C014480
import PlattCertificates.Count131072.C014481
import PlattCertificates.Count131072.C014482
import PlattCertificates.Count131072.C014483
import PlattCertificates.Count131072.C014484
import PlattCertificates.Count131072.C014485
import PlattCertificates.Count131072.C014486
import PlattCertificates.Count131072.C014487
import PlattCertificates.Count131072.C014488
import PlattCertificates.Count131072.C014489
import PlattCertificates.Count131072.C014490
import PlattCertificates.Count131072.C014491
import PlattCertificates.Count131072.C014492
import PlattCertificates.Count131072.C014493
import PlattCertificates.Count131072.C014494
import PlattCertificates.Count131072.C014495
import PlattCertificates.Count131072.C014496
import PlattCertificates.Count131072.C014497
import PlattCertificates.Count131072.C014498
import PlattCertificates.Count131072.C014499
import PlattCertificates.Count131072.C014500
import PlattCertificates.Count131072.C014501
import PlattCertificates.Count131072.C014502
import PlattCertificates.Count131072.C014503
import PlattCertificates.Count131072.C014504
import PlattCertificates.Count131072.C014505
import PlattCertificates.Count131072.C014506
import PlattCertificates.Count131072.C014507
import PlattCertificates.Count131072.C014508
import PlattCertificates.Count131072.C014509
import PlattCertificates.Count131072.C014510
import PlattCertificates.Count131072.C014511
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000140
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14480 : List PrefixCut := [⟨19,131719519,131719611⟩,
⟨78,545221304,545221674⟩,
⟨128,892854544,892855149⟩]
theorem checked14480 : checkPrefixCuts (2^48) 1901854721 9 Manual.Count131072.C014480.packed 128 cuts14480 = true := by
 decide +kernel
def pointBounds14480 : List (Nat × Nat × Nat) := [(1901874176,95805475002115,95805852724514),(1901934592,95805888503900,95806266226577)]
theorem point_links_checked14480 : (cuts14480.take 2).map (fun c => (1901854721-1+2*2^9*c.k,95805343282596+c.lower,95805721004903+c.upper)) = pointBounds14480 := by
 decide +kernel
def cuts14481 : List PrefixCut := [⟨9,63339572,63339613⟩,
⟨68,478738900,478739228⟩,
⟨127,896788742,896789356⟩,
⟨128,904631674,904632293⟩]
theorem checked14481 : checkPrefixCuts (2^48) 1901985793 9 Manual.Count131072.C014481.packed 128 cuts14481 = true := by
 decide +kernel
def pointBounds14481 : List (Nat × Nat × Nat) := [(1901995008,95806299476712,95806677199665),(1902055424,95806714876040,95807092599280),(1902115840,95807132925882,95807510649408)]
theorem point_links_checked14481 : (cuts14481.take 3).map (fun c => (1901985793-1+2*2^9*c.k,95806236137140+c.lower,95806613860052+c.upper)) = pointBounds14481 := by
 decide +kernel
def cuts14482 : List PrefixCut := [⟨58,410193557,410193832⟩,
⟨117,829548480,829549041⟩,
⟨128,906196956,906197571⟩]
theorem checked14482 : checkPrefixCuts (2^48) 1902116865 9 Manual.Count131072.C014482.packed 128 cuts14482 = true := by
 decide +kernel
def pointBounds14482 : List (Nat × Nat × Nat) := [(1902176256,95807550962371,95807928686177),(1902236672,95807970317294,95808348041386)]
theorem point_links_checked14482 : (cuts14482.take 2).map (fun c => (1902116865-1+2*2^9*c.k,95807140768814+c.lower,95807518492345+c.upper)) = pointBounds14482 := by
 decide +kernel
def cuts14483 : List PrefixCut := [⟨48,342249293,342249524⟩,
⟨107,764536900,764537416⟩,
⟨128,907170576,907171191⟩]
theorem checked14483 : checkPrefixCuts (2^48) 1902247937 9 Manual.Count131072.C014483.packed 128 cuts14483 = true := by
 decide +kernel
def pointBounds14483 : List (Nat × Nat × Nat) := [(1902297088,95808389215063,95808766939440),(1902357504,95808811502670,95809189227332)]
theorem point_links_checked14483 : (cuts14483.take 2).map (fun c => (1902247937-1+2*2^9*c.k,95808046965770+c.lower,95808424689916+c.upper)) = pointBounds14483 := by
 decide +kernel
def cuts14484 : List PrefixCut := [⟨38,270319109,270319292⟩,
⟨97,697758369,697758841⟩,
⟨128,913766061,913766682⟩]
theorem checked14484 : checkPrefixCuts (2^48) 1902379009 9 Manual.Count131072.C014484.packed 128 cuts14484 = true := by
 decide +kernel
def pointBounds14484 : List (Nat × Nat × Nat) := [(1902417920,95809224455455,95809602180399),(1902478336,95809651894715,95810029619948)]
theorem point_links_checked14484 : (cuts14484.take 2).map (fun c => (1902379009-1+2*2^9*c.k,95808954136346+c.lower,95809331861107+c.upper)) = pointBounds14484 := by
 decide +kernel
def cuts14485 : List PrefixCut := [⟨28,199581980,199582117⟩,
⟨87,618709219,618709644⟩,
⟨128,902459373,902459985⟩]
theorem checked14485 : checkPrefixCuts (2^48) 1902510081 9 Manual.Count131072.C014485.packed 128 cuts14485 = true := by
 decide +kernel
def pointBounds14485 : List (Nat × Nat × Nat) := [(1902538752,95810067484387,95810445209906),(1902599168,95810486611626,95810864337433)]
theorem point_links_checked14485 : (cuts14485.take 2).map (fun c => (1902510081-1+2*2^9*c.k,95809867902407+c.lower,95810245627789+c.upper)) = pointBounds14485 := by
 decide +kernel
def cuts14486 : List PrefixCut := [⟨18,135363531,135363622⟩,
⟨77,550913610,550913989⟩,
⟨128,921036613,921037242⟩]
theorem checked14486 : checkPrefixCuts (2^48) 1902641153 9 Manual.Count131072.C014486.packed 128 cuts14486 = true := by
 decide +kernel
def pointBounds14486 : List (Nat × Nat × Nat) := [(1902659584,95810905725311,95811283451396),(1902720000,95811321275390,95811699001763)]
theorem point_links_checked14486 : (cuts14486.take 2).map (fun c => (1902641153-1+2*2^9*c.k,95810770361780+c.lower,95811148087774+c.upper)) = pointBounds14486 := by
 decide +kernel
def cuts14487 : List PrefixCut := [⟨8,55177336,55177373⟩,
⟨67,472180299,472180617⟩,
⟨126,894051427,894052031⟩,
⟨128,908547463,908548076⟩]
theorem checked14487 : checkPrefixCuts (2^48) 1902772225 9 Manual.Count131072.C014487.packed 128 cuts14487 = true := by
 decide +kernel
def pointBounds14487 : List (Nat × Nat × Nat) := [(1902780416,95811746575729,95812124302389),(1902840832,95812163578692,95812541305633),(1902901248,95812585449820,95812963177047)]
theorem point_links_checked14487 : (cuts14487.take 3).map (fun c => (1902772225-1+2*2^9*c.k,95811691398393+c.lower,95812069125016+c.upper)) = pointBounds14487 := by
 decide +kernel
def cuts14488 : List PrefixCut := [⟨57,403663740,403664014⟩,
⟨116,828318442,828318998⟩,
⟨128,913218173,913218788⟩]
theorem checked14488 : checkPrefixCuts (2^48) 1902903297 9 Manual.Count131072.C014488.packed 128 cuts14488 = true := by
 decide +kernel
def pointBounds14488 : List (Nat × Nat × Nat) := [(1902961664,95813003609596,95813381337106),(1903022080,95813428264298,95813805992090)]
theorem point_links_checked14488 : (cuts14488.take 2).map (fun c => (1902903297-1+2*2^9*c.k,95812599945856+c.lower,95812977673092+c.upper)) = pointBounds14488 := by
 decide +kernel
def cuts14489 : List PrefixCut := [⟨47,328648409,328648635⟩,
⟨106,750909618,750910131⟩,
⟨128,907682699,907683318⟩]
theorem checked14489 : checkPrefixCuts (2^48) 1903034369 9 Manual.Count131072.C014489.packed 128 cuts14489 = true := by
 decide +kernel
def pointBounds14489 : List (Nat × Nat × Nat) := [(1903082496,95813841812438,95814219540515),(1903142912,95814264073647,95814641802011)]
theorem point_links_checked14489 : (cuts14489.take 2).map (fun c => (1903034369-1+2*2^9*c.k,95813513164029+c.lower,95813890891880+c.upper)) = pointBounds14489 := by
 decide +kernel
def cuts14490 : List PrefixCut := [⟨37,266805832,266806009⟩,
⟨96,678983548,678984007⟩,
⟨128,902444374,902444984⟩]
theorem checked14490 : checkPrefixCuts (2^48) 1903165441 9 Manual.Count131072.C014490.packed 128 cuts14490 = true := by
 decide +kernel
def pointBounds14490 : List (Nat × Nat × Nat) := [(1903203328,95814687652560,95815065381207),(1903263744,95815099830276,95815477559205)]
theorem point_links_checked14490 : (cuts14490.take 2).map (fun c => (1903165441-1+2*2^9*c.k,95814420846728+c.lower,95814798575198+c.upper)) = pointBounds14490 := by
 decide +kernel
def cuts14491 : List PrefixCut := [⟨27,188999604,188999732⟩,
⟨86,606622873,606623289⟩,
⟨128,899868116,899868730⟩]
theorem checked14491 : checkPrefixCuts (2^48) 1903296513 9 Manual.Count131072.C014491.packed 128 cuts14491 = true := by
 decide +kernel
def pointBounds14491 : List (Nat × Nat × Nat) := [(1903324160,95815512290706,95815890019914),(1903384576,95815929913975,95816307643471)]
theorem point_links_checked14491 : (cuts14491.take 2).map (fun c => (1903296513-1+2*2^9*c.k,95815323291102+c.lower,95815701020182+c.upper)) = pointBounds14491 := by
 decide +kernel
def cuts14492 : List PrefixCut := [⟨17,118745414,118745494⟩,
⟨76,528800589,528800951⟩,
⟨128,899658014,899658628⟩]
theorem checked14492 : checkPrefixCuts (2^48) 1903427585 9 Manual.Count131072.C014492.packed 128 cuts14492 = true := by
 decide +kernel
def pointBounds14492 : List (Nat × Nat × Nat) := [(1903444992,95816341904632,95816719634406),(1903505408,95816751959807,95817129689863)]
theorem point_links_checked14492 : (cuts14492.take 2).map (fun c => (1903427585-1+2*2^9*c.k,95816223159218+c.lower,95816600888912+c.upper)) = pointBounds14492 := by
 decide +kernel
def cuts14493 : List PrefixCut := [⟨7,49239859,49239894⟩,
⟨66,473316166,473316487⟩,
⟨125,890577430,890578042⟩,
⟨128,914678229,914678856⟩]
theorem checked14493 : checkPrefixCuts (2^48) 1903558657 9 Manual.Count131072.C014493.packed 128 cuts14493 = true := by
 decide +kernel
def pointBounds14493 : List (Nat × Nat × Nat) := [(1903565824,95817172057091,95817549787434),(1903626240,95817596133398,95817973864027),(1903686656,95818013394662,95818391125582)]
theorem point_links_checked14493 : (cuts14493.take 3).map (fun c => (1903558657-1+2*2^9*c.k,95817122817232+c.lower,95817500547540+c.upper)) = pointBounds14493 := by
 decide +kernel
def cuts14494 : List PrefixCut := [⟨56,403053543,403053816⟩,
⟨115,828715775,828716332⟩,
⟨128,916093863,916094480⟩]
theorem checked14494 : checkPrefixCuts (2^48) 1903689729 9 Manual.Count131072.C014494.packed 128 cuts14494 = true := by
 decide +kernel
def pointBounds14494 : List (Nat × Nat × Nat) := [(1903747072,95818440549004,95818818280212),(1903807488,95818866211236,95819243942728)]
theorem point_links_checked14494 : (cuts14494.take 2).map (fun c => (1903689729-1+2*2^9*c.k,95818037495461+c.lower,95818415226396+c.upper)) = pointBounds14494 := by
 decide +kernel
def cuts14495 : List PrefixCut := [⟨46,322155428,322155643⟩,
⟨105,740694330,740694828⟩,
⟨128,905681624,905682234⟩]
theorem checked14495 : checkPrefixCuts (2^48) 1903820801 9 Manual.Count131072.C014495.packed 128 cuts14495 = true := by
 decide +kernel
def pointBounds14495 : List (Nat × Nat × Nat) := [(1903867904,95819275744752,95819653476519),(1903928320,95819694283654,95820072015704)]
theorem point_links_checked14495 : (cuts14495.take 2).map (fun c => (1903820801-1+2*2^9*c.k,95818953589324+c.lower,95819331320876+c.upper)) = pointBounds14495 := by
 decide +kernel
def cuts14496 : List PrefixCut := [⟨36,248659738,248659905⟩,
⟨95,669389530,669389984⟩,
⟨128,907393158,907393776⟩]
theorem checked14496 : checkPrefixCuts (2^48) 1903951873 9 Manual.Count131072.C014496.packed 128 cuts14496 = true := by
 decide +kernel
def pointBounds14496 : List (Nat × Nat × Nat) := [(1903988736,95820107930686,95820485663015),(1904049152,95820528660478,95820906393094)]
theorem point_links_checked14496 : (cuts14496.take 2).map (fun c => (1903951873-1+2*2^9*c.k,95819859270948+c.lower,95820237003110+c.upper)) = pointBounds14496 := by
 decide +kernel
def cuts14497 : List PrefixCut := [⟨26,181678094,181678220⟩,
⟨85,596616115,596616524⟩,
⟨128,905409085,905409705⟩]
theorem checked14497 : checkPrefixCuts (2^48) 1904082945 9 Manual.Count131072.C014497.packed 128 cuts14497 = true := by
 decide +kernel
def pointBounds14497 : List (Nat × Nat × Nat) := [(1904109568,95820948342200,95821326075106),(1904169984,95821363280221,95821741013410)]
theorem point_links_checked14497 : (cuts14497.take 2).map (fun c => (1904082945-1+2*2^9*c.k,95820766664106+c.lower,95821144396886+c.upper)) = pointBounds14497 := by
 decide +kernel
def cuts14498 : List PrefixCut := [⟨16,113375019,113375095⟩,
⟨75,529764838,529765196⟩,
⟨128,907416205,907416819⟩]
theorem checked14498 : checkPrefixCuts (2^48) 1904214017 9 Manual.Count131072.C014498.packed 128 cuts14498 = true := by
 decide +kernel
def pointBounds14498 : List (Nat × Nat × Nat) := [(1904230400,95821785448210,95822163181686),(1904290816,95822201838029,95822579571787)]
theorem point_links_checked14498 : (cuts14498.take 2).map (fun c => (1904214017-1+2*2^9*c.k,95821672073191+c.lower,95822049806591+c.upper)) = pointBounds14498 := by
 decide +kernel
def cuts14499 : List PrefixCut := [⟨6,40498958,40498986⟩,
⟨65,466026227,466026546⟩,
⟨124,885627961,885628560⟩,
⟨128,914743898,914744517⟩]
theorem checked14499 : checkPrefixCuts (2^48) 1904345089 9 Manual.Count131072.C014499.packed 128 cuts14499 = true := by
 decide +kernel
def pointBounds14499 : List (Nat × Nat × Nat) := [(1904351232,95822619988354,95822997722396),(1904411648,95823045515623,95823423249956),(1904472064,95823465117357,95823842851970)]
theorem point_links_checked14499 : (cuts14499.take 3).map (fun c => (1904345089-1+2*2^9*c.k,95822579489396+c.lower,95822957223410+c.upper)) = pointBounds14499 := by
 decide +kernel
def cuts14500 : List PrefixCut := [⟨55,385299797,385300060⟩,
⟨114,806057185,806057739⟩,
⟨128,904778832,904779450⟩]
theorem checked14500 : checkPrefixCuts (2^48) 1904476161 9 Manual.Count131072.C014500.packed 128 cuts14500 = true := by
 decide +kernel
def pointBounds14500 : List (Nat × Nat × Nat) := [(1904532480,95823879533091,95824257267987),(1904592896,95824300290479,95824678025666)]
theorem point_links_checked14500 : (cuts14500.take 2).map (fun c => (1904476161-1+2*2^9*c.k,95823494233294+c.lower,95823871967927+c.upper)) = pointBounds14500 := by
 decide +kernel
def cuts14501 : List PrefixCut := [⟨45,316554484,316554700⟩,
⟨104,729305151,729305645⟩,
⟨128,903386573,903387186⟩]
theorem checked14501 : checkPrefixCuts (2^48) 1904607233 9 Manual.Count131072.C014501.packed 128 cuts14501 = true := by
 decide +kernel
def pointBounds14501 : List (Nat × Nat × Nat) := [(1904653312,95824715566610,95825093302077),(1904713728,95825128317277,95825506053022)]
theorem point_links_checked14501 : (cuts14501.take 2).map (fun c => (1904607233-1+2*2^9*c.k,95824399012126+c.lower,95824776747377+c.upper)) = pointBounds14501 := by
 decide +kernel
def cuts14502 : List PrefixCut := [⟨35,256241398,256241577⟩,
⟨94,666010401,666010860⟩,
⟨128,907757754,907758374⟩]
theorem checked14502 : checkPrefixCuts (2^48) 1904738305 9 Manual.Count131072.C014502.packed 128 cuts14502 = true := by
 decide +kernel
def pointBounds14502 : List (Nat × Nat × Nat) := [(1904774144,95825558640097,95825936376140),(1904834560,95825968409100,95826346145423)]
theorem point_links_checked14502 : (cuts14502.take 2).map (fun c => (1904738305-1+2*2^9*c.k,95825302398699+c.lower,95825680134563+c.upper)) = pointBounds14502 := by
 decide +kernel
def cuts14503 : List PrefixCut := [⟨25,175249257,175249375⟩,
⟨84,598881903,598882306⟩,
⟨128,917742705,917743324⟩]
theorem checked14503 : checkPrefixCuts (2^48) 1904869377 9 Manual.Count131072.C014503.packed 128 cuts14503 = true := by
 decide +kernel
def pointBounds14503 : List (Nat × Nat × Nat) := [(1904894976,95826385405710,95826763142312),(1904955392,95826809038356,95827186775243)]
theorem point_links_checked14503 : (cuts14503.take 2).map (fun c => (1904869377-1+2*2^9*c.k,95826210156453+c.lower,95826587892937+c.upper)) = pointBounds14503 := by
 decide +kernel
def cuts14504 : List PrefixCut := [⟨15,105349465,105349535⟩,
⟨74,524965915,524966272⟩,
⟨128,909996573,909997189⟩]
theorem checked14504 : checkPrefixCuts (2^48) 1905000449 9 Manual.Count131072.C014504.packed 128 cuts14504 = true := by
 decide +kernel
def pointBounds14504 : List (Nat × Nat × Nat) := [(1905015808,95827233248623,95827610985796),(1905076224,95827652865073,95828030602533)]
theorem point_links_checked14504 : (cuts14504.take 2).map (fun c => (1905000449-1+2*2^9*c.k,95827127899158+c.lower,95827505636261+c.upper)) = pointBounds14504 := by
 decide +kernel
def cuts14505 : List PrefixCut := [⟨5,36493127,36493151⟩,
⟨64,448104918,448105221⟩,
⟨123,862658387,862658971⟩,
⟨128,898705894,898706501⟩]
theorem checked14505 : checkPrefixCuts (2^48) 1905131521 9 Manual.Count131072.C014505.packed 128 cuts14505 = true := by
 decide +kernel
def pointBounds14505 : List (Nat × Nat × Nat) := [(1905136640,95828074388858,95828452126601),(1905197056,95828486000649,95828863738671),(1905257472,95828900554118,95829278292421)]
theorem point_links_checked14505 : (cuts14505.take 3).map (fun c => (1905131521-1+2*2^9*c.k,95828037895731+c.lower,95828415633450+c.upper)) = pointBounds14505 := by
 decide +kernel
def cuts14506 : List PrefixCut := [⟨54,380265501,380265761⟩,
⟨113,795974537,795975076⟩,
⟨128,904553084,904553697⟩]
theorem checked14506 : checkPrefixCuts (2^48) 1905262593 9 Manual.Count131072.C014506.packed 128 cuts14506 = true := by
 decide +kernel
def pointBounds14506 : List (Nat × Nat × Nat) := [(1905317888,95829316867126,95829694605712),(1905378304,95829732576162,95830110315027)]
theorem point_links_checked14506 : (cuts14506.take 2).map (fun c => (1905262593-1+2*2^9*c.k,95828936601625+c.lower,95829314339951+c.upper)) = pointBounds14506 := by
 decide +kernel
def cuts14507 : List PrefixCut := [⟨44,310810421,310810634⟩,
⟨103,723095488,723095983⟩,
⟨128,899763995,899764610⟩]
theorem checked14507 : checkPrefixCuts (2^48) 1905393665 9 Manual.Count131072.C014507.packed 128 cuts14507 = true := by
 decide +kernel
def pointBounds14507 : List (Nat × Nat × Nat) := [(1905438720,95830151965130,95830529704282),(1905499136,95830564250197,95830941989631)]
theorem point_links_checked14507 : (cuts14507.take 2).map (fun c => (1905393665-1+2*2^9*c.k,95829841154709+c.lower,95830218893648+c.upper)) = pointBounds14507 := by
 decide +kernel
def cuts14508 : List PrefixCut := [⟨34,238705519,238705682⟩,
⟨93,647714847,647715298⟩,
⟨128,896009269,896009890⟩]
theorem checked14508 : checkPrefixCuts (2^48) 1905524737 9 Manual.Count131072.C014508.packed 128 cuts14508 = true := by
 decide +kernel
def pointBounds14508 : List (Nat × Nat × Nat) := [(1905559552,95830979624223,95831357363940),(1905619968,95831388633551,95831766373556)]
theorem point_links_checked14508 : (cuts14508.take 2).map (fun c => (1905524737-1+2*2^9*c.k,95830740918704+c.lower,95831118658258+c.upper)) = pointBounds14508 := by
 decide +kernel
def cuts14509 : List PrefixCut := [⟨24,169859643,169859757⟩,
⟨83,590658998,590659401⟩,
⟨128,915443879,915444498⟩]
theorem checked14509 : checkPrefixCuts (2^48) 1905655809 9 Manual.Count131072.C014509.packed 128 cuts14509 = true := by
 decide +kernel
def pointBounds14509 : List (Nat × Nat × Nat) := [(1905680384,95831806787616,95832184527905),(1905740800,95832227586971,95832605327549)]
theorem point_links_checked14509 : (cuts14509.take 2).map (fun c => (1905655809-1+2*2^9*c.k,95831636927973+c.lower,95832014668148+c.upper)) = pointBounds14509 := by
 decide +kernel
def cuts14510 : List PrefixCut := [⟨14,95410508,95410572⟩,
⟨73,519284735,519285087⟩,
⟨128,918334606,918335228⟩]
theorem checked14510 : checkPrefixCuts (2^48) 1905786881 9 Manual.Count131072.C014510.packed 128 cuts14510 = true := by
 decide +kernel
def pointBounds14510 : List (Nat × Nat × Nat) := [(1905801216,95832647782360,95833025523218),(1905861632,95833071656587,95833449397733)]
theorem point_links_checked14510 : (cuts14510.take 2).map (fun c => (1905786881-1+2*2^9*c.k,95832552371852+c.lower,95832930112646+c.upper)) = pointBounds14510 := by
 decide +kernel
def cuts14511 : List PrefixCut := [⟨4,29832274,29832294⟩,
⟨63,448215419,448215720⟩,
⟨122,857281696,857282271⟩,
⟨128,901731801,901732406⟩]
theorem checked14511 : checkPrefixCuts (2^48) 1905917953 9 Manual.Count131072.C014511.packed 128 cuts14511 = true := by
 decide +kernel
def pointBounds14511 : List (Nat × Nat × Nat) := [(1905922048,95833500538732,95833878280168),(1905982464,95833918921877,95834296663594),(1906042880,95834327988154,95834705730145)]
theorem point_links_checked14511 : (cuts14511.take 3).map (fun c => (1905917953-1+2*2^9*c.k,95833470706458+c.lower,95833848447874+c.upper)) = pointBounds14511 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000140
