import PlattAssemblyKernel
import PlattCertificates.Count131072.C024512
import PlattCertificates.Count131072.C024513
import PlattCertificates.Count131072.C024514
import PlattCertificates.Count131072.C024515
import PlattCertificates.Count131072.C024516
import PlattCertificates.Count131072.C024517
import PlattCertificates.Count131072.C024518
import PlattCertificates.Count131072.C024519
import PlattCertificates.Count131072.C024520
import PlattCertificates.Count131072.C024521
import PlattCertificates.Count131072.C024522
import PlattCertificates.Count131072.C024523
import PlattCertificates.Count131072.C024524
import PlattCertificates.Count131072.C024525
import PlattCertificates.Count131072.C024526
import PlattCertificates.Count131072.C024527
import PlattCertificates.Count131072.C024528
import PlattCertificates.Count131072.C024529
import PlattCertificates.Count131072.C024530
import PlattCertificates.Count131072.C024531
import PlattCertificates.Count131072.C024532
import PlattCertificates.Count131072.C024533
import PlattCertificates.Count131072.C024534
import PlattCertificates.Count131072.C024535
import PlattCertificates.Count131072.C024536
import PlattCertificates.Count131072.C024537
import PlattCertificates.Count131072.C024538
import PlattCertificates.Count131072.C024539
import PlattCertificates.Count131072.C024540
import PlattCertificates.Count131072.C024541
import PlattCertificates.Count131072.C024542
import PlattCertificates.Count131072.C024543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000141
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24512 : List PrefixCut := [⟨56,231266693,231266827⟩,
⟨128,530341034,530341335⟩]
theorem checked24512 : checkPrefixCuts (2^48) 3216769025 9 Manual.Count131072.C024512.packed 128 cuts24512 = true := by
 decide +kernel
def pointBounds24512 : List (Nat × Nat × Nat) := [(3216826368,102645253073748,102645634948153)]
theorem point_links_checked24512 : (cuts24512.take 1).map (fun c => (3216769025-1+2*2^9*c.k,102645021807055+c.lower,102645403681326+c.upper)) = pointBounds24512 := by
 decide +kernel
def cuts24513 : List PrefixCut := [⟨27,114360437,114360501⟩,
⟨126,526294723,526295019⟩,
⟨128,534694269,534694569⟩]
theorem checked24513 : checkPrefixCuts (2^48) 3216900097 9 Manual.Count131072.C024513.packed 128 cuts24513 = true := by
 decide +kernel
def pointBounds24513 : List (Nat × Nat × Nat) := [(3216927744,102645666508526,102646048383162),(3217029120,102646078442812,102646460317680)]
theorem point_links_checked24513 : (cuts24513.take 2).map (fun c => (3216900097-1+2*2^9*c.k,102645552148089+c.lower,102645934022661+c.upper)) = pointBounds24513 := by
 decide +kernel
def cuts24514 : List PrefixCut := [⟨97,395559887,395560106⟩,
⟨128,518486279,518486567⟩]
theorem checked24514 : checkPrefixCuts (2^48) 3217031169 9 Manual.Count131072.C024514.packed 128 cuts24514 = true := by
 decide +kernel
def pointBounds24514 : List (Nat × Nat × Nat) := [(3217130496,102646482402245,102646864277336)]
theorem point_links_checked24514 : (cuts24514.take 1).map (fun c => (3217031169-1+2*2^9*c.k,102646086842358+c.lower,102646468717230+c.upper)) = pointBounds24514 := by
 decide +kernel
def cuts24515 : List PrefixCut := [⟨68,278570507,278570667⟩,
⟨128,524851914,524852212⟩]
theorem checked24515 : checkPrefixCuts (2^48) 3217162241 9 Manual.Count131072.C024515.packed 128 cuts24515 = true := by
 decide +kernel
def pointBounds24515 : List (Nat × Nat × Nat) := [(3217231872,102646883899144,102647265774464)]
theorem point_links_checked24515 : (cuts24515.take 1).map (fun c => (3217162241-1+2*2^9*c.k,102646605328637+c.lower,102646987203797+c.upper)) = pointBounds24515 := by
 decide +kernel
def cuts24516 : List PrefixCut := [⟨39,161327073,161327161⟩,
⟨128,524393074,524393368⟩]
theorem checked24516 : checkPrefixCuts (2^48) 3217293313 9 Manual.Count131072.C024516.packed 128 cuts24516 = true := by
 decide +kernel
def pointBounds24516 : List (Nat × Nat × Nat) := [(3217333248,102647291507624,102647673383170)]
theorem point_links_checked24516 : (cuts24516.take 1).map (fun c => (3217293313-1+2*2^9*c.k,102647130180551+c.lower,102647512056009+c.upper)) = pointBounds24516 := by
 decide +kernel
def cuts24517 : List PrefixCut := [⟨10,40767731,40767753⟩,
⟨109,450187570,450187819⟩,
⟨128,525508916,525509207⟩]
theorem checked24517 : checkPrefixCuts (2^48) 3217424385 9 Manual.Count131072.C024517.packed 128 cuts24517 = true := by
 decide +kernel
def pointBounds24517 : List (Nat × Nat × Nat) := [(3217434624,102647695341356,102648077217130),(3217536000,102648104761195,102648486637196)]
theorem point_links_checked24517 : (cuts24517.take 2).map (fun c => (3217424385-1+2*2^9*c.k,102647654573625+c.lower,102648036449377+c.upper)) = pointBounds24517 := by
 decide +kernel
def cuts24518 : List PrefixCut := [⟨80,333298275,333298471⟩,
⟨128,527937038,527937344⟩]
theorem checked24518 : checkPrefixCuts (2^48) 3217555457 9 Manual.Count131072.C024518.packed 128 cuts24518 = true := by
 decide +kernel
def pointBounds24518 : List (Nat × Nat × Nat) := [(3217637376,102648513380816,102648895257055)]
theorem point_links_checked24518 : (cuts24518.take 1).map (fun c => (3217555457-1+2*2^9*c.k,102648180082541+c.lower,102648561958584+c.upper)) = pointBounds24518 := by
 decide +kernel
def cuts24519 : List PrefixCut := [⟨51,210119054,210119169⟩,
⟨128,522317085,522317376⟩]
theorem checked24519 : checkPrefixCuts (2^48) 3217686529 9 Manual.Count131072.C024519.packed 128 cuts24519 = true := by
 decide +kernel
def pointBounds24519 : List (Nat × Nat × Nat) := [(3217738752,102648918138633,102649300015097)]
theorem point_links_checked24519 : (cuts24519.take 1).map (fun c => (3217686529-1+2*2^9*c.k,102648708019579+c.lower,102649089895928+c.upper)) = pointBounds24519 := by
 decide +kernel
def cuts24520 : List PrefixCut := [⟨22,87735961,87736013⟩,
⟨121,488969426,488969707⟩,
⟨128,516260186,516260483⟩]
theorem checked24520 : checkPrefixCuts (2^48) 3217817601 9 Manual.Count131072.C024520.packed 128 cuts24520 = true := by
 decide +kernel
def pointBounds24520 : List (Nat × Nat × Nat) := [(3217840128,102649318072625,102649699949317),(3217941504,102649719306090,102650101183011)]
theorem point_links_checked24520 : (cuts24520.take 2).map (fun c => (3217817601-1+2*2^9*c.k,102649230336664+c.lower,102649612213304+c.upper)) = pointBounds24520 := by
 decide +kernel
def cuts24521 : List PrefixCut := [⟨92,367632292,367632500⟩,
⟨128,515102029,515102322⟩]
theorem checked24521 : checkPrefixCuts (2^48) 3217948673 9 Manual.Count131072.C024521.packed 128 cuts24521 = true := by
 decide +kernel
def pointBounds24521 : List (Nat × Nat × Nat) := [(3218042880,102650114229142,102650496106287)]
theorem point_links_checked24521 : (cuts24521.take 1).map (fun c => (3217948673-1+2*2^9*c.k,102649746596850+c.lower,102650128473787+c.upper)) = pointBounds24521 := by
 decide +kernel
def cuts24522 : List PrefixCut := [⟨63,254875478,254875624⟩,
⟨128,523215235,523215535⟩]
theorem checked24522 : checkPrefixCuts (2^48) 3218079745 9 Manual.Count131072.C024522.packed 128 cuts24522 = true := by
 decide +kernel
def pointBounds24522 : List (Nat × Nat × Nat) := [(3218144256,102650516574357,102650898451733)]
theorem point_links_checked24522 : (cuts24522.take 1).map (fun c => (3218079745-1+2*2^9*c.k,102650261698879+c.lower,102650643576109+c.upper)) = pointBounds24522 := by
 decide +kernel
def cuts24523 : List PrefixCut := [⟨34,141427161,141427240⟩,
⟨128,531152899,531153198⟩]
theorem checked24523 : checkPrefixCuts (2^48) 3218210817 9 Manual.Count131072.C024523.packed 128 cuts24523 = true := by
 decide +kernel
def pointBounds24523 : List (Nat × Nat × Nat) := [(3218245632,102650926341275,102651308218884)]
theorem point_links_checked24523 : (cuts24523.take 1).map (fun c => (3218210817-1+2*2^9*c.k,102650784914114+c.lower,102651166791644+c.upper)) = pointBounds24523 := by
 decide +kernel
def cuts24524 : List PrefixCut := [⟨5,20902828,20902839⟩,
⟨104,432917874,432918113⟩,
⟨128,528857522,528857818⟩]
theorem checked24524 : checkPrefixCuts (2^48) 3218341889 9 Manual.Count131072.C024524.packed 128 cuts24524 = true := by
 decide +kernel
def pointBounds24524 : List (Nat × Nat × Nat) := [(3218347008,102651336969841,102651718847681),(3218448384,102651748984887,102652130862955)]
theorem point_links_checked24524 : (cuts24524.take 2).map (fun c => (3218341889-1+2*2^9*c.k,102651316067013+c.lower,102651697944842+c.upper)) = pointBounds24524 := by
 decide +kernel
def cuts24525 : List PrefixCut := [⟨75,306529767,306529940⟩,
⟨128,524288250,524288552⟩]
theorem checked24525 : checkPrefixCuts (2^48) 3218472961 9 Manual.Count131072.C024525.packed 128 cuts24525 = true := by
 decide +kernel
def pointBounds24525 : List (Nat × Nat × Nat) := [(3218549760,102652151454302,102652533332600)]
theorem point_links_checked24525 : (cuts24525.take 1).map (fun c => (3218472961-1+2*2^9*c.k,102651844924535+c.lower,102652226802660+c.upper)) = pointBounds24525 := by
 decide +kernel
def cuts24526 : List PrefixCut := [⟨46,187059468,187059576⟩,
⟨128,522430438,522430729⟩]
theorem checked24526 : checkPrefixCuts (2^48) 3218604033 9 Manual.Count131072.C024526.packed 128 cuts24526 = true := by
 decide +kernel
def pointBounds24526 : List (Nat × Nat × Nat) := [(3218651136,102652556272253,102652938150788)]
theorem point_links_checked24526 : (cuts24526.take 1).map (fun c => (3218604033-1+2*2^9*c.k,102652369212785+c.lower,102652751091212+c.upper)) = pointBounds24526 := by
 decide +kernel
def cuts24527 : List PrefixCut := [⟨17,68384872,68384908⟩,
⟨116,472915048,472915309⟩,
⟨128,522234323,522234611⟩]
theorem checked24527 : checkPrefixCuts (2^48) 3218735105 9 Manual.Count131072.C024527.packed 128 cuts24527 = true := by
 decide +kernel
def pointBounds24527 : List (Nat × Nat × Nat) := [(3218752512,102652960028095,102653341906849),(3218853888,102653364558271,102653746437250)]
theorem point_links_checked24527 : (cuts24527.take 2).map (fun c => (3218735105-1+2*2^9*c.k,102652891643223+c.lower,102653273521941+c.upper)) = pointBounds24527 := by
 decide +kernel
def cuts24528 : List PrefixCut := [⟨87,360007552,360007747⟩,
⟨128,527809447,527809737⟩]
theorem checked24528 : checkPrefixCuts (2^48) 3218866177 9 Manual.Count131072.C024528.packed 128 cuts24528 = true := by
 decide +kernel
def pointBounds24528 : List (Nat × Nat × Nat) := [(3218955264,102653773885098,102654155764299)]
theorem point_links_checked24528 : (cuts24528.take 1).map (fun c => (3218866177-1+2*2^9*c.k,102653413877546+c.lower,102653795756552+c.upper)) = pointBounds24528 := by
 decide +kernel
def cuts24529 : List PrefixCut := [⟨58,232243300,232243432⟩,
⟨128,521492212,521492500⟩]
theorem checked24529 : checkPrefixCuts (2^48) 3218997249 9 Manual.Count131072.C024529.packed 128 cuts24529 = true := by
 decide +kernel
def pointBounds24529 : List (Nat × Nat × Nat) := [(3219056640,102654173930293,102654555809721)]
theorem point_links_checked24529 : (cuts24529.take 1).map (fun c => (3218997249-1+2*2^9*c.k,102653941686993+c.lower,102654323566289+c.upper)) = pointBounds24529 := by
 decide +kernel
def cuts24530 : List PrefixCut := [⟨29,117429008,117429073⟩,
⟨128,522432829,522433121⟩]
theorem checked24530 : checkPrefixCuts (2^48) 3219128321 9 Manual.Count131072.C024530.packed 128 cuts24530 = true := by
 decide +kernel
def pointBounds24530 : List (Nat × Nat × Nat) := [(3219158016,102654580608213,102654962487862),(3219259392,102654985612034,102655367491910)]
theorem point_links_checked24530 : (cuts24530.take 2).map (fun c => (3219128321-1+2*2^9*c.k,102654463179205+c.lower,102654845058789+c.upper)) = pointBounds24530 := by
 decide +kernel
def cuts24531 : List PrefixCut := [⟨99,404291633,404291858⟩,
⟨128,521799598,521799892⟩]
theorem checked24531 : checkPrefixCuts (2^48) 3219259393 9 Manual.Count131072.C024531.packed 128 cuts24531 = true := by
 decide +kernel
def pointBounds24531 : List (Nat × Nat × Nat) := [(3219360768,102655389903667,102655771783768)]
theorem point_links_checked24531 : (cuts24531.take 1).map (fun c => (3219259393-1+2*2^9*c.k,102654985612034+c.lower,102655367491910+c.upper)) = pointBounds24531 := by
 decide +kernel
def cuts24532 : List PrefixCut := [⟨70,280038787,280038948⟩,
⟨128,518980512,518980809⟩]
theorem checked24532 : checkPrefixCuts (2^48) 3219390465 9 Manual.Count131072.C024532.packed 128 cuts24532 = true := by
 decide +kernel
def pointBounds24532 : List (Nat × Nat × Nat) := [(3219462144,102655787450419,102656169330750)]
theorem point_links_checked24532 : (cuts24532.take 1).map (fun c => (3219390465-1+2*2^9*c.k,102655507411632+c.lower,102655889291802+c.upper)) = pointBounds24532 := by
 decide +kernel
def cuts24533 : List PrefixCut := [⟨41,165062142,165062236⟩,
⟨128,515986940,515987233⟩]
theorem checked24533 : checkPrefixCuts (2^48) 3219521537 9 Manual.Count131072.C024533.packed 128 cuts24533 = true := by
 decide +kernel
def pointBounds24533 : List (Nat × Nat × Nat) := [(3219563520,102656191454286,102656573334847)]
theorem point_links_checked24533 : (cuts24533.take 1).map (fun c => (3219521537-1+2*2^9*c.k,102656026392144+c.lower,102656408272611+c.upper)) = pointBounds24533 := by
 decide +kernel
def cuts24534 : List PrefixCut := [⟨12,46334628,46334656⟩,
⟨111,448914264,448914520⟩,
⟨128,514829450,514829743⟩]
theorem checked24534 : checkPrefixCuts (2^48) 3219652609 9 Manual.Count131072.C024534.packed 128 cuts24534 = true := by
 decide +kernel
def pointBounds24534 : List (Nat × Nat × Nat) := [(3219664896,102656588713712,102656970594500),(3219766272,102656991293348,102657373174364)]
theorem point_links_checked24534 : (cuts24534.take 2).map (fun c => (3219652609-1+2*2^9*c.k,102656542379084+c.lower,102656924259844+c.upper)) = pointBounds24534 := by
 decide +kernel
def cuts24535 : List PrefixCut := [⟨82,329832982,329833167⟩,
⟨128,515857466,515857752⟩]
theorem checked24535 : checkPrefixCuts (2^48) 3219783681 9 Manual.Count131072.C024535.packed 128 cuts24535 = true := by
 decide +kernel
def pointBounds24535 : List (Nat × Nat × Nat) := [(3219867648,102657387041516,102657768922754)]
theorem point_links_checked24535 : (cuts24535.take 1).map (fun c => (3219783681-1+2*2^9*c.k,102657057208534+c.lower,102657439089587+c.upper)) = pointBounds24535 := by
 decide +kernel
def cuts24536 : List PrefixCut := [⟨53,214606633,214606757⟩,
⟨128,524577965,524578263⟩]
theorem checked24536 : checkPrefixCuts (2^48) 3219914753 9 Manual.Count131072.C024536.packed 128 cuts24536 = true := by
 decide +kernel
def pointBounds24536 : List (Nat × Nat × Nat) := [(3219969024,102657787672633,102658169554096)]
theorem point_links_checked24536 : (cuts24536.take 1).map (fun c => (3219914753-1+2*2^9*c.k,102657573066000+c.lower,102657954947339+c.upper)) = pointBounds24536 := by
 decide +kernel
def cuts24537 : List PrefixCut := [⟨24,100787171,100787226⟩,
⟨123,504190197,504190479⟩,
⟨128,523158129,523158423⟩]
theorem checked24537 : checkPrefixCuts (2^48) 3220045825 9 Manual.Count131072.C024537.packed 128 cuts24537 = true := by
 decide +kernel
def pointBounds24537 : List (Nat × Nat × Nat) := [(3220070400,102658198431136,102658580312828),(3220171776,102658601834162,102658983716081)]
theorem point_links_checked24537 : (cuts24537.take 2).map (fun c => (3220045825-1+2*2^9*c.k,102658097643965+c.lower,102658479525602+c.upper)) = pointBounds24537 := by
 decide +kernel
def cuts24538 : List PrefixCut := [⟨94,382237198,382237418⟩,
⟨128,522000466,522000764⟩]
theorem checked24538 : checkPrefixCuts (2^48) 3220176897 9 Manual.Count131072.C024538.packed 128 cuts24538 = true := by
 decide +kernel
def pointBounds24538 : List (Nat × Nat × Nat) := [(3220273152,102659003039292,102659384921443)]
theorem point_links_checked24538 : (cuts24538.take 1).map (fun c => (3220176897-1+2*2^9*c.k,102658620802094+c.lower,102659002684025+c.upper)) = pointBounds24538 := by
 decide +kernel
def cuts24539 : List PrefixCut := [⟨65,261516620,261516771⟩,
⟨128,512102502,512102798⟩]
theorem checked24539 : checkPrefixCuts (2^48) 3220307969 9 Manual.Count131072.C024539.packed 128 cuts24539 = true := by
 decide +kernel
def pointBounds24539 : List (Nat × Nat × Nat) := [(3220374528,102659404319180,102659786201560)]
theorem point_links_checked24539 : (cuts24539.take 1).map (fun c => (3220307969-1+2*2^9*c.k,102659142802560+c.lower,102659524684789+c.upper)) = pointBounds24539 := by
 decide +kernel
def cuts24540 : List PrefixCut := [⟨36,146311195,146311276⟩,
⟨128,525366599,525366885⟩]
theorem checked24540 : checkPrefixCuts (2^48) 3220439041 9 Manual.Count131072.C024540.packed 128 cuts24540 = true := by
 decide +kernel
def pointBounds24540 : List (Nat × Nat × Nat) := [(3220475904,102659801216257,102660183098863)]
theorem point_links_checked24540 : (cuts24540.take 1).map (fun c => (3220439041-1+2*2^9*c.k,102659654905062+c.lower,102660036787587+c.upper)) = pointBounds24540 := by
 decide +kernel
def cuts24541 : List PrefixCut := [⟨7,26918890,26918905⟩,
⟨106,433929101,433929341⟩,
⟨128,524121604,524121893⟩]
theorem checked24541 : checkPrefixCuts (2^48) 3220570113 9 Manual.Count131072.C024541.packed 128 cuts24541 = true := by
 decide +kernel
def pointBounds24541 : List (Nat × Nat × Nat) := [(3220577280,102660207190551,102660589073377),(3220678656,102660614200762,102660996083813)]
theorem point_links_checked24541 : (cuts24541.take 2).map (fun c => (3220570113-1+2*2^9*c.k,102660180271661+c.lower,102660562154472+c.upper)) = pointBounds24541 := by
 decide +kernel
def cuts24542 : List PrefixCut := [⟨77,320213306,320213484⟩,
⟨128,527858327,527858624⟩]
theorem checked24542 : checkPrefixCuts (2^48) 3220701185 9 Manual.Count131072.C024542.packed 128 cuts24542 = true := by
 decide +kernel
def pointBounds24542 : List (Nat × Nat × Nat) := [(3220780032,102661024606571,102661406489849)]
theorem point_links_checked24542 : (cuts24542.take 1).map (fun c => (3220701185-1+2*2^9*c.k,102660704393265+c.lower,102661086276365+c.upper)) = pointBounds24542 := by
 decide +kernel
def cuts24543 : List PrefixCut := [⟨48,192523062,192523168⟩,
⟨128,521894226,521894517⟩]
theorem checked24543 : checkPrefixCuts (2^48) 3220832257 9 Manual.Count131072.C024543.packed 128 cuts24543 = true := by
 decide +kernel
def pointBounds24543 : List (Nat × Nat × Nat) := [(3220881408,102661424774654,102661806658157)]
theorem point_links_checked24543 : (cuts24543.take 1).map (fun c => (3220832257-1+2*2^9*c.k,102661232251592+c.lower,102661614134989+c.upper)) = pointBounds24543 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000141
