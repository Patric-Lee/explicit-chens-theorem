import PlattAssemblyKernel
import PlattCertificates.Count131072.C038512
import PlattCertificates.Count131072.C038513
import PlattCertificates.Count131072.C038514
import PlattCertificates.Count131072.C038515
import PlattCertificates.Count131072.C038516
import PlattCertificates.Count131072.C038517
import PlattCertificates.Count131072.C038518
import PlattCertificates.Count131072.C038519
import PlattCertificates.Count131072.C038520
import PlattCertificates.Count131072.C038521
import PlattCertificates.Count131072.C038522
import PlattCertificates.Count131072.C038523
import PlattCertificates.Count131072.C038524
import PlattCertificates.Count131072.C038525
import PlattCertificates.Count131072.C038526
import PlattCertificates.Count131072.C038527
import PlattCertificates.Count131072.C038528
import PlattCertificates.Count131072.C038529
import PlattCertificates.Count131072.C038530
import PlattCertificates.Count131072.C038531
import PlattCertificates.Count131072.C038532
import PlattCertificates.Count131072.C038533
import PlattCertificates.Count131072.C038534
import PlattCertificates.Count131072.C038535
import PlattCertificates.Count131072.C038536
import PlattCertificates.Count131072.C038537
import PlattCertificates.Count131072.C038538
import PlattCertificates.Count131072.C038539
import PlattCertificates.Count131072.C038540
import PlattCertificates.Count131072.C038541
import PlattCertificates.Count131072.C038542
import PlattCertificates.Count131072.C038543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000266
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts38512 : List PrefixCut := [⟨64,327283268,327283469⟩]
theorem checked38512 : checkPrefixCuts (2^48) 5051777025 10 Manual.Count131072.C038512.packed 64 cuts38512 = true := by
 decide +kernel
def cuts38513 : List PrefixCut := [⟨9,45408904,45408931⟩,
⟨64,329949126,329949329⟩]
theorem checked38513 : checkPrefixCuts (2^48) 5051908097 10 Manual.Count131072.C038513.packed 64 cuts38513 = true := by
 decide +kernel
def pointBounds38513 : List (Nat × Nat × Nat) := [(5051926528,108389761975911,108390147196878)]
theorem point_links_checked38513 : (cuts38513.take 1).map (fun c => (5051908097-1+2*2^10*c.k,108389716567007+c.lower,108390101787947+c.upper)) = pointBounds38513 := by
 decide +kernel
def cuts38514 : List PrefixCut := [⟨23,117279746,117279815⟩,
⟨64,323589153,323589348⟩]
theorem checked38514 : checkPrefixCuts (2^48) 5052039169 10 Manual.Count131072.C038514.packed 64 cuts38514 = true := by
 decide +kernel
def pointBounds38514 : List (Nat × Nat × Nat) := [(5052086272,108390163795879,108390549017091)]
theorem point_links_checked38514 : (cuts38514.take 1).map (fun c => (5052039169-1+2*2^10*c.k,108390046516133+c.lower,108390431737276+c.upper)) = pointBounds38514 := by
 decide +kernel
def cuts38515 : List PrefixCut := [⟨37,191263552,191263661⟩,
⟨64,329040602,329040793⟩]
theorem checked38515 : checkPrefixCuts (2^48) 5052170241 10 Manual.Count131072.C038515.packed 64 cuts38515 = true := by
 decide +kernel
def pointBounds38515 : List (Nat × Nat × Nat) := [(5052246016,108390561368838,108390946590285)]
theorem point_links_checked38515 : (cuts38515.take 1).map (fun c => (5052170241-1+2*2^10*c.k,108390370105286+c.lower,108390755326624+c.upper)) = pointBounds38515 := by
 decide +kernel
def cuts38516 : List PrefixCut := [⟨51,257053481,257053637⟩,
⟨64,325466485,325466682⟩]
theorem checked38516 : checkPrefixCuts (2^48) 5052301313 10 Manual.Count131072.C038516.packed 64 cuts38516 = true := by
 decide +kernel
def pointBounds38516 : List (Nat × Nat × Nat) := [(5052405760,108390956199369,108391341421054)]
theorem point_links_checked38516 : (cuts38516.take 1).map (fun c => (5052301313-1+2*2^10*c.k,108390699145888+c.lower,108391084367417+c.upper)) = pointBounds38516 := by
 decide +kernel
def cuts38517 : List PrefixCut := [⟨64,331753300,331753502⟩]
theorem checked38517 : checkPrefixCuts (2^48) 5052432385 10 Manual.Count131072.C038517.packed 64 cuts38517 = true := by
 decide +kernel
def cuts38518 : List PrefixCut := [⟨1,5626641,5626644⟩,
⟨64,327956525,327956725⟩]
theorem checked38518 : checkPrefixCuts (2^48) 5052563457 10 Manual.Count131072.C038518.packed 64 cuts38518 = true := by
 decide +kernel
def pointBounds38518 : List (Nat × Nat × Nat) := [(5052565504,108391361992314,108391747214245)]
theorem point_links_checked38518 : (cuts38518.take 1).map (fun c => (5052563457-1+2*2^10*c.k,108391356365673+c.lower,108391741587601+c.upper)) = pointBounds38518 := by
 decide +kernel
def cuts38519 : List PrefixCut := [⟨15,78269336,78269383⟩,
⟨64,325775454,325775652⟩]
theorem checked38519 : checkPrefixCuts (2^48) 5052694529 10 Manual.Count131072.C038519.packed 64 cuts38519 = true := by
 decide +kernel
def pointBounds38519 : List (Nat × Nat × Nat) := [(5052725248,108391762591534,108392147813709)]
theorem point_links_checked38519 : (cuts38519.take 1).map (fun c => (5052694529-1+2*2^10*c.k,108391684322198+c.lower,108392069544326+c.upper)) = pointBounds38519 := by
 decide +kernel
def cuts38520 : List PrefixCut := [⟨29,146785582,146785672⟩,
⟨64,326602544,326602741⟩]
theorem checked38520 : checkPrefixCuts (2^48) 5052825601 10 Manual.Count131072.C038520.packed 64 cuts38520 = true := by
 decide +kernel
def pointBounds38520 : List (Nat × Nat × Nat) := [(5052884992,108392156883234,108392542105650)]
theorem point_links_checked38520 : (cuts38520.take 1).map (fun c => (5052825601-1+2*2^10*c.k,108392010097652+c.lower,108392395319978+c.upper)) = pointBounds38520 := by
 decide +kernel
def cuts38521 : List PrefixCut := [⟨43,223653575,223653708⟩,
⟨64,332777282,332777479⟩]
theorem checked38521 : checkPrefixCuts (2^48) 5052956673 10 Manual.Count131072.C038521.packed 64 cuts38521 = true := by
 decide +kernel
def pointBounds38521 : List (Nat × Nat × Nat) := [(5053044736,108392560353771,108392945576427)]
theorem point_links_checked38521 : (cuts38521.take 1).map (fun c => (5052956673-1+2*2^10*c.k,108392336700196+c.lower,108392721922719+c.upper)) = pointBounds38521 := by
 decide +kernel
def cuts38522 : List PrefixCut := [⟨57,288875254,288875430⟩,
⟨64,326140012,326140211⟩]
theorem checked38522 : checkPrefixCuts (2^48) 5053087745 10 Manual.Count131072.C038522.packed 64 cuts38522 = true := by
 decide +kernel
def pointBounds38522 : List (Nat × Nat × Nat) := [(5053204480,108392958352732,108393343575628)]
theorem point_links_checked38522 : (cuts38522.take 1).map (fun c => (5053087745-1+2*2^10*c.k,108392669477478+c.lower,108393054700198+c.upper)) = pointBounds38522 := by
 decide +kernel
def cuts38523 : List PrefixCut := [⟨64,325463139,325463336⟩]
theorem checked38523 : checkPrefixCuts (2^48) 5053218817 10 Manual.Count131072.C038523.packed 64 cuts38523 = true := by
 decide +kernel
def cuts38524 : List PrefixCut := [⟨7,35815471,35815491⟩,
⟨64,330022075,330022272⟩]
theorem checked38524 : checkPrefixCuts (2^48) 5053349889 10 Manual.Count131072.C038524.packed 64 cuts38524 = true := by
 decide +kernel
def pointBounds38524 : List (Nat × Nat × Nat) := [(5053364224,108393356896100,108393742119236)]
theorem point_links_checked38524 : (cuts38524.take 1).map (fun c => (5053349889-1+2*2^10*c.k,108393321080629+c.lower,108393706303745+c.upper)) = pointBounds38524 := by
 decide +kernel
def cuts38525 : List PrefixCut := [⟨21,105215361,105215423⟩,
⟨64,321046080,321046269⟩]
theorem checked38525 : checkPrefixCuts (2^48) 5053480961 10 Manual.Count131072.C038525.packed 64 cuts38525 = true := by
 decide +kernel
def pointBounds38525 : List (Nat × Nat × Nat) := [(5053523968,108393756318065,108394141541440)]
theorem point_links_checked38525 : (cuts38525.take 1).map (fun c => (5053480961-1+2*2^10*c.k,108393651102704+c.lower,108394036326017+c.upper)) = pointBounds38525 := by
 decide +kernel
def cuts38526 : List PrefixCut := [⟨35,177786004,177786110⟩,
⟨64,325660597,325660792⟩]
theorem checked38526 : checkPrefixCuts (2^48) 5053612033 10 Manual.Count131072.C038526.packed 64 cuts38526 = true := by
 decide +kernel
def pointBounds38526 : List (Nat × Nat × Nat) := [(5053683712,108394149934788,108394535158396)]
theorem point_links_checked38526 : (cuts38526.take 1).map (fun c => (5053612033-1+2*2^10*c.k,108393972148784+c.lower,108394357372286+c.upper)) = pointBounds38526 := by
 decide +kernel
def cuts38527 : List PrefixCut := [⟨49,251243596,251243747⟩,
⟨64,328604016,328604212⟩]
theorem checked38527 : checkPrefixCuts (2^48) 5053743105 10 Manual.Count131072.C038527.packed 64 cuts38527 = true := by
 decide +kernel
def pointBounds38527 : List (Nat × Nat × Nat) := [(5053843456,108394549052977,108394934276825)]
theorem point_links_checked38527 : (cuts38527.take 1).map (fun c => (5053743105-1+2*2^10*c.k,108394297809381+c.lower,108394683033078+c.upper)) = pointBounds38527 := by
 decide +kernel
def cuts38528 : List PrefixCut := [⟨63,321355343,321355535⟩,
⟨64,326144979,326145174⟩]
theorem checked38528 : checkPrefixCuts (2^48) 5053874177 10 Manual.Count131072.C038528.packed 64 cuts38528 = true := by
 decide +kernel
def pointBounds38528 : List (Nat × Nat × Nat) := [(5054003200,108394947768740,108395332992825)]
theorem point_links_checked38528 : (cuts38528.take 1).map (fun c => (5053874177-1+2*2^10*c.k,108394626413397+c.lower,108395011637290+c.upper)) = pointBounds38528 := by
 decide +kernel
def cuts38529 : List PrefixCut := [⟨64,325969440,325969637⟩]
theorem checked38529 : checkPrefixCuts (2^48) 5054005249 10 Manual.Count131072.C038529.packed 64 cuts38529 = true := by
 decide +kernel
def cuts38530 : List PrefixCut := [⟨13,68055427,68055468⟩,
⟨64,327297573,327297769⟩]
theorem checked38530 : checkPrefixCuts (2^48) 5054136321 10 Manual.Count131072.C038530.packed 64 cuts38530 = true := by
 decide +kernel
def pointBounds38530 : List (Nat × Nat × Nat) := [(5054162944,108395346583243,108395731807569)]
theorem point_links_checked38530 : (cuts38530.take 1).map (fun c => (5054136321-1+2*2^10*c.k,108395278527816+c.lower,108395663752101+c.upper)) = pointBounds38530 := by
 decide +kernel
def cuts38531 : List PrefixCut := [⟨27,141954422,141954504⟩,
⟨64,334584463,334584659⟩]
theorem checked38531 : checkPrefixCuts (2^48) 5054267393 10 Manual.Count131072.C038531.packed 64 cuts38531 = true := by
 decide +kernel
def pointBounds38531 : List (Nat × Nat × Nat) := [(5054322688,108395747779811,108396133004374)]
theorem point_links_checked38531 : (cuts38531.take 1).map (fun c => (5054267393-1+2*2^10*c.k,108395605825389+c.lower,108395991049870+c.upper)) = pointBounds38531 := by
 decide +kernel
def cuts38532 : List PrefixCut := [⟨41,211059928,211060055⟩,
⟨64,327503351,327503549⟩]
theorem checked38532 : checkPrefixCuts (2^48) 5054398465 10 Manual.Count131072.C038532.packed 64 cuts38532 = true := by
 decide +kernel
def pointBounds38532 : List (Nat × Nat × Nat) := [(5054482432,108396151469780,108396536694584)]
theorem point_links_checked38532 : (cuts38532.take 1).map (fun c => (5054398465-1+2*2^10*c.k,108395940409852+c.lower,108396325634529+c.upper)) = pointBounds38532 := by
 decide +kernel
def cuts38533 : List PrefixCut := [⟨55,282890140,282890312⟩,
⟨64,329109778,329109978⟩]
theorem checked38533 : checkPrefixCuts (2^48) 5054529537 10 Manual.Count131072.C038533.packed 64 cuts38533 = true := by
 decide +kernel
def pointBounds38533 : List (Nat × Nat × Nat) := [(5054642176,108396550803343,108396936028390)]
theorem point_links_checked38533 : (cuts38533.take 1).map (fun c => (5054529537-1+2*2^10*c.k,108396267913203+c.lower,108396653138078+c.upper)) = pointBounds38533 := by
 decide +kernel
def cuts38534 : List PrefixCut := [⟨64,325927130,325927325⟩]
theorem checked38534 : checkPrefixCuts (2^48) 5054660609 10 Manual.Count131072.C038534.packed 64 cuts38534 = true := by
 decide +kernel
def cuts38535 : List PrefixCut := [⟨5,26505922,26505937⟩,
⟨64,321519655,321519848⟩]
theorem checked38535 : checkPrefixCuts (2^48) 5054791681 10 Manual.Count131072.C038535.packed 64 cuts38535 = true := by
 decide +kernel
def pointBounds38535 : List (Nat × Nat × Nat) := [(5054801920,108396949456033,108397334681318)]
theorem point_links_checked38535 : (cuts38535.take 1).map (fun c => (5054791681-1+2*2^10*c.k,108396922950111+c.lower,108397308175381+c.upper)) = pointBounds38535 := by
 decide +kernel
def cuts38536 : List PrefixCut := [⟨19,99672763,99672821⟩,
⟨64,331255822,331256018⟩]
theorem checked38536 : checkPrefixCuts (2^48) 5054922753 10 Manual.Count131072.C038536.packed 64 cuts38536 = true := by
 decide +kernel
def pointBounds38536 : List (Nat × Nat × Nat) := [(5054961664,108397344142529,108397729368050)]
theorem point_links_checked38536 : (cuts38536.take 1).map (fun c => (5054922753-1+2*2^10*c.k,108397244469766+c.lower,108397629695229+c.upper)) = pointBounds38536 := by
 decide +kernel
def cuts38537 : List PrefixCut := [⟨33,170329724,170329826⟩,
⟨64,331692638,331692836⟩]
theorem checked38537 : checkPrefixCuts (2^48) 5055053825 10 Manual.Count131072.C038537.packed 64 cuts38537 = true := by
 decide +kernel
def pointBounds38537 : List (Nat × Nat × Nat) := [(5055121408,108397746055312,108398131281073)]
theorem point_links_checked38537 : (cuts38537.take 1).map (fun c => (5055053825-1+2*2^10*c.k,108397575725588+c.lower,108397960951247+c.upper)) = pointBounds38537 := by
 decide +kernel
def cuts38538 : List PrefixCut := [⟨47,235804400,235804538⟩,
⟨64,321940097,321940286⟩]
theorem checked38538 : checkPrefixCuts (2^48) 5055184897 10 Manual.Count131072.C038538.packed 64 cuts38538 = true := by
 decide +kernel
def pointBounds38538 : List (Nat × Nat × Nat) := [(5055281152,108398143222626,108398528448621)]
theorem point_links_checked38538 : (cuts38538.take 1).map (fun c => (5055184897-1+2*2^10*c.k,108397907418226+c.lower,108398292644083+c.upper)) = pointBounds38538 := by
 decide +kernel
def cuts38539 : List PrefixCut := [⟨61,312522313,312522500⟩,
⟨64,328279068,328279264⟩]
theorem checked38539 : checkPrefixCuts (2^48) 5055315969 10 Manual.Count131072.C038539.packed 64 cuts38539 = true := by
 decide +kernel
def pointBounds38539 : List (Nat × Nat × Nat) := [(5055440896,108398541880636,108398927106869)]
theorem point_links_checked38539 : (cuts38539.take 1).map (fun c => (5055315969-1+2*2^10*c.k,108398229358323+c.lower,108398614584369+c.upper)) = pointBounds38539 := by
 decide +kernel
def cuts38540 : List PrefixCut := [⟨64,323315337,323315534⟩]
theorem checked38540 : checkPrefixCuts (2^48) 5055447041 10 Manual.Count131072.C038540.packed 64 cuts38540 = true := by
 decide +kernel
def cuts38541 : List PrefixCut := [⟨11,57234907,57234942⟩,
⟨64,328039365,328039564⟩]
theorem checked38541 : checkPrefixCuts (2^48) 5055578113 10 Manual.Count131072.C038541.packed 64 cuts38541 = true := by
 decide +kernel
def pointBounds38541 : List (Nat × Nat × Nat) := [(5055600640,108398938187635,108399323414109)]
theorem point_links_checked38541 : (cuts38541.take 1).map (fun c => (5055578113-1+2*2^10*c.k,108398880952728+c.lower,108399266179167+c.upper)) = pointBounds38541 := by
 decide +kernel
def cuts38542 : List PrefixCut := [⟨25,126937589,126937666⟩,
⟨64,328921611,328921809⟩]
theorem checked38542 : checkPrefixCuts (2^48) 5055709185 10 Manual.Count131072.C038542.packed 64 cuts38542 = true := by
 decide +kernel
def pointBounds38542 : List (Nat × Nat × Nat) := [(5055760384,108399335929682,108399721156397)]
theorem point_links_checked38542 : (cuts38542.take 1).map (fun c => (5055709185-1+2*2^10*c.k,108399208992093+c.lower,108399594218731+c.upper)) = pointBounds38542 := by
 decide +kernel
def cuts38543 : List PrefixCut := [⟨39,199586909,199587035⟩,
⟨64,326964560,326964763⟩]
theorem checked38543 : checkPrefixCuts (2^48) 5055840257 10 Manual.Count131072.C038543.packed 64 cuts38543 = true := by
 decide +kernel
def pointBounds38543 : List (Nat × Nat × Nat) := [(5055920128,108399737500613,108400122727575)]
theorem point_links_checked38543 : (cuts38543.take 1).map (fun c => (5055840257-1+2*2^10*c.k,108399537913704+c.lower,108399923140540+c.upper)) = pointBounds38543 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000266
