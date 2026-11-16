import PlattAssemblyKernel
import PlattCertificates.Count131072.C044512
import PlattCertificates.Count131072.C044513
import PlattCertificates.Count131072.C044514
import PlattCertificates.Count131072.C044515
import PlattCertificates.Count131072.C044516
import PlattCertificates.Count131072.C044517
import PlattCertificates.Count131072.C044518
import PlattCertificates.Count131072.C044519
import PlattCertificates.Count131072.C044520
import PlattCertificates.Count131072.C044521
import PlattCertificates.Count131072.C044522
import PlattCertificates.Count131072.C044523
import PlattCertificates.Count131072.C044524
import PlattCertificates.Count131072.C044525
import PlattCertificates.Count131072.C044526
import PlattCertificates.Count131072.C044527
import PlattCertificates.Count131072.C044528
import PlattCertificates.Count131072.C044529
import PlattCertificates.Count131072.C044530
import PlattCertificates.Count131072.C044531
import PlattCertificates.Count131072.C044532
import PlattCertificates.Count131072.C044533
import PlattCertificates.Count131072.C044534
import PlattCertificates.Count131072.C044535
import PlattCertificates.Count131072.C044536
import PlattCertificates.Count131072.C044537
import PlattCertificates.Count131072.C044538
import PlattCertificates.Count131072.C044539
import PlattCertificates.Count131072.C044540
import PlattCertificates.Count131072.C044541
import PlattCertificates.Count131072.C044542
import PlattCertificates.Count131072.C044543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000141
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts44512 : List PrefixCut := [⟨64,280304578,280304741⟩]
theorem checked44512 : checkPrefixCuts (2^48) 5838209025 10 Manual.Count131072.C044512.packed 64 cuts44512 = true := by
 decide +kernel
def cuts44513 : List PrefixCut := [⟨1,4435453,4435456⟩,
⟨64,278321629,278321787⟩]
theorem checked44513 : checkPrefixCuts (2^48) 5838340097 10 Manual.Count131072.C044513.packed 64 cuts44513 = true := by
 decide +kernel
def pointBounds44513 : List (Nat × Nat × Nat) := [(5838342144,110206563982017,110206950272769)]
theorem point_links_checked44513 : (cuts44513.take 1).map (fun c => (5838340097-1+2*2^10*c.k,110206559546564+c.lower,110206945837313+c.upper)) = pointBounds44513 := by
 decide +kernel
def cuts44514 : List PrefixCut := [⟨27,119995068,119995136⟩,
⟨64,282943529,282943696⟩]
theorem checked44514 : checkPrefixCuts (2^48) 5838471169 10 Manual.Count131072.C044514.packed 64 cuts44514 = true := by
 decide +kernel
def pointBounds44514 : List (Nat × Nat × Nat) := [(5838526464,110206957863261,110207344154236)]
theorem point_links_checked44514 : (cuts44514.take 1).map (fun c => (5838471169-1+2*2^10*c.k,110206837868193+c.lower,110207224159100+c.upper)) = pointBounds44514 := by
 decide +kernel
def cuts44515 : List PrefixCut := [⟨53,233716515,233716644⟩,
⟨64,282744361,282744519⟩]
theorem checked44515 : checkPrefixCuts (2^48) 5838602241 10 Manual.Count131072.C044515.packed 64 cuts44515 = true := by
 decide +kernel
def pointBounds44515 : List (Nat × Nat × Nat) := [(5838710784,110207354528237,110207740819440)]
theorem point_links_checked44515 : (cuts44515.take 1).map (fun c => (5838602241-1+2*2^10*c.k,110207120811722+c.lower,110207507102796+c.upper)) = pointBounds44515 := by
 decide +kernel
def cuts44516 : List PrefixCut := [⟨64,282255906,282256069⟩]
theorem checked44516 : checkPrefixCuts (2^48) 5838733313 10 Manual.Count131072.C044516.packed 64 cuts44516 = true := by
 decide +kernel
def cuts44517 : List PrefixCut := [⟨15,66959528,66959566⟩,
⟨64,284177845,284178008⟩]
theorem checked44517 : checkPrefixCuts (2^48) 5838864385 10 Manual.Count131072.C044517.packed 64 cuts44517 = true := by
 decide +kernel
def pointBounds44517 : List (Nat × Nat × Nat) := [(5838895104,110207752771517,110208139062950)]
theorem point_links_checked44517 : (cuts44517.take 1).map (fun c => (5838864385-1+2*2^10*c.k,110207685811989+c.lower,110208072103384+c.upper)) = pointBounds44517 := by
 decide +kernel
def cuts44518 : List PrefixCut := [⟨41,182796018,182796124⟩,
⟨64,284219676,284219836⟩]
theorem checked44518 : checkPrefixCuts (2^48) 5838995457 10 Manual.Count131072.C044518.packed 64 cuts44518 = true := by
 decide +kernel
def pointBounds44518 : List (Nat × Nat × Nat) := [(5839079424,110208152785852,110208539077516)]
theorem point_links_checked44518 : (cuts44518.take 1).map (fun c => (5838995457-1+2*2^10*c.k,110207969989834+c.lower,110208356281392+c.upper)) = pointBounds44518 := by
 decide +kernel
def cuts44519 : List PrefixCut := [⟨64,276548805,276548967⟩]
theorem checked44519 : checkPrefixCuts (2^48) 5839126529 10 Manual.Count131072.C044519.packed 64 cuts44519 = true := by
 decide +kernel
def cuts44520 : List PrefixCut := [⟨3,13352469,13352476⟩,
⟨64,281748565,281748723⟩]
theorem checked44520 : checkPrefixCuts (2^48) 5839257601 10 Manual.Count131072.C044520.packed 64 cuts44520 = true := by
 decide +kernel
def pointBounds44520 : List (Nat × Nat × Nat) := [(5839263744,110208544110784,110208930402671)]
theorem point_links_checked44520 : (cuts44520.take 1).map (fun c => (5839257601-1+2*2^10*c.k,110208530758315+c.lower,110208917050195+c.upper)) = pointBounds44520 := by
 decide +kernel
def cuts44521 : List PrefixCut := [⟨29,126676321,126676395⟩,
⟨64,280344357,280344516⟩]
theorem checked44521 : checkPrefixCuts (2^48) 5839388673 10 Manual.Count131072.C044521.packed 64 cuts44521 = true := by
 decide +kernel
def pointBounds44521 : List (Nat × Nat × Nat) := [(5839448064,110208939183201,110209325475313)]
theorem point_links_checked44521 : (cuts44521.take 1).map (fun c => (5839388673-1+2*2^10*c.k,110208812506880+c.lower,110209198798918+c.upper)) = pointBounds44521 := by
 decide +kernel
def cuts44522 : List PrefixCut := [⟨55,240042260,240042404⟩,
⟨64,280145255,280145422⟩]
theorem checked44522 : checkPrefixCuts (2^48) 5839519745 10 Manual.Count131072.C044522.packed 64 cuts44522 = true := by
 decide +kernel
def pointBounds44522 : List (Nat × Nat × Nat) := [(5839632384,110209332893497,110209719185838)]
theorem point_links_checked44522 : (cuts44522.take 1).map (fun c => (5839519745-1+2*2^10*c.k,110209092851237+c.lower,110209479143434+c.upper)) = pointBounds44522 := by
 decide +kernel
def cuts44523 : List PrefixCut := [⟨64,277680754,277680906⟩]
theorem checked44523 : checkPrefixCuts (2^48) 5839650817 10 Manual.Count131072.C044523.packed 64 cuts44523 = true := by
 decide +kernel
def cuts44524 : List PrefixCut := [⟨17,74612690,74612735⟩,
⟨64,278301125,278301289⟩]
theorem checked44524 : checkPrefixCuts (2^48) 5839781889 10 Manual.Count131072.C044524.packed 64 cuts44524 = true := by
 decide +kernel
def pointBounds44524 : List (Nat × Nat × Nat) := [(5839816704,110209725289936,110210111582497)]
theorem point_links_checked44524 : (cuts44524.take 1).map (fun c => (5839781889-1+2*2^10*c.k,110209650677246+c.lower,110210036969762+c.upper)) = pointBounds44524 := by
 decide +kernel
def cuts44525 : List PrefixCut := [⟨43,187683445,187683552⟩,
⟨64,280367371,280367527⟩]
theorem checked44525 : checkPrefixCuts (2^48) 5839912961 10 Manual.Count131072.C044525.packed 64 cuts44525 = true := by
 decide +kernel
def pointBounds44525 : List (Nat × Nat × Nat) := [(5840001024,110210116661816,110210502954603)]
theorem point_links_checked44525 : (cuts44525.take 1).map (fun c => (5839912961-1+2*2^10*c.k,110209928978371+c.lower,110210315271051+c.upper)) = pointBounds44525 := by
 decide +kernel
def cuts44526 : List PrefixCut := [⟨64,282674502,282674667⟩]
theorem checked44526 : checkPrefixCuts (2^48) 5840044033 10 Manual.Count131072.C044526.packed 64 cuts44526 = true := by
 decide +kernel
def cuts44527 : List PrefixCut := [⟨5,22266675,22266689⟩,
⟨64,282475407,282475570⟩]
theorem checked44527 : checkPrefixCuts (2^48) 5840175105 10 Manual.Count131072.C044527.packed 64 cuts44527 = true := by
 decide +kernel
def pointBounds44527 : List (Nat × Nat × Nat) := [(5840185344,110210514286919,110210900579934)]
theorem point_links_checked44527 : (cuts44527.take 1).map (fun c => (5840175105-1+2*2^10*c.k,110210492020244+c.lower,110210878313245+c.upper)) = pointBounds44527 := by
 decide +kernel
def cuts44528 : List PrefixCut := [⟨31,135235079,135235158⟩,
⟨64,283529338,283529496⟩]
theorem checked44528 : checkPrefixCuts (2^48) 5840306177 10 Manual.Count131072.C044528.packed 64 cuts44528 = true := by
 decide +kernel
def pointBounds44528 : List (Nat × Nat × Nat) := [(5840369664,110210909730730,110211296023973)]
theorem point_links_checked44528 : (cuts44528.take 1).map (fun c => (5840306177-1+2*2^10*c.k,110210774495651+c.lower,110211160788815+c.upper)) = pointBounds44528 := by
 decide +kernel
def cuts44529 : List PrefixCut := [⟨57,249113068,249113211⟩,
⟨64,279715703,279715864⟩]
theorem checked44529 : checkPrefixCuts (2^48) 5840437249 10 Manual.Count131072.C044529.packed 64 cuts44529 = true := by
 decide +kernel
def pointBounds44529 : List (Nat × Nat × Nat) := [(5840553984,110211307138057,110211693431522)]
theorem point_links_checked44529 : (cuts44529.take 1).map (fun c => (5840437249-1+2*2^10*c.k,110211058024989+c.lower,110211444318311+c.upper)) = pointBounds44529 := by
 decide +kernel
def cuts44530 : List PrefixCut := [⟨64,278408208,278408368⟩]
theorem checked44530 : checkPrefixCuts (2^48) 5840568321 10 Manual.Count131072.C044530.packed 64 cuts44530 = true := by
 decide +kernel
def cuts44531 : List PrefixCut := [⟨19,85733249,85733299⟩,
⟨64,282064548,282064714⟩]
theorem checked44531 : checkPrefixCuts (2^48) 5840699393 10 Manual.Count131072.C044531.packed 64 cuts44531 = true := by
 decide +kernel
def pointBounds44531 : List (Nat × Nat × Nat) := [(5840738304,110211701882149,110212088175842)]
theorem point_links_checked44531 : (cuts44531.take 1).map (fun c => (5840699393-1+2*2^10*c.k,110211616148900+c.lower,110212002442543+c.upper)) = pointBounds44531 := by
 decide +kernel
def cuts44532 : List PrefixCut := [⟨45,198448569,198448683⟩,
⟨64,281865423,281865587⟩]
theorem checked44532 : checkPrefixCuts (2^48) 5840830465 10 Manual.Count131072.C044532.packed 64 cuts44532 = true := by
 decide +kernel
def pointBounds44532 : List (Nat × Nat × Nat) := [(5840922624,110212096662017,110212482955940)]
theorem point_links_checked44532 : (cuts44532.take 1).map (fun c => (5840830465-1+2*2^10*c.k,110211898213448+c.lower,110212284507257+c.upper)) = pointBounds44532 := by
 decide +kernel
def cuts44533 : List PrefixCut := [⟨64,279449625,279449788⟩]
theorem checked44533 : checkPrefixCuts (2^48) 5840961537 10 Manual.Count131072.C044533.packed 64 cuts44533 = true := by
 decide +kernel
def cuts44534 : List PrefixCut := [⟨7,31419019,31419037⟩,
⟨64,278527806,278527967⟩]
theorem checked44534 : checkPrefixCuts (2^48) 5841092609 10 Manual.Count131072.C044534.packed 64 cuts44534 = true := by
 decide +kernel
def pointBounds44534 : List (Nat × Nat × Nat) := [(5841106944,110212490947515,110212877241669)]
theorem point_links_checked44534 : (cuts44534.take 1).map (fun c => (5841092609-1+2*2^10*c.k,110212459528496+c.lower,110212845822632+c.upper)) = pointBounds44534 := by
 decide +kernel
def cuts44535 : List PrefixCut := [⟨33,144321210,144321294⟩,
⟨64,278280624,278280784⟩]
theorem checked44535 : checkPrefixCuts (2^48) 5841223681 10 Manual.Count131072.C044535.packed 64 cuts44535 = true := by
 decide +kernel
def pointBounds44535 : List (Nat × Nat × Nat) := [(5841291264,110212882377512,110213268671893)]
theorem point_links_checked44535 : (cuts44535.take 1).map (fun c => (5841223681-1+2*2^10*c.k,110212738056302+c.lower,110213124350599+c.upper)) = pointBounds44535 := by
 decide +kernel
def cuts44536 : List PrefixCut := [⟨59,257795537,257795682⟩,
⟨64,279141730,279141888⟩]
theorem checked44536 : checkPrefixCuts (2^48) 5841354753 10 Manual.Count131072.C044536.packed 64 cuts44536 = true := by
 decide +kernel
def pointBounds44536 : List (Nat × Nat × Nat) := [(5841475584,110213274132463,110213660427065)]
theorem point_links_checked44536 : (cuts44536.take 1).map (fun c => (5841354753-1+2*2^10*c.k,110213016336926+c.lower,110213402631383+c.upper)) = pointBounds44536 := by
 decide +kernel
def cuts44537 : List PrefixCut := [⟨64,281978371,281978532⟩]
theorem checked44537 : checkPrefixCuts (2^48) 5841485825 10 Manual.Count131072.C044537.packed 64 cuts44537 = true := by
 decide +kernel
def cuts44538 : List PrefixCut := [⟨21,94055633,94055685⟩,
⟨64,285296731,285296892⟩]
theorem checked44538 : checkPrefixCuts (2^48) 5841616897 10 Manual.Count131072.C044538.packed 64 cuts44538 = true := by
 decide +kernel
def pointBounds44538 : List (Nat × Nat × Nat) := [(5841659904,110213671512660,110214057807488)]
theorem point_links_checked44538 : (cuts44538.take 1).map (fun c => (5841616897-1+2*2^10*c.k,110213577457027+c.lower,110213963751803+c.upper)) = pointBounds44538 := by
 decide +kernel
def cuts44539 : List PrefixCut := [⟨47,205500228,205500342⟩,
⟨64,276954719,276954877⟩]
theorem checked44539 : checkPrefixCuts (2^48) 5841747969 10 Manual.Count131072.C044539.packed 64 cuts44539 = true := by
 decide +kernel
def pointBounds44539 : List (Nat × Nat × Nat) := [(5841844224,110214068253986,110214454549037)]
theorem point_links_checked44539 : (cuts44539.take 1).map (fun c => (5841747969-1+2*2^10*c.k,110213862753758+c.lower,110214249048695+c.upper)) = pointBounds44539 := by
 decide +kernel
def cuts44540 : List PrefixCut := [⟨64,280176641,280176804⟩]
theorem checked44540 : checkPrefixCuts (2^48) 5841879041 10 Manual.Count131072.C044540.packed 64 cuts44540 = true := by
 decide +kernel
def cuts44541 : List PrefixCut := [⟨9,38400335,38400355⟩,
⟨64,279303136,279303298⟩]
theorem checked44541 : checkPrefixCuts (2^48) 5842010113 10 Manual.Count131072.C044541.packed 64 cuts44541 = true := by
 decide +kernel
def pointBounds44541 : List (Nat × Nat × Nat) := [(5842028544,110214458285453,110214844580731)]
theorem point_links_checked44541 : (cuts44541.take 1).map (fun c => (5842010113-1+2*2^10*c.k,110214419885118+c.lower,110214806180376+c.upper)) = pointBounds44541 := by
 decide +kernel
def cuts44542 : List PrefixCut := [⟨35,154657127,154657219⟩,
⟨64,280260457,280260620⟩]
theorem checked44542 : checkPrefixCuts (2^48) 5842141185 10 Manual.Count131072.C044542.packed 64 cuts44542 = true := by
 decide +kernel
def pointBounds44542 : List (Nat × Nat × Nat) := [(5842212864,110214853845381,110215240140893)]
theorem point_links_checked44542 : (cuts44542.take 1).map (fun c => (5842141185-1+2*2^10*c.k,110214699188254+c.lower,110215085483674+c.upper)) = pointBounds44542 := by
 decide +kernel
def cuts44543 : List PrefixCut := [⟨61,270233153,270233311⟩,
⟨64,282470354,282470519⟩]
theorem checked44543 : checkPrefixCuts (2^48) 5842272257 10 Manual.Count131072.C044543.packed 64 cuts44543 = true := by
 decide +kernel
def pointBounds44543 : List (Nat × Nat × Nat) := [(5842397184,110215249681864,110215635977605)]
theorem point_links_checked44543 : (cuts44543.take 1).map (fun c => (5842272257-1+2*2^10*c.k,110214979448711+c.lower,110215365744294+c.upper)) = pointBounds44543 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000141
