import PlattAssemblyKernel
import PlattCertificates.Count131072.C061536
import PlattCertificates.Count131072.C061537
import PlattCertificates.Count131072.C061538
import PlattCertificates.Count131072.C061539
import PlattCertificates.Count131072.C061540
import PlattCertificates.Count131072.C061541
import PlattCertificates.Count131072.C061542
import PlattCertificates.Count131072.C061543
import PlattCertificates.Count131072.C061544
import PlattCertificates.Count131072.C061545
import PlattCertificates.Count131072.C061546
import PlattCertificates.Count131072.C061547
import PlattCertificates.Count131072.C061548
import PlattCertificates.Count131072.C061549
import PlattCertificates.Count131072.C061550
import PlattCertificates.Count131072.C061551
import PlattCertificates.Count131072.C061552
import PlattCertificates.Count131072.C061553
import PlattCertificates.Count131072.C061554
import PlattCertificates.Count131072.C061555
import PlattCertificates.Count131072.C061556
import PlattCertificates.Count131072.C061557
import PlattCertificates.Count131072.C061558
import PlattCertificates.Count131072.C061559
import PlattCertificates.Count131072.C061560
import PlattCertificates.Count131072.C061561
import PlattCertificates.Count131072.C061562
import PlattCertificates.Count131072.C061563
import PlattCertificates.Count131072.C061564
import PlattCertificates.Count131072.C061565
import PlattCertificates.Count131072.C061566
import PlattCertificates.Count131072.C061567
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000048
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61536 : List PrefixCut := [⟨40,123478087,123478160⟩,
⟨64,197948011,197948129⟩]
theorem checked61536 : checkPrefixCuts (2^48) 8069578753 10 Manual.Count131072.C061536.packed 64 cuts61536 = true := by
 decide +kernel
def pointBounds61536 : List (Nat × Nat × Nat) := [(8069660672,114228877732238,114229266317991)]
theorem point_links_checked61536 : (cuts61536.take 1).map (fun c => (8069578753-1+2*2^10*c.k,114228754254151+c.lower,114229142839831+c.upper)) = pointBounds61536 := by
 decide +kernel
def cuts61537 : List PrefixCut := [⟨64,201816483,201816598⟩]
theorem checked61537 : checkPrefixCuts (2^48) 8069709825 10 Manual.Count131072.C061537.packed 64 cuts61537 = true := by
 decide +kernel
def cuts61538 : List PrefixCut := [⟨36,111510394,111510460⟩,
⟨64,198360136,198360250⟩]
theorem checked61538 : checkPrefixCuts (2^48) 8069840897 10 Manual.Count131072.C061538.packed 64 cuts61538 = true := by
 decide +kernel
def pointBounds61538 : List (Nat × Nat × Nat) := [(8069914624,114229265529039,114229654115018)]
theorem point_links_checked61538 : (cuts61538.take 1).map (fun c => (8069840897-1+2*2^10*c.k,114229154018645+c.lower,114229542604558+c.upper)) = pointBounds61538 := by
 decide +kernel
def cuts61539 : List PrefixCut := [⟨64,198531302,198531414⟩]
theorem checked61539 : checkPrefixCuts (2^48) 8069971969 10 Manual.Count131072.C061539.packed 64 cuts61539 = true := by
 decide +kernel
def cuts61540 : List PrefixCut := [⟨32,100554950,100555003⟩,
⟨64,200062738,200062847⟩]
theorem checked61540 : checkPrefixCuts (2^48) 8070103041 10 Manual.Count131072.C061540.packed 64 cuts61540 = true := by
 decide +kernel
def pointBounds61540 : List (Nat × Nat × Nat) := [(8070168576,114229651465033,114230040051225)]
theorem point_links_checked61540 : (cuts61540.take 1).map (fun c => (8070103041-1+2*2^10*c.k,114229550910083+c.lower,114229939496222+c.upper)) = pointBounds61540 := by
 decide +kernel
def cuts61541 : List PrefixCut := [⟨64,201210466,201210583⟩]
theorem checked61541 : checkPrefixCuts (2^48) 8070234113 10 Manual.Count131072.C061541.packed 64 cuts61541 = true := by
 decide +kernel
def cuts61542 : List PrefixCut := [⟨28,89390952,89391004⟩,
⟨64,203822991,203823108⟩]
theorem checked61542 : checkPrefixCuts (2^48) 8070365185 10 Manual.Count131072.C061542.packed 64 cuts61542 = true := by
 decide +kernel
def pointBounds61542 : List (Nat × Nat × Nat) := [(8070422528,114230041574239,114230430160656)]
theorem point_links_checked61542 : (cuts61542.take 1).map (fun c => (8070365185-1+2*2^10*c.k,114229952183287+c.lower,114230340769652+c.upper)) = pointBounds61542 := by
 decide +kernel
def cuts61543 : List PrefixCut := [⟨64,197855746,197855861⟩]
theorem checked61543 : checkPrefixCuts (2^48) 8070496257 10 Manual.Count131072.C061543.packed 64 cuts61543 = true := by
 decide +kernel
def cuts61544 : List PrefixCut := [⟨24,74635394,74635438⟩,
⟨64,197573532,197573646⟩]
theorem checked61544 : checkPrefixCuts (2^48) 8070627329 10 Manual.Count131072.C061544.packed 64 cuts61544 = true := by
 decide +kernel
def pointBounds61544 : List (Nat × Nat × Nat) := [(8070676480,114230428497418,114230817084059)]
theorem point_links_checked61544 : (cuts61544.take 1).map (fun c => (8070627329-1+2*2^10*c.k,114230353862024+c.lower,114230742448621+c.upper)) = pointBounds61544 := by
 decide +kernel
def cuts61545 : List PrefixCut := [⟨64,201650756,201650876⟩]
theorem checked61545 : checkPrefixCuts (2^48) 8070758401 10 Manual.Count131072.C061545.packed 64 cuts61545 = true := by
 decide +kernel
def cuts61546 : List PrefixCut := [⟨20,63124178,63124214⟩,
⟨64,203844613,203844725⟩]
theorem checked61546 : checkPrefixCuts (2^48) 8070889473 10 Manual.Count131072.C061546.packed 64 cuts61546 = true := by
 decide +kernel
def pointBounds61546 : List (Nat × Nat × Nat) := [(8070930432,114230816210490,114231204797357)]
theorem point_links_checked61546 : (cuts61546.take 1).map (fun c => (8070889473-1+2*2^10*c.k,114230753086312+c.lower,114231141673143+c.upper)) = pointBounds61546 := by
 decide +kernel
def cuts61547 : List PrefixCut := [⟨64,198296260,198296375⟩]
theorem checked61547 : checkPrefixCuts (2^48) 8071020545 10 Manual.Count131072.C061547.packed 64 cuts61547 = true := by
 decide +kernel
def cuts61548 : List PrefixCut := [⟨16,49172509,49172541⟩,
⟨64,202373286,202373404⟩]
theorem checked61548 : checkPrefixCuts (2^48) 8071151617 10 Manual.Count131072.C061548.packed 64 cuts61548 = true := by
 decide +kernel
def pointBounds61548 : List (Nat × Nat × Nat) := [(8071184384,114231204399694,114231592986784)]
theorem point_links_checked61548 : (cuts61548.take 1).map (fun c => (8071151617-1+2*2^10*c.k,114231155227185+c.lower,114231543814243+c.upper)) = pointBounds61548 := by
 decide +kernel
def cuts61549 : List PrefixCut := [⟨64,198429304,198429420⟩]
theorem checked61549 : checkPrefixCuts (2^48) 8071282689 10 Manual.Count131072.C061549.packed 64 cuts61549 = true := by
 decide +kernel
def cuts61550 : List PrefixCut := [⟨12,37662847,37662868⟩,
⟨64,199855865,199855981⟩]
theorem checked61550 : checkPrefixCuts (2^48) 8071413761 10 Manual.Count131072.C061550.packed 64 cuts61550 = true := by
 decide +kernel
def pointBounds61550 : List (Nat × Nat × Nat) := [(8071438336,114231593692622,114231982279935)]
theorem point_links_checked61550 : (cuts61550.take 1).map (fun c => (8071413761-1+2*2^10*c.k,114231556029775+c.lower,114231944617067+c.upper)) = pointBounds61550 := by
 decide +kernel
def cuts61551 : List PrefixCut := [⟨64,200096747,200096863⟩]
theorem checked61551 : checkPrefixCuts (2^48) 8071544833 10 Manual.Count131072.C061551.packed 64 cuts61551 = true := by
 decide +kernel
def cuts61552 : List PrefixCut := [⟨8,24898532,24898545⟩,
⟨64,196989932,196990044⟩]
theorem checked61552 : checkPrefixCuts (2^48) 8071675905 10 Manual.Count131072.C061552.packed 64 cuts61552 = true := by
 decide +kernel
def pointBounds61552 : List (Nat × Nat × Nat) := [(8071692288,114231980880919,114232369468456)]
theorem point_links_checked61552 : (cuts61552.take 1).map (fun c => (8071675905-1+2*2^10*c.k,114231955982387+c.lower,114232344569911+c.upper)) = pointBounds61552 := by
 decide +kernel
def cuts61553 : List PrefixCut := [⟨64,200090243,200090360⟩]
theorem checked61553 : checkPrefixCuts (2^48) 8071806977 10 Manual.Count131072.C061553.packed 64 cuts61553 = true := by
 decide +kernel
def cuts61554 : List PrefixCut := [⟨4,12902187,12902195⟩,
⟨64,202772037,202772154⟩]
theorem checked61554 : checkPrefixCuts (2^48) 8071938049 10 Manual.Count131072.C061554.packed 64 cuts61554 = true := by
 decide +kernel
def pointBounds61554 : List (Nat × Nat × Nat) := [(8071946240,114232365964749,114232754552510)]
theorem point_links_checked61554 : (cuts61554.take 1).map (fun c => (8071938049-1+2*2^10*c.k,114232353062562+c.lower,114232741650315+c.upper)) = pointBounds61554 := by
 decide +kernel
def cuts61555 : List PrefixCut := [⟨64,201164723,201164837⟩]
theorem checked61555 : checkPrefixCuts (2^48) 8072069121 10 Manual.Count131072.C061555.packed 64 cuts61555 = true := by
 decide +kernel
def pointBounds61555 : List (Nat × Nat × Nat) := [(8072200192,114232756999322,114233145587306)]
theorem point_links_checked61555 : (cuts61555.take 1).map (fun c => (8072069121-1+2*2^10*c.k,114232555834599+c.lower,114232944422469+c.upper)) = pointBounds61555 := by
 decide +kernel
def cuts61556 : List PrefixCut := [⟨64,203427966,203428083⟩]
theorem checked61556 : checkPrefixCuts (2^48) 8072200193 10 Manual.Count131072.C061556.packed 64 cuts61556 = true := by
 decide +kernel
def cuts61557 : List PrefixCut := [⟨60,188640375,188640484⟩,
⟨64,201227920,201228037⟩]
theorem checked61557 : checkPrefixCuts (2^48) 8072331265 10 Manual.Count131072.C061557.packed 64 cuts61557 = true := by
 decide +kernel
def pointBounds61557 : List (Nat × Nat × Nat) := [(8072454144,114233149067663,114233537655873)]
theorem point_links_checked61557 : (cuts61557.take 1).map (fun c => (8072331265-1+2*2^10*c.k,114232960427288+c.lower,114233349015389+c.upper)) = pointBounds61557 := by
 decide +kernel
def cuts61558 : List PrefixCut := [⟨64,199306913,199307025⟩]
theorem checked61558 : checkPrefixCuts (2^48) 8072462337 10 Manual.Count131072.C061558.packed 64 cuts61558 = true := by
 decide +kernel
def cuts61559 : List PrefixCut := [⟨56,177825346,177825447⟩,
⟨64,203243706,203243822⟩]
theorem checked61559 : checkPrefixCuts (2^48) 8072593409 10 Manual.Count131072.C061559.packed 64 cuts61559 = true := by
 decide +kernel
def pointBounds61559 : List (Nat × Nat × Nat) := [(8072708096,114233538787467,114233927375898)]
theorem point_links_checked61559 : (cuts61559.take 1).map (fun c => (8072593409-1+2*2^10*c.k,114233360962121+c.lower,114233749550451+c.upper)) = pointBounds61559 := by
 decide +kernel
def cuts61560 : List PrefixCut := [⟨64,198010356,198010473⟩]
theorem checked61560 : checkPrefixCuts (2^48) 8072724481 10 Manual.Count131072.C061560.packed 64 cuts61560 = true := by
 decide +kernel
def cuts61561 : List PrefixCut := [⟨52,164640096,164640195⟩,
⟨64,201842457,201842579⟩]
theorem checked61561 : checkPrefixCuts (2^48) 8072855553 10 Manual.Count131072.C061561.packed 64 cuts61561 = true := by
 decide +kernel
def pointBounds61561 : List (Nat × Nat × Nat) := [(8072962048,114233926856279,114234315444941)]
theorem point_links_checked61561 : (cuts61561.take 1).map (fun c => (8072855553-1+2*2^10*c.k,114233762216183+c.lower,114234150804746+c.upper)) = pointBounds61561 := by
 decide +kernel
def cuts61562 : List PrefixCut := [⟨64,202745695,202745813⟩]
theorem checked61562 : checkPrefixCuts (2^48) 8072986625 10 Manual.Count131072.C061562.packed 64 cuts61562 = true := by
 decide +kernel
def cuts61563 : List PrefixCut := [⟨48,152710847,152710933⟩,
⟨64,203021335,203021451⟩]
theorem checked61563 : checkPrefixCuts (2^48) 8073117697 10 Manual.Count131072.C061563.packed 64 cuts61563 = true := by
 decide +kernel
def pointBounds61563 : List (Nat × Nat × Nat) := [(8073216000,114234319515182,114234708104071)]
theorem point_links_checked61563 : (cuts61563.take 1).map (fun c => (8073117697-1+2*2^10*c.k,114234166804335+c.lower,114234555393138+c.upper)) = pointBounds61563 := by
 decide +kernel
def cuts61564 : List PrefixCut := [⟨64,202808838,202808956⟩]
theorem checked61564 : checkPrefixCuts (2^48) 8073248769 10 Manual.Count131072.C061564.packed 64 cuts61564 = true := by
 decide +kernel
def cuts61565 : List PrefixCut := [⟨44,137261041,137261116⟩,
⟨64,199353987,199354097⟩]
theorem checked61565 : checkPrefixCuts (2^48) 8073379841 10 Manual.Count131072.C061565.packed 64 cuts61565 = true := by
 decide +kernel
def pointBounds61565 : List (Nat × Nat × Nat) := [(8073469952,114234709895549,114235098484661)]
theorem point_links_checked61565 : (cuts61565.take 1).map (fun c => (8073379841-1+2*2^10*c.k,114234572634508+c.lower,114234961223545+c.upper)) = pointBounds61565 := by
 decide +kernel
def cuts61566 : List PrefixCut := [⟨64,200431517,200431635⟩]
theorem checked61566 : checkPrefixCuts (2^48) 8073510913 10 Manual.Count131072.C061566.packed 64 cuts61566 = true := by
 decide +kernel
def cuts61567 : List PrefixCut := [⟨40,124461833,124461904⟩,
⟨64,198266750,198266864⟩]
theorem checked61567 : checkPrefixCuts (2^48) 8073641985 10 Manual.Count131072.C061567.packed 64 cuts61567 = true := by
 decide +kernel
def pointBounds61567 : List (Nat × Nat × Nat) := [(8073723904,114235096881845,114235485471181)]
theorem point_links_checked61567 : (cuts61567.take 1).map (fun c => (8073641985-1+2*2^10*c.k,114234972420012+c.lower,114235361009277+c.upper)) = pointBounds61567 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000048
