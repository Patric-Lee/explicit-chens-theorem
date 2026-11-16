import PlattAssemblyKernel
import PlattCertificates.Count131072.C062528
import PlattCertificates.Count131072.C062529
import PlattCertificates.Count131072.C062530
import PlattCertificates.Count131072.C062531
import PlattCertificates.Count131072.C062532
import PlattCertificates.Count131072.C062533
import PlattCertificates.Count131072.C062534
import PlattCertificates.Count131072.C062535
import PlattCertificates.Count131072.C062536
import PlattCertificates.Count131072.C062537
import PlattCertificates.Count131072.C062538
import PlattCertificates.Count131072.C062539
import PlattCertificates.Count131072.C062540
import PlattCertificates.Count131072.C062541
import PlattCertificates.Count131072.C062542
import PlattCertificates.Count131072.C062543
import PlattCertificates.Count131072.C062544
import PlattCertificates.Count131072.C062545
import PlattCertificates.Count131072.C062546
import PlattCertificates.Count131072.C062547
import PlattCertificates.Count131072.C062548
import PlattCertificates.Count131072.C062549
import PlattCertificates.Count131072.C062550
import PlattCertificates.Count131072.C062551
import PlattCertificates.Count131072.C062552
import PlattCertificates.Count131072.C062553
import PlattCertificates.Count131072.C062554
import PlattCertificates.Count131072.C062555
import PlattCertificates.Count131072.C062556
import PlattCertificates.Count131072.C062557
import PlattCertificates.Count131072.C062558
import PlattCertificates.Count131072.C062559
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000079
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62528 : List PrefixCut := [⟨64,195735972,195736084⟩]
theorem checked62528 : checkPrefixCuts (2^48) 8199602177 10 Manual.Count131072.C062528.packed 64 cuts62528 = true := by
 decide +kernel
def cuts62529 : List PrefixCut := [⟨44,134596694,134596771⟩,
⟨64,195458221,195458331⟩]
theorem checked62529 : checkPrefixCuts (2^48) 8199733249 10 Manual.Count131072.C062529.packed 64 cuts62529 = true := by
 decide +kernel
def pointBounds62529 : List (Nat × Nat × Nat) := [(8199823360,114426246901695,114426635600735)]
theorem point_links_checked62529 : (cuts62529.take 1).map (fun c => (8199733249-1+2*2^10*c.k,114426112305001+c.lower,114426501003964+c.upper)) = pointBounds62529 := by
 decide +kernel
def cuts62530 : List PrefixCut := [⟨64,195455093,195455203⟩]
theorem checked62530 : checkPrefixCuts (2^48) 8199864321 10 Manual.Count131072.C062530.packed 64 cuts62530 = true := by
 decide +kernel
def cuts62531 : List PrefixCut := [⟨42,130335996,130336069⟩,
⟨64,198712934,198713045⟩]
theorem checked62531 : checkPrefixCuts (2^48) 8199995393 10 Manual.Count131072.C062531.packed 64 cuts62531 = true := by
 decide +kernel
def pointBounds62531 : List (Nat × Nat × Nat) := [(8200081408,114426633554311,114427022253567)]
theorem point_links_checked62531 : (cuts62531.take 1).map (fun c => (8199995393-1+2*2^10*c.k,114426503218315+c.lower,114426891917498+c.upper)) = pointBounds62531 := by
 decide +kernel
def cuts62532 : List PrefixCut := [⟨64,195311528,195311642⟩]
theorem checked62532 : checkPrefixCuts (2^48) 8200126465 10 Manual.Count131072.C062532.packed 64 cuts62532 = true := by
 decide +kernel
def cuts62533 : List PrefixCut := [⟨40,124187689,124187763⟩,
⟨64,198672252,198672368⟩]
theorem checked62533 : checkPrefixCuts (2^48) 8200257537 10 Manual.Count131072.C062533.packed 64 cuts62533 = true := by
 decide +kernel
def pointBounds62533 : List (Nat × Nat × Nat) := [(8200339456,114427021430466,114427410129948)]
theorem point_links_checked62533 : (cuts62533.take 1).map (fun c => (8200257537-1+2*2^10*c.k,114426897242777+c.lower,114427285942185+c.upper)) = pointBounds62533 := by
 decide +kernel
def cuts62534 : List PrefixCut := [⟨64,195957465,195957581⟩]
theorem checked62534 : checkPrefixCuts (2^48) 8200388609 10 Manual.Count131072.C062534.packed 64 cuts62534 = true := by
 decide +kernel
def cuts62535 : List PrefixCut := [⟨38,117318983,117319052⟩,
⟨64,196606487,196606601⟩]
theorem checked62535 : checkPrefixCuts (2^48) 8200519681 10 Manual.Count131072.C062535.packed 64 cuts62535 = true := by
 decide +kernel
def pointBounds62535 : List (Nat × Nat × Nat) := [(8200597504,114427409191477,114427797891186)]
theorem point_links_checked62535 : (cuts62535.take 1).map (fun c => (8200519681-1+2*2^10*c.k,114427291872494+c.lower,114427680572134+c.upper)) = pointBounds62535 := by
 decide +kernel
def cuts62536 : List PrefixCut := [⟨64,201031031,201031146⟩]
theorem checked62536 : checkPrefixCuts (2^48) 8200650753 10 Manual.Count131072.C062536.packed 64 cuts62536 = true := by
 decide +kernel
def cuts62537 : List PrefixCut := [⟨36,110210454,110210512⟩,
⟨64,195124326,195124435⟩]
theorem checked62537 : checkPrefixCuts (2^48) 8200781825 10 Manual.Count131072.C062537.packed 64 cuts62537 = true := by
 decide +kernel
def pointBounds62537 : List (Nat × Nat × Nat) := [(8200855552,114427799720466,114428188420393)]
theorem point_links_checked62537 : (cuts62537.take 1).map (fun c => (8200781825-1+2*2^10*c.k,114427689510012+c.lower,114428078209881+c.upper)) = pointBounds62537 := by
 decide +kernel
def cuts62538 : List PrefixCut := [⟨64,200612741,200612857⟩]
theorem checked62538 : checkPrefixCuts (2^48) 8200912897 10 Manual.Count131072.C062538.packed 64 cuts62538 = true := by
 decide +kernel
def cuts62539 : List PrefixCut := [⟨34,106054026,106054089⟩,
⟨64,198172711,198172826⟩]
theorem checked62539 : checkPrefixCuts (2^48) 8201043969 10 Manual.Count131072.C062539.packed 64 cuts62539 = true := by
 decide +kernel
def pointBounds62539 : List (Nat × Nat × Nat) := [(8201113600,114428191301105,114428580001262)]
theorem point_links_checked62539 : (cuts62539.take 1).map (fun c => (8201043969-1+2*2^10*c.k,114428085247079+c.lower,114428473947173+c.upper)) = pointBounds62539 := by
 decide +kernel
def cuts62540 : List PrefixCut := [⟨64,201979177,201979292⟩]
theorem checked62540 : checkPrefixCuts (2^48) 8201175041 10 Manual.Count131072.C062540.packed 64 cuts62540 = true := by
 decide +kernel
def cuts62541 : List PrefixCut := [⟨32,98397168,98397226⟩,
⟨64,198097719,198097837⟩]
theorem checked62541 : checkPrefixCuts (2^48) 8201306113 10 Manual.Count131072.C062541.packed 64 cuts62541 = true := by
 decide +kernel
def pointBounds62541 : List (Nat × Nat × Nat) := [(8201371648,114428583796135,114428972496517)]
theorem point_links_checked62541 : (cuts62541.take 1).map (fun c => (8201306113-1+2*2^10*c.k,114428485398967+c.lower,114428874099291+c.upper)) = pointBounds62541 := by
 decide +kernel
def cuts62542 : List PrefixCut := [⟨64,197614084,197614200⟩]
theorem checked62542 : checkPrefixCuts (2^48) 8201437185 10 Manual.Count131072.C062542.packed 64 cuts62542 = true := by
 decide +kernel
def cuts62543 : List PrefixCut := [⟨30,91015355,91015407⟩,
⟨64,196169501,196169612⟩]
theorem checked62543 : checkPrefixCuts (2^48) 8201568257 10 Manual.Count131072.C062543.packed 64 cuts62543 = true := by
 decide +kernel
def pointBounds62543 : List (Nat × Nat × Nat) := [(8201629696,114428972126125,114429360826735)]
theorem point_links_checked62543 : (cuts62543.take 1).map (fun c => (8201568257-1+2*2^10*c.k,114428881110770+c.lower,114429269811328+c.upper)) = pointBounds62543 := by
 decide +kernel
def cuts62544 : List PrefixCut := [⟨64,196921399,196921508⟩]
theorem checked62544 : checkPrefixCuts (2^48) 8201699329 10 Manual.Count131072.C062544.packed 64 cuts62544 = true := by
 decide +kernel
def cuts62545 : List PrefixCut := [⟨28,85693110,85693158⟩,
⟨64,193314836,193314947⟩]
theorem checked62545 : checkPrefixCuts (2^48) 8201830401 10 Manual.Count131072.C062545.packed 64 cuts62545 = true := by
 decide +kernel
def pointBounds62545 : List (Nat × Nat × Nat) := [(8201887744,114429359894780,114429748595606)]
theorem point_links_checked62545 : (cuts62545.take 1).map (fun c => (8201830401-1+2*2^10*c.k,114429274201670+c.lower,114429662902448+c.upper)) = pointBounds62545 := by
 decide +kernel
def cuts62546 : List PrefixCut := [⟨64,200038000,200038118⟩]
theorem checked62546 : checkPrefixCuts (2^48) 8201961473 10 Manual.Count131072.C062546.packed 64 cuts62546 = true := by
 decide +kernel
def cuts62547 : List PrefixCut := [⟨26,78415120,78415165⟩,
⟨64,197769875,197769983⟩]
theorem checked62547 : checkPrefixCuts (2^48) 8202092545 10 Manual.Count131072.C062547.packed 64 cuts62547 = true := by
 decide +kernel
def pointBounds62547 : List (Nat × Nat × Nat) := [(8202145792,114429745969626,114430134670678)]
theorem point_links_checked62547 : (cuts62547.take 1).map (fun c => (8202092545-1+2*2^10*c.k,114429667554506+c.lower,114430056255513+c.upper)) = pointBounds62547 := by
 decide +kernel
def cuts62548 : List PrefixCut := [⟨64,196599966,196600075⟩]
theorem checked62548 : checkPrefixCuts (2^48) 8202223617 10 Manual.Count131072.C062548.packed 64 cuts62548 = true := by
 decide +kernel
def cuts62549 : List PrefixCut := [⟨24,73676990,73677032⟩,
⟨64,195292804,195292914⟩]
theorem checked62549 : checkPrefixCuts (2^48) 8202354689 10 Manual.Count131072.C062549.packed 64 cuts62549 = true := by
 decide +kernel
def pointBounds62549 : List (Nat × Nat × Nat) := [(8202403840,114430135601337,114430524302603)]
theorem point_links_checked62549 : (cuts62549.take 1).map (fun c => (8202354689-1+2*2^10*c.k,114430061924347+c.lower,114430450625571+c.upper)) = pointBounds62549 := by
 decide +kernel
def cuts62550 : List PrefixCut := [⟨64,196456412,196456527⟩]
theorem checked62550 : checkPrefixCuts (2^48) 8202485761 10 Manual.Count131072.C062550.packed 64 cuts62550 = true := by
 decide +kernel
def cuts62551 : List PrefixCut := [⟨22,68801901,68801939⟩,
⟨64,194977744,194977853⟩]
theorem checked62551 : checkPrefixCuts (2^48) 8202616833 10 Manual.Count131072.C062551.packed 64 cuts62551 = true := by
 decide +kernel
def pointBounds62551 : List (Nat × Nat × Nat) := [(8202661888,114430522475464,114430911176951)]
theorem point_links_checked62551 : (cuts62551.take 1).map (fun c => (8202616833-1+2*2^10*c.k,114430453673563+c.lower,114430842375012+c.upper)) = pointBounds62551 := by
 decide +kernel
def cuts62552 : List PrefixCut := [⟨64,197102106,197102221⟩]
theorem checked62552 : checkPrefixCuts (2^48) 8202747905 10 Manual.Count131072.C062552.packed 64 cuts62552 = true := by
 decide +kernel
def cuts62553 : List PrefixCut := [⟨20,63069265,63069303⟩,
⟨64,197339165,197339281⟩]
theorem checked62553 : checkPrefixCuts (2^48) 8202878977 10 Manual.Count131072.C062553.packed 64 cuts62553 = true := by
 decide +kernel
def pointBounds62553 : List (Nat × Nat × Nat) := [(8202919936,114430908822678,114431297524389)]
theorem point_links_checked62553 : (cuts62553.take 1).map (fun c => (8202878977-1+2*2^10*c.k,114430845753413+c.lower,114431234455086+c.upper)) = pointBounds62553 := by
 decide +kernel
def cuts62554 : List PrefixCut := [⟨64,196546782,196546899⟩]
theorem checked62554 : checkPrefixCuts (2^48) 8203010049 10 Manual.Count131072.C062554.packed 64 cuts62554 = true := by
 decide +kernel
def cuts62555 : List PrefixCut := [⟨18,55964481,55964513⟩,
⟨64,197332846,197332960⟩]
theorem checked62555 : checkPrefixCuts (2^48) 8203141121 10 Manual.Count131072.C062555.packed 64 cuts62555 = true := by
 decide +kernel
def pointBounds62555 : List (Nat × Nat × Nat) := [(8203177984,114431295603841,114431684305779)]
theorem point_links_checked62555 : (cuts62555.take 1).map (fun c => (8203141121-1+2*2^10*c.k,114431239639360+c.lower,114431628341266+c.upper)) = pointBounds62555 := by
 decide +kernel
def cuts62556 : List PrefixCut := [⟨64,201035415,201035528⟩]
theorem checked62556 : checkPrefixCuts (2^48) 8203272193 10 Manual.Count131072.C062556.packed 64 cuts62556 = true := by
 decide +kernel
def cuts62557 : List PrefixCut := [⟨16,49374820,49374851⟩,
⟨64,197978469,197978586⟩]
theorem checked62557 : checkPrefixCuts (2^48) 8203403265 10 Manual.Count131072.C062557.packed 64 cuts62557 = true := by
 decide +kernel
def pointBounds62557 : List (Nat × Nat × Nat) := [(8203436032,114431687382441,114432076084605)]
theorem point_links_checked62557 : (cuts62557.take 1).map (fun c => (8203403265-1+2*2^10*c.k,114431638007621+c.lower,114432026709754+c.upper)) = pointBounds62557 := by
 decide +kernel
def cuts62558 : List PrefixCut := [⟨64,197769443,197769558⟩]
theorem checked62558 : checkPrefixCuts (2^48) 8203534337 10 Manual.Count131072.C062558.packed 64 cuts62558 = true := by
 decide +kernel
def cuts62559 : List PrefixCut := [⟨14,43197312,43197335⟩,
⟨64,195261599,195261716⟩]
theorem checked62559 : checkPrefixCuts (2^48) 8203665409 10 Manual.Count131072.C062559.packed 64 cuts62559 = true := by
 decide +kernel
def pointBounds62559 : List (Nat × Nat × Nat) := [(8203694080,114432076952845,114432465655233)]
theorem point_links_checked62559 : (cuts62559.take 1).map (fun c => (8203665409-1+2*2^10*c.k,114432033755533+c.lower,114432422457898+c.upper)) = pointBounds62559 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000079
