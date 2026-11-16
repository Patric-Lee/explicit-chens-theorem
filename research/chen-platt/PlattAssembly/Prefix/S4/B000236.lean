import PlattAssemblyKernel
import PlattCertificates.Count131072.C037552
import PlattCertificates.Count131072.C037553
import PlattCertificates.Count131072.C037554
import PlattCertificates.Count131072.C037555
import PlattCertificates.Count131072.C037556
import PlattCertificates.Count131072.C037557
import PlattCertificates.Count131072.C037558
import PlattCertificates.Count131072.C037559
import PlattCertificates.Count131072.C037560
import PlattCertificates.Count131072.C037561
import PlattCertificates.Count131072.C037562
import PlattCertificates.Count131072.C037563
import PlattCertificates.Count131072.C037564
import PlattCertificates.Count131072.C037565
import PlattCertificates.Count131072.C037566
import PlattCertificates.Count131072.C037567
import PlattCertificates.Count131072.C037568
import PlattCertificates.Count131072.C037569
import PlattCertificates.Count131072.C037570
import PlattCertificates.Count131072.C037571
import PlattCertificates.Count131072.C037572
import PlattCertificates.Count131072.C037573
import PlattCertificates.Count131072.C037574
import PlattCertificates.Count131072.C037575
import PlattCertificates.Count131072.C037576
import PlattCertificates.Count131072.C037577
import PlattCertificates.Count131072.C037578
import PlattCertificates.Count131072.C037579
import PlattCertificates.Count131072.C037580
import PlattCertificates.Count131072.C037581
import PlattCertificates.Count131072.C037582
import PlattCertificates.Count131072.C037583
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000236
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts37552 : List PrefixCut := [⟨64,333072004,333072210⟩]
theorem checked37552 : checkPrefixCuts (2^48) 4925947905 10 Manual.Count131072.C037552.packed 64 cuts37552 = true := by
 decide +kernel
def cuts37553 : List PrefixCut := [⟨12,62625002,62625040⟩,
⟨64,330834760,330834965⟩]
theorem checked37553 : checkPrefixCuts (2^48) 4926078977 10 Manual.Count131072.C037553.packed 64 cuts37553 = true := by
 decide +kernel
def pointBounds37553 : List (Nat × Nat × Nat) := [(4926103552,108071890715813,108072275744751)]
theorem point_links_checked37553 : (cuts37553.take 1).map (fun c => (4926078977-1+2*2^10*c.k,108071828090811+c.lower,108072213119711+c.upper)) = pointBounds37553 := by
 decide +kernel
def cuts37554 : List PrefixCut := [⟨24,127017641,127017715⟩,
⟨64,340367875,340368079⟩]
theorem checked37554 : checkPrefixCuts (2^48) 4926210049 10 Manual.Count131072.C037554.packed 64 cuts37554 = true := by
 decide +kernel
def pointBounds37554 : List (Nat × Nat × Nat) := [(4926259200,108072285943212,108072670972391)]
theorem point_links_checked37554 : (cuts37554.take 1).map (fun c => (4926210049-1+2*2^10*c.k,108072158925571+c.lower,108072543954676+c.upper)) = pointBounds37554 := by
 decide +kernel
def cuts37555 : List PrefixCut := [⟨36,188378279,188378392⟩,
⟨64,333902434,333902639⟩]
theorem checked37555 : checkPrefixCuts (2^48) 4926341121 10 Manual.Count131072.C037555.packed 64 cuts37555 = true := by
 decide +kernel
def pointBounds37555 : List (Nat × Nat × Nat) := [(4926414848,108072687671725,108073072701147)]
theorem point_links_checked37555 : (cuts37555.take 1).map (fun c => (4926341121-1+2*2^10*c.k,108072499293446+c.lower,108072884322755+c.upper)) = pointBounds37555 := by
 decide +kernel
def cuts37556 : List PrefixCut := [⟨48,249906774,249906928⟩,
⟨64,335436150,335436353⟩]
theorem checked37556 : checkPrefixCuts (2^48) 4926472193 10 Manual.Count131072.C037556.packed 64 cuts37556 = true := by
 decide +kernel
def pointBounds37556 : List (Nat × Nat × Nat) := [(4926570496,108073083102654,108073468132322)]
theorem point_links_checked37556 : (cuts37556.take 1).map (fun c => (4926472193-1+2*2^10*c.k,108072833195880+c.lower,108073218225394+c.upper)) = pointBounds37556 := by
 decide +kernel
def cuts37557 : List PrefixCut := [⟨60,310174814,310175007⟩,
⟨64,331256592,331256800⟩]
theorem checked37557 : checkPrefixCuts (2^48) 4926603265 10 Manual.Count131072.C037557.packed 64 cuts37557 = true := by
 decide +kernel
def pointBounds37557 : List (Nat × Nat × Nat) := [(4926726144,108073478806844,108073863836754)]
theorem point_links_checked37557 : (cuts37557.take 1).map (fun c => (4926603265-1+2*2^10*c.k,108073168632030+c.lower,108073553661747+c.upper)) = pointBounds37557 := by
 decide +kernel
def cuts37558 : List PrefixCut := [⟨64,335932545,335932747⟩]
theorem checked37558 : checkPrefixCuts (2^48) 4926734337 10 Manual.Count131072.C037558.packed 64 cuts37558 = true := by
 decide +kernel
def cuts37559 : List PrefixCut := [⟨8,41933810,41933836⟩,
⟨64,335752220,335752423⟩]
theorem checked37559 : checkPrefixCuts (2^48) 4926865409 10 Manual.Count131072.C037559.packed 64 cuts37559 = true := by
 decide +kernel
def pointBounds37559 : List (Nat × Nat × Nat) := [(4926881792,108073877754977,108074262785130)]
theorem point_links_checked37559 : (cuts37559.take 1).map (fun c => (4926865409-1+2*2^10*c.k,108073835821167+c.lower,108074220851294+c.upper)) = pointBounds37559 := by
 decide +kernel
def cuts37560 : List PrefixCut := [⟨20,105745534,105745598⟩,
⟨64,333401043,333401245⟩]
theorem checked37560 : checkPrefixCuts (2^48) 4926996481 10 Manual.Count131072.C037560.packed 64 cuts37560 = true := by
 decide +kernel
def pointBounds37560 : List (Nat × Nat × Nat) := [(4927037440,108074277318921,108074662349315)]
theorem point_links_checked37560 : (cuts37560.take 1).map (fun c => (4926996481-1+2*2^10*c.k,108074171573387+c.lower,108074556603717+c.upper)) = pointBounds37560 := by
 decide +kernel
def cuts37561 : List PrefixCut := [⟨32,166183027,166183129⟩,
⟨64,334020532,334020738⟩]
theorem checked37561 : checkPrefixCuts (2^48) 4927127553 10 Manual.Count131072.C037561.packed 64 cuts37561 = true := by
 decide +kernel
def pointBounds37561 : List (Nat × Nat × Nat) := [(4927193088,108074671157457,108075056188091)]
theorem point_links_checked37561 : (cuts37561.take 1).map (fun c => (4927127553-1+2*2^10*c.k,108074504974430+c.lower,108074890004962+c.upper)) = pointBounds37561 := by
 decide +kernel
def cuts37562 : List PrefixCut := [⟨44,229187667,229187805⟩,
⟨64,333269022,333269224⟩]
theorem checked37562 : checkPrefixCuts (2^48) 4927258625 10 Manual.Count131072.C037562.packed 64 cuts37562 = true := by
 decide +kernel
def pointBounds37562 : List (Nat × Nat × Nat) := [(4927348736,108075068182629,108075453213505)]
theorem point_links_checked37562 : (cuts37562.take 1).map (fun c => (4927258625-1+2*2^10*c.k,108074838994962+c.lower,108075224025700+c.upper)) = pointBounds37562 := by
 decide +kernel
def cuts37563 : List PrefixCut := [⟨56,292474250,292474430⟩,
⟨64,335202342,335202549⟩]
theorem checked37563 : checkPrefixCuts (2^48) 4927389697 10 Manual.Count131072.C037563.packed 64 cuts37563 = true := by
 decide +kernel
def pointBounds37563 : List (Nat × Nat × Nat) := [(4927504384,108075464738234,108075849769354)]
theorem point_links_checked37563 : (cuts37563.take 1).map (fun c => (4927389697-1+2*2^10*c.k,108075172263984+c.lower,108075557294924+c.upper)) = pointBounds37563 := by
 decide +kernel
def cuts37564 : List PrefixCut := [⟨64,332737182,332737389⟩]
theorem checked37564 : checkPrefixCuts (2^48) 4927520769 10 Manual.Count131072.C037564.packed 64 cuts37564 = true := by
 decide +kernel
def cuts37565 : List PrefixCut := [⟨4,19535537,19535550⟩,
⟨64,334841765,334841973⟩]
theorem checked37565 : checkPrefixCuts (2^48) 4927651841 10 Manual.Count131072.C037565.packed 64 cuts37565 = true := by
 decide +kernel
def pointBounds37565 : List (Nat × Nat × Nat) := [(4927660032,108075859739045,108076244770412)]
theorem point_links_checked37565 : (cuts37565.take 1).map (fun c => (4927651841-1+2*2^10*c.k,108075840203508+c.lower,108076225234862+c.upper)) = pointBounds37565 := by
 decide +kernel
def cuts37566 : List PrefixCut := [⟨16,82880825,82880876⟩,
⟨64,337574605,337574810⟩]
theorem checked37566 : checkPrefixCuts (2^48) 4927782913 10 Manual.Count131072.C037566.packed 64 cuts37566 = true := by
 decide +kernel
def pointBounds37566 : List (Nat × Nat × Nat) := [(4927815680,108076257926098,108076642957711)]
theorem point_links_checked37566 : (cuts37566.take 1).map (fun c => (4927782913-1+2*2^10*c.k,108076175045273+c.lower,108076560076835+c.upper)) = pointBounds37566 := by
 decide +kernel
def cuts37567 : List PrefixCut := [⟨28,147364778,147364868⟩,
⟨64,342135013,342135217⟩]
theorem checked37567 : checkPrefixCuts (2^48) 4927913985 10 Manual.Count131072.C037567.packed 64 cuts37567 = true := by
 decide +kernel
def pointBounds37567 : List (Nat × Nat × Nat) := [(4927971328,108076659984656,108077045016513)]
theorem point_links_checked37567 : (cuts37567.take 1).map (fun c => (4927913985-1+2*2^10*c.k,108076512619878+c.lower,108076897651645+c.upper)) = pointBounds37567 := by
 decide +kernel
def cuts37568 : List PrefixCut := [⟨40,209960143,209960271⟩,
⟨64,333787014,333787219⟩]
theorem checked37568 : checkPrefixCuts (2^48) 4928045057 10 Manual.Count131072.C037568.packed 64 cuts37568 = true := by
 decide +kernel
def pointBounds37568 : List (Nat × Nat × Nat) := [(4928126976,108077064715034,108077449747133)]
theorem point_links_checked37568 : (cuts37568.take 1).map (fun c => (4928045057-1+2*2^10*c.k,108076854754891+c.lower,108077239786862+c.upper)) = pointBounds37568 := by
 decide +kernel
def cuts37569 : List PrefixCut := [⟨52,274779353,274779518⟩,
⟨64,337661923,337662128⟩]
theorem checked37569 : checkPrefixCuts (2^48) 4928176129 10 Manual.Count131072.C037569.packed 64 cuts37569 = true := by
 decide +kernel
def pointBounds37569 : List (Nat × Nat × Nat) := [(4928282624,108077463321258,108077848353599)]
theorem point_links_checked37569 : (cuts37569.take 1).map (fun c => (4928176129-1+2*2^10*c.k,108077188541905+c.lower,108077573574081+c.upper)) = pointBounds37569 := by
 decide +kernel
def cuts37570 : List PrefixCut := [⟨64,337481610,337481807⟩]
theorem checked37570 : checkPrefixCuts (2^48) 4928307201 10 Manual.Count131072.C037570.packed 64 cuts37570 = true := by
 decide +kernel
def pointBounds37570 : List (Nat × Nat × Nat) := [(4928438272,108077863685438,108078248718016)]
theorem point_links_checked37570 : (cuts37570.take 1).map (fun c => (4928307201-1+2*2^10*c.k,108077526203828+c.lower,108077911236209+c.upper)) = pointBounds37570 := by
 decide +kernel
def cuts37571 : List PrefixCut := [⟨64,333360604,333360804⟩]
theorem checked37571 : checkPrefixCuts (2^48) 4928438273 10 Manual.Count131072.C037571.packed 64 cuts37571 = true := by
 decide +kernel
def cuts37572 : List PrefixCut := [⟨12,62479137,62479175⟩,
⟨64,337235211,337235415⟩]
theorem checked37572 : checkPrefixCuts (2^48) 4928569345 10 Manual.Count131072.C037572.packed 64 cuts37572 = true := by
 decide +kernel
def pointBounds37572 : List (Nat × Nat × Nat) := [(4928593920,108078259525179,108078644557995)]
theorem point_links_checked37572 : (cuts37572.take 1).map (fun c => (4928569345-1+2*2^10*c.k,108078197046042+c.lower,108078582078820+c.upper)) = pointBounds37572 := by
 decide +kernel
def cuts37573 : List PrefixCut := [⟨24,126153930,126154006⟩,
⟨64,334028165,334028366⟩]
theorem checked37573 : checkPrefixCuts (2^48) 4928700417 10 Manual.Count131072.C037573.packed 64 cuts37573 = true := by
 decide +kernel
def pointBounds37573 : List (Nat × Nat × Nat) := [(4928749568,108078660435183,108079045468241)]
theorem point_links_checked37573 : (cuts37573.take 1).map (fun c => (4928700417-1+2*2^10*c.k,108078534281253+c.lower,108078919314235+c.upper)) = pointBounds37573 := by
 decide +kernel
def cuts37574 : List PrefixCut := [⟨36,188911287,188911404⟩,
⟨64,336988825,336989030⟩]
theorem checked37574 : checkPrefixCuts (2^48) 4928831489 10 Manual.Count131072.C037574.packed 64 cuts37574 = true := by
 decide +kernel
def pointBounds37574 : List (Nat × Nat × Nat) := [(4928905216,108079057220705,108079442254005)]
theorem point_links_checked37574 : (cuts37574.take 1).map (fun c => (4928831489-1+2*2^10*c.k,108078868309418+c.lower,108079253342601+c.upper)) = pointBounds37574 := by
 decide +kernel
def cuts37575 : List PrefixCut := [⟨48,252293168,252293316⟩,
⟨64,336123288,336123485⟩]
theorem checked37575 : checkPrefixCuts (2^48) 4928962561 10 Manual.Count131072.C037575.packed 64 cuts37575 = true := by
 decide +kernel
def pointBounds37575 : List (Nat × Nat × Nat) := [(4929060864,108079457591411,108079842624947)]
theorem point_links_checked37575 : (cuts37575.take 1).map (fun c => (4928962561-1+2*2^10*c.k,108079205298243+c.lower,108079590331631+c.upper)) = pointBounds37575 := by
 decide +kernel
def cuts37576 : List PrefixCut := [⟨60,314814831,314815026⟩,
⟨64,335714648,335714855⟩]
theorem checked37576 : checkPrefixCuts (2^48) 4929093633 10 Manual.Count131072.C037576.packed 64 cuts37576 = true := by
 decide +kernel
def pointBounds37576 : List (Nat × Nat × Nat) := [(4929216512,108079856236362,108080241270142)]
theorem point_links_checked37576 : (cuts37576.take 1).map (fun c => (4929093633-1+2*2^10*c.k,108079541421531+c.lower,108079926455116+c.upper)) = pointBounds37576 := by
 decide +kernel
def cuts37577 : List PrefixCut := [⟨64,331023304,331023503⟩]
theorem checked37577 : checkPrefixCuts (2^48) 4929224705 10 Manual.Count131072.C037577.packed 64 cuts37577 = true := by
 decide +kernel
def cuts37578 : List PrefixCut := [⟨8,40884791,40884816⟩,
⟨64,338266316,338266521⟩]
theorem checked37578 : checkPrefixCuts (2^48) 4929355777 10 Manual.Count131072.C037578.packed 64 cuts37578 = true := by
 decide +kernel
def pointBounds37578 : List (Nat × Nat × Nat) := [(4929372160,108080249044274,108080634078290)]
theorem point_links_checked37578 : (cuts37578.take 1).map (fun c => (4929355777-1+2*2^10*c.k,108080208159483+c.lower,108080593193474+c.upper)) = pointBounds37578 := by
 decide +kernel
def cuts37579 : List PrefixCut := [⟨20,104607203,104607264⟩,
⟨64,333632284,333632486⟩]
theorem checked37579 : checkPrefixCuts (2^48) 4929486849 10 Manual.Count131072.C037579.packed 64 cuts37579 = true := by
 decide +kernel
def pointBounds37579 : List (Nat × Nat × Nat) := [(4929527808,108080651033002,108081036067259)]
theorem point_links_checked37579 : (cuts37579.take 1).map (fun c => (4929486849-1+2*2^10*c.k,108080546425799+c.lower,108080931459995+c.upper)) = pointBounds37579 := by
 decide +kernel
def cuts37580 : List PrefixCut := [⟨32,171523421,171523529⟩,
⟨64,342016818,342017029⟩]
theorem checked37580 : checkPrefixCuts (2^48) 4929617921 10 Manual.Count131072.C037580.packed 64 cuts37580 = true := by
 decide +kernel
def pointBounds37580 : List (Nat × Nat × Nat) := [(4929683456,108081051581504,108081436616010)]
theorem point_links_checked37580 : (cuts37580.take 1).map (fun c => (4929617921-1+2*2^10*c.k,108080880058083+c.lower,108081265092481+c.upper)) = pointBounds37580 := by
 decide +kernel
def cuts37581 : List PrefixCut := [⟨44,229585782,229585922⟩,
⟨64,333900040,333900243⟩]
theorem checked37581 : checkPrefixCuts (2^48) 4929748993 10 Manual.Count131072.C037581.packed 64 cuts37581 = true := by
 decide +kernel
def pointBounds37581 : List (Nat × Nat × Nat) := [(4929839104,108081451660683,108081836695432)]
theorem point_links_checked37581 : (cuts37581.take 1).map (fun c => (4929748993-1+2*2^10*c.k,108081222074901+c.lower,108081607109510+c.upper)) = pointBounds37581 := by
 decide +kernel
def cuts37582 : List PrefixCut := [⟨56,290899125,290899304⟩,
⟨64,331835711,331835914⟩]
theorem checked37582 : checkPrefixCuts (2^48) 4929880065 10 Manual.Count131072.C037582.packed 64 cuts37582 = true := by
 decide +kernel
def pointBounds37582 : List (Nat × Nat × Nat) := [(4929994752,108081846874066,108082231909057)]
theorem point_links_checked37582 : (cuts37582.take 1).map (fun c => (4929880065-1+2*2^10*c.k,108081555974941+c.lower,108081941009753+c.upper)) = pointBounds37582 := by
 decide +kernel
def cuts37583 : List PrefixCut := [⟨64,336793998,336794206⟩]
theorem checked37583 : checkPrefixCuts (2^48) 4930011137 10 Manual.Count131072.C037583.packed 64 cuts37583 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000236
