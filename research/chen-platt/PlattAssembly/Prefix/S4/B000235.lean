import PlattAssemblyKernel
import PlattCertificates.Count131072.C037520
import PlattCertificates.Count131072.C037521
import PlattCertificates.Count131072.C037522
import PlattCertificates.Count131072.C037523
import PlattCertificates.Count131072.C037524
import PlattCertificates.Count131072.C037525
import PlattCertificates.Count131072.C037526
import PlattCertificates.Count131072.C037527
import PlattCertificates.Count131072.C037528
import PlattCertificates.Count131072.C037529
import PlattCertificates.Count131072.C037530
import PlattCertificates.Count131072.C037531
import PlattCertificates.Count131072.C037532
import PlattCertificates.Count131072.C037533
import PlattCertificates.Count131072.C037534
import PlattCertificates.Count131072.C037535
import PlattCertificates.Count131072.C037536
import PlattCertificates.Count131072.C037537
import PlattCertificates.Count131072.C037538
import PlattCertificates.Count131072.C037539
import PlattCertificates.Count131072.C037540
import PlattCertificates.Count131072.C037541
import PlattCertificates.Count131072.C037542
import PlattCertificates.Count131072.C037543
import PlattCertificates.Count131072.C037544
import PlattCertificates.Count131072.C037545
import PlattCertificates.Count131072.C037546
import PlattCertificates.Count131072.C037547
import PlattCertificates.Count131072.C037548
import PlattCertificates.Count131072.C037549
import PlattCertificates.Count131072.C037550
import PlattCertificates.Count131072.C037551
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000235
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts37520 : List PrefixCut := [⟨64,334899954,334900160⟩]
theorem checked37520 : checkPrefixCuts (2^48) 4921753601 10 Manual.Count131072.C037520.packed 64 cuts37520 = true := by
 decide +kernel
def cuts37521 : List PrefixCut := [⟨8,43977834,43977860⟩,
⟨64,337121357,337121563⟩]
theorem checked37521 : checkPrefixCuts (2^48) 4921884673 10 Manual.Count131072.C037521.packed 64 cuts37521 = true := by
 decide +kernel
def pointBounds37521 : List (Nat × Nat × Nat) := [(4921901056,108061124478350,108061509500735)]
theorem point_links_checked37521 : (cuts37521.take 1).map (fun c => (4921884673-1+2*2^10*c.k,108061080500516+c.lower,108061465522875+c.upper)) = pointBounds37521 := by
 decide +kernel
def cuts37522 : List PrefixCut := [⟨20,103736629,103736690⟩,
⟨64,333624008,333624208⟩]
theorem checked37522 : checkPrefixCuts (2^48) 4922015745 10 Manual.Count131072.C037522.packed 64 cuts37522 = true := by
 decide +kernel
def pointBounds37522 : List (Nat × Nat × Nat) := [(4922056704,108061521358502,108061906381128)]
theorem point_links_checked37522 : (cuts37522.take 1).map (fun c => (4922015745-1+2*2^10*c.k,108061417621873+c.lower,108061802644438+c.upper)) = pointBounds37522 := by
 decide +kernel
def cuts37523 : List PrefixCut := [⟨32,167838010,167838112⟩,
⟨64,336074078,336074282⟩]
theorem checked37523 : checkPrefixCuts (2^48) 4922146817 10 Manual.Count131072.C037523.packed 64 cuts37523 = true := by
 decide +kernel
def pointBounds37523 : List (Nat × Nat × Nat) := [(4922212352,108061919083891,108062304106758)]
theorem point_links_checked37523 : (cuts37523.take 1).map (fun c => (4922146817-1+2*2^10*c.k,108061751245881+c.lower,108062136268646+c.upper)) = pointBounds37523 := by
 decide +kernel
def cuts37524 : List PrefixCut := [⟨44,231821267,231821413⟩,
⟨64,336808483,336808693⟩]
theorem checked37524 : checkPrefixCuts (2^48) 4922277889 10 Manual.Count131072.C037524.packed 64 cuts37524 = true := by
 decide +kernel
def pointBounds37524 : List (Nat × Nat × Nat) := [(4922368000,108062319141226,108062704164341)]
theorem point_links_checked37524 : (cuts37524.take 1).map (fun c => (4922277889-1+2*2^10*c.k,108062087319959+c.lower,108062472342928+c.upper)) = pointBounds37524 := by
 decide +kernel
def cuts37525 : List PrefixCut := [⟨56,290425762,290425942⟩,
⟨64,333311452,333311656⟩]
theorem checked37525 : checkPrefixCuts (2^48) 4922408961 10 Manual.Count131072.C037525.packed 64 cuts37525 = true := by
 decide +kernel
def pointBounds37525 : List (Nat × Nat × Nat) := [(4922523648,108062714554204,108063099577563)]
theorem point_links_checked37525 : (cuts37525.take 1).map (fun c => (4922408961-1+2*2^10*c.k,108062424128442+c.lower,108062809151621+c.upper)) = pointBounds37525 := by
 decide +kernel
def cuts37526 : List PrefixCut := [⟨64,336333133,336333339⟩]
theorem checked37526 : checkPrefixCuts (2^48) 4922540033 10 Manual.Count131072.C037526.packed 64 cuts37526 = true := by
 decide +kernel
def cuts37527 : List PrefixCut := [⟨4,22128371,22128383⟩,
⟨64,338268227,338268431⟩]
theorem checked37527 : checkPrefixCuts (2^48) 4922671105 10 Manual.Count131072.C037527.packed 64 cuts37527 = true := by
 decide +kernel
def pointBounds37527 : List (Nat × Nat × Nat) := [(4922679296,108063115901398,108063500924999)]
theorem point_links_checked37527 : (cuts37527.take 1).map (fun c => (4922671105-1+2*2^10*c.k,108063093773027+c.lower,108063478796616+c.upper)) = pointBounds37527 := by
 decide +kernel
def cuts37528 : List PrefixCut := [⟨16,84336941,84336992⟩,
⟨64,336143682,336143885⟩]
theorem checked37528 : checkPrefixCuts (2^48) 4922802177 10 Manual.Count131072.C037528.packed 64 cuts37528 = true := by
 decide +kernel
def pointBounds37528 : List (Nat × Nat × Nat) := [(4922834944,108063516378195,108063901402039)]
theorem point_links_checked37528 : (cuts37528.take 1).map (fun c => (4922802177-1+2*2^10*c.k,108063432041254+c.lower,108063817065047+c.upper)) = pointBounds37528 := by
 decide +kernel
def cuts37529 : List PrefixCut := [⟨28,145970132,145970217⟩,
⟨64,335848834,335849033⟩]
theorem checked37529 : checkPrefixCuts (2^48) 4922933249 10 Manual.Count131072.C037529.packed 64 cuts37529 = true := by
 decide +kernel
def pointBounds37529 : List (Nat × Nat × Nat) := [(4922990592,108063914155068,108064299179149)]
theorem point_links_checked37529 : (cuts37529.take 1).map (fun c => (4922933249-1+2*2^10*c.k,108063768184936+c.lower,108064153208932+c.upper)) = pointBounds37529 := by
 decide +kernel
def cuts37530 : List PrefixCut := [⟨40,212516737,212516862⟩,
⟨64,340356682,340356883⟩]
theorem checked37530 : checkPrefixCuts (2^48) 4923064321 10 Manual.Count131072.C037530.packed 64 cuts37530 = true := by
 decide +kernel
def pointBounds37530 : List (Nat × Nat × Nat) := [(4923146240,108064316550507,108064701574827)]
theorem point_links_checked37530 : (cuts37530.take 1).map (fun c => (4923064321-1+2*2^10*c.k,108064104033770+c.lower,108064489057965+c.upper)) = pointBounds37530 := by
 decide +kernel
def cuts37531 : List PrefixCut := [⟨52,271569802,271569967⟩,
⟨64,333029520,333029723⟩]
theorem checked37531 : checkPrefixCuts (2^48) 4923195393 10 Manual.Count131072.C037531.packed 64 cuts37531 = true := by
 decide +kernel
def pointBounds37531 : List (Nat × Nat × Nat) := [(4923301888,108064715960254,108065100984815)]
theorem point_links_checked37531 : (cuts37531.take 1).map (fun c => (4923195393-1+2*2^10*c.k,108064444390452+c.lower,108064829414848+c.upper)) = pointBounds37531 := by
 decide +kernel
def cuts37532 : List PrefixCut := [⟨64,335993546,335993752⟩]
theorem checked37532 : checkPrefixCuts (2^48) 4923326465 10 Manual.Count131072.C037532.packed 64 cuts37532 = true := by
 decide +kernel
def pointBounds37532 : List (Nat × Nat × Nat) := [(4923457536,108065113413518,108065498438323)]
theorem point_links_checked37532 : (cuts37532.take 1).map (fun c => (4923326465-1+2*2^10*c.k,108064777419972+c.lower,108065162444571+c.upper)) = pointBounds37532 := by
 decide +kernel
def cuts37533 : List PrefixCut := [⟨64,338614436,338614641⟩]
theorem checked37533 : checkPrefixCuts (2^48) 4923457537 10 Manual.Count131072.C037533.packed 64 cuts37533 = true := by
 decide +kernel
def cuts37534 : List PrefixCut := [⟨12,61856320,61856357⟩,
⟨64,336147140,336147344⟩]
theorem checked37534 : checkPrefixCuts (2^48) 4923588609 10 Manual.Count131072.C037534.packed 64 cuts37534 = true := by
 decide +kernel
def pointBounds37534 : List (Nat × Nat × Nat) := [(4923613184,108065513884274,108065898909321)]
theorem point_links_checked37534 : (cuts37534.take 1).map (fun c => (4923588609-1+2*2^10*c.k,108065452027954+c.lower,108065837052964+c.upper)) = pointBounds37534 := by
 decide +kernel
def cuts37535 : List PrefixCut := [⟨24,125881381,125881459⟩,
⟨64,335280738,335280945⟩]
theorem checked37535 : checkPrefixCuts (2^48) 4923719681 10 Manual.Count131072.C037535.packed 64 cuts37535 = true := by
 decide +kernel
def pointBounds37535 : List (Nat × Nat × Nat) := [(4923768832,108065914056475,108066299081767)]
theorem point_links_checked37535 : (cuts37535.take 1).map (fun c => (4923719681-1+2*2^10*c.k,108065788175094+c.lower,108066173200308+c.upper)) = pointBounds37535 := by
 decide +kernel
def cuts37536 : List PrefixCut := [⟨36,187501764,187501875⟩,
⟨64,332928044,332928243⟩]
theorem checked37536 : checkPrefixCuts (2^48) 4923850753 10 Manual.Count131072.C037536.packed 64 cuts37536 = true := by
 decide +kernel
def pointBounds37536 : List (Nat × Nat × Nat) := [(4923924480,108066310957596,108066695983128)]
theorem point_links_checked37536 : (cuts37536.take 1).map (fun c => (4923850753-1+2*2^10*c.k,108066123455832+c.lower,108066508481253+c.upper)) = pointBounds37536 := by
 decide +kernel
def cuts37537 : List PrefixCut := [⟨48,251633797,251633953⟩,
⟨64,333948157,333948363⟩]
theorem checked37537 : checkPrefixCuts (2^48) 4923981825 10 Manual.Count131072.C037537.packed 64 cuts37537 = true := by
 decide +kernel
def pointBounds37537 : List (Nat × Nat × Nat) := [(4924080128,108066708017673,108067093043449)]
theorem point_links_checked37537 : (cuts37537.take 1).map (fun c => (4923981825-1+2*2^10*c.k,108066456383876+c.lower,108066841409496+c.upper)) = pointBounds37537 := by
 decide +kernel
def cuts37538 : List PrefixCut := [⟨60,311017599,311017790⟩,
⟨64,332110040,332110243⟩]
theorem checked37538 : checkPrefixCuts (2^48) 4924112897 10 Manual.Count131072.C037538.packed 64 cuts37538 = true := by
 decide +kernel
def pointBounds37538 : List (Nat × Nat × Nat) := [(4924235776,108067101349632,108067486375649)]
theorem point_links_checked37538 : (cuts37538.take 1).map (fun c => (4924112897-1+2*2^10*c.k,108066790332033+c.lower,108067175357859+c.upper)) = pointBounds37538 := by
 decide +kernel
def cuts37539 : List PrefixCut := [⟨64,338960435,338960642⟩]
theorem checked37539 : checkPrefixCuts (2^48) 4924243969 10 Manual.Count131072.C037539.packed 64 cuts37539 = true := by
 decide +kernel
def cuts37540 : List PrefixCut := [⟨8,40354552,40354575⟩,
⟨64,334092899,334093105⟩]
theorem checked37540 : checkPrefixCuts (2^48) 4924375041 10 Manual.Count131072.C037540.packed 64 cuts37540 = true := by
 decide +kernel
def pointBounds37540 : List (Nat × Nat × Nat) := [(4924391424,108067501757060,108067886783319)]
theorem point_links_checked37540 : (cuts37540.take 1).map (fun c => (4924375041-1+2*2^10*c.k,108067461402508+c.lower,108067846428744+c.upper)) = pointBounds37540 := by
 decide +kernel
def cuts37541 : List PrefixCut := [⟨20,106370584,106370645⟩,
⟨64,335741615,335741816⟩]
theorem checked37541 : checkPrefixCuts (2^48) 4924506113 10 Manual.Count131072.C037541.packed 64 cuts37541 = true := by
 decide +kernel
def pointBounds37541 : List (Nat × Nat × Nat) := [(4924547072,108067901865991,108068286892494)]
theorem point_links_checked37541 : (cuts37541.take 1).map (fun c => (4924506113-1+2*2^10*c.k,108067795495407+c.lower,108068180521849+c.upper)) = pointBounds37541 := by
 decide +kernel
def cuts37542 : List PrefixCut := [⟨32,164266628,164266732⟩,
⟨64,333903666,333903872⟩]
theorem checked37542 : checkPrefixCuts (2^48) 4924637185 10 Manual.Count131072.C037542.packed 64 cuts37542 = true := by
 decide +kernel
def pointBounds37542 : List (Nat × Nat × Nat) := [(4924702720,108068295503650,108068680530397)]
theorem point_links_checked37542 : (cuts37542.take 1).map (fun c => (4924637185-1+2*2^10*c.k,108068131237022+c.lower,108068516263665+c.upper)) = pointBounds37542 := by
 decide +kernel
def cuts37543 : List PrefixCut := [⟨44,230732424,230732565⟩,
⟨64,333723330,333723534⟩]
theorem checked37543 : checkPrefixCuts (2^48) 4924768257 10 Manual.Count131072.C037543.packed 64 cuts37543 = true := by
 decide +kernel
def pointBounds37543 : List (Nat × Nat × Nat) := [(4924858368,108068695873112,108069080900102)]
theorem point_links_checked37543 : (cuts37543.take 1).map (fun c => (4924768257-1+2*2^10*c.k,108068465140688+c.lower,108068850167537+c.upper)) = pointBounds37543 := by
 decide +kernel
def cuts37544 : List PrefixCut := [⟨56,297194362,297194543⟩,
⟨64,339886908,339887116⟩]
theorem checked37544 : checkPrefixCuts (2^48) 4924899329 10 Manual.Count131072.C037544.packed 64 cuts37544 = true := by
 decide +kernel
def pointBounds37544 : List (Nat × Nat × Nat) := [(4925014016,108069096058380,108069481085614)]
theorem point_links_checked37544 : (cuts37544.take 1).map (fun c => (4924899329-1+2*2^10*c.k,108068798864018+c.lower,108069183891071+c.upper)) = pointBounds37544 := by
 decide +kernel
def cuts37545 : List PrefixCut := [⟨64,333705564,333705766⟩]
theorem checked37545 : checkPrefixCuts (2^48) 4925030401 10 Manual.Count131072.C037545.packed 64 cuts37545 = true := by
 decide +kernel
def cuts37546 : List PrefixCut := [⟨4,20174069,20174082⟩,
⟨64,337239934,337240141⟩]
theorem checked37546 : checkPrefixCuts (2^48) 4925161473 10 Manual.Count131072.C037546.packed 64 cuts37546 = true := by
 decide +kernel
def pointBounds37546 : List (Nat × Nat × Nat) := [(4925169664,108069492630559,108069877658035)]
theorem point_links_checked37546 : (cuts37546.take 1).map (fun c => (4925161473-1+2*2^10*c.k,108069472456490+c.lower,108069857483953+c.upper)) = pointBounds37546 := by
 decide +kernel
def cuts37547 : List PrefixCut := [⟨16,84580041,84580092⟩,
⟨64,338545388,338545591⟩]
theorem checked37547 : checkPrefixCuts (2^48) 4925292545 10 Manual.Count131072.C037547.packed 64 cuts37547 = true := by
 decide +kernel
def pointBounds37547 : List (Nat × Nat × Nat) := [(4925325312,108069894276465,108070279304186)]
theorem point_links_checked37547 : (cuts37547.take 1).map (fun c => (4925292545-1+2*2^10*c.k,108069809696424+c.lower,108070194724094+c.upper)) = pointBounds37547 := by
 decide +kernel
def cuts37548 : List PrefixCut := [⟨28,147610749,147610835⟩,
⟨64,339564985,339565192⟩]
theorem checked37548 : checkPrefixCuts (2^48) 4925423617 10 Manual.Count131072.C037548.packed 64 cuts37548 = true := by
 decide +kernel
def pointBounds37548 : List (Nat × Nat × Nat) := [(4925480960,108070295852561,108070680880520)]
theorem point_links_checked37548 : (cuts37548.take 1).map (fun c => (4925423617-1+2*2^10*c.k,108070148241812+c.lower,108070533269685+c.upper)) = pointBounds37548 := by
 decide +kernel
def cuts37549 : List PrefixCut := [⟨40,205723287,205723413⟩,
⟨64,334241469,334241670⟩]
theorem checked37549 : checkPrefixCuts (2^48) 4925554689 10 Manual.Count131072.C037549.packed 64 cuts37549 = true := by
 decide +kernel
def pointBounds37549 : List (Nat × Nat × Nat) := [(4925636608,108070693530084,108071078558290)]
theorem point_links_checked37549 : (cuts37549.take 1).map (fun c => (4925554689-1+2*2^10*c.k,108070487806797+c.lower,108070872834877+c.upper)) = pointBounds37549 := by
 decide +kernel
def cuts37550 : List PrefixCut := [⟨52,272232514,272232684⟩,
⟨64,335546877,335547086⟩]
theorem checked37550 : checkPrefixCuts (2^48) 4925685761 10 Manual.Count131072.C037550.packed 64 cuts37550 = true := by
 decide +kernel
def pointBounds37550 : List (Nat × Nat × Nat) := [(4925792256,108071094280780,108071479309231)]
theorem point_links_checked37550 : (cuts37550.take 1).map (fun c => (4925685761-1+2*2^10*c.k,108070822048266+c.lower,108071207076547+c.upper)) = pointBounds37550 := by
 decide +kernel
def cuts37551 : List PrefixCut := [⟨64,337423664,337423868⟩]
theorem checked37551 : checkPrefixCuts (2^48) 4925816833 10 Manual.Count131072.C037551.packed 64 cuts37551 = true := by
 decide +kernel
def pointBounds37551 : List (Nat × Nat × Nat) := [(4925947904,108071495018807,108071880047501)]
theorem point_links_checked37551 : (cuts37551.take 1).map (fun c => (4925816833-1+2*2^10*c.k,108071157595143+c.lower,108071542623633+c.upper)) = pointBounds37551 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000235
