import PlattAssemblyKernel
import PlattCertificates.Count131072.C035600
import PlattCertificates.Count131072.C035601
import PlattCertificates.Count131072.C035602
import PlattCertificates.Count131072.C035603
import PlattCertificates.Count131072.C035604
import PlattCertificates.Count131072.C035605
import PlattCertificates.Count131072.C035606
import PlattCertificates.Count131072.C035607
import PlattCertificates.Count131072.C035608
import PlattCertificates.Count131072.C035609
import PlattCertificates.Count131072.C035610
import PlattCertificates.Count131072.C035611
import PlattCertificates.Count131072.C035612
import PlattCertificates.Count131072.C035613
import PlattCertificates.Count131072.C035614
import PlattCertificates.Count131072.C035615
import PlattCertificates.Count131072.C035616
import PlattCertificates.Count131072.C035617
import PlattCertificates.Count131072.C035618
import PlattCertificates.Count131072.C035619
import PlattCertificates.Count131072.C035620
import PlattCertificates.Count131072.C035621
import PlattCertificates.Count131072.C035622
import PlattCertificates.Count131072.C035623
import PlattCertificates.Count131072.C035624
import PlattCertificates.Count131072.C035625
import PlattCertificates.Count131072.C035626
import PlattCertificates.Count131072.C035627
import PlattCertificates.Count131072.C035628
import PlattCertificates.Count131072.C035629
import PlattCertificates.Count131072.C035630
import PlattCertificates.Count131072.C035631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000175
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts35600 : List PrefixCut := [⟨32,176052579,176052686⟩,
⟨64,354694329,354694543⟩]
theorem checked35600 : checkPrefixCuts (2^48) 4670095361 10 Manual.Count131072.C035600.packed 64 cuts35600 = true := by
 decide +kernel
def pointBounds35600 : List (Nat × Nat × Nat) := [(4670160896,107398151833217,107398536449278)]
theorem point_links_checked35600 : (cuts35600.take 1).map (fun c => (4670095361-1+2*2^10*c.k,107397975780638+c.lower,107398360396592+c.upper)) = pointBounds35600 := by
 decide +kernel
def cuts35601 : List PrefixCut := [⟨40,219200330,219200468⟩,
⟨64,350947712,350947930⟩]
theorem checked35601 : checkPrefixCuts (2^48) 4670226433 10 Manual.Count131072.C035601.packed 64 cuts35601 = true := by
 decide +kernel
def pointBounds35601 : List (Nat × Nat × Nat) := [(4670308352,107398549675297,107398934291603)]
theorem point_links_checked35601 : (cuts35601.take 1).map (fun c => (4670226433-1+2*2^10*c.k,107398330474967+c.lower,107398715091135+c.upper)) = pointBounds35601 := by
 decide +kernel
def cuts35602 : List PrefixCut := [⟨48,262767390,262767554⟩,
⟨64,350154397,350154614⟩]
theorem checked35602 : checkPrefixCuts (2^48) 4670357505 10 Manual.Count131072.C035602.packed 64 cuts35602 = true := by
 decide +kernel
def pointBounds35602 : List (Nat × Nat × Nat) := [(4670455808,107398944190069,107399328806619)]
theorem point_links_checked35602 : (cuts35602.take 1).map (fun c => (4670357505-1+2*2^10*c.k,107398681422679+c.lower,107399066039065+c.upper)) = pointBounds35602 := by
 decide +kernel
def cuts35603 : List PrefixCut := [⟨56,305849709,305849900⟩,
⟨64,352856490,352856709⟩]
theorem checked35603 : checkPrefixCuts (2^48) 4670488577 10 Manual.Count131072.C035603.packed 64 cuts35603 = true := by
 decide +kernel
def pointBounds35603 : List (Nat × Nat × Nat) := [(4670603264,107399337426785,107399722043579)]
theorem point_links_checked35603 : (cuts35603.take 1).map (fun c => (4670488577-1+2*2^10*c.k,107399031577076+c.lower,107399416193679+c.upper)) = pointBounds35603 := by
 decide +kernel
def cuts35604 : List PrefixCut := [⟨64,349471814,349472027⟩]
theorem checked35604 : checkPrefixCuts (2^48) 4670619649 10 Manual.Count131072.C035604.packed 64 cuts35604 = true := by
 decide +kernel
def pointBounds35604 : List (Nat × Nat × Nat) := [(4670750720,107399733905380,107400118522415)]
theorem point_links_checked35604 : (cuts35604.take 1).map (fun c => (4670619649-1+2*2^10*c.k,107399384433566+c.lower,107399769050388+c.upper)) = pointBounds35604 := by
 decide +kernel
def cuts35605 : List PrefixCut := [⟨64,360309289,360309505⟩]
theorem checked35605 : checkPrefixCuts (2^48) 4670750721 10 Manual.Count131072.C035605.packed 64 cuts35605 = true := by
 decide +kernel
def cuts35606 : List PrefixCut := [⟨8,44292212,44292239⟩,
⟨64,353489647,353489867⟩]
theorem checked35606 : checkPrefixCuts (2^48) 4670881793 10 Manual.Count131072.C035606.packed 64 cuts35606 = true := by
 decide +kernel
def pointBounds35606 : List (Nat × Nat × Nat) := [(4670898176,107400138506881,107400523124159)]
theorem point_links_checked35606 : (cuts35606.take 1).map (fun c => (4670881793-1+2*2^10*c.k,107400094214669+c.lower,107400478831920+c.upper)) = pointBounds35606 := by
 decide +kernel
def cuts35607 : List PrefixCut := [⟨16,93040999,93041057⟩,
⟨64,361494255,361494475⟩]
theorem checked35607 : checkPrefixCuts (2^48) 4671012865 10 Manual.Count131072.C035607.packed 64 cuts35607 = true := by
 decide +kernel
def pointBounds35607 : List (Nat × Nat × Nat) := [(4671045632,107400540745315,107400925362844)]
theorem point_links_checked35607 : (cuts35607.take 1).map (fun c => (4671012865-1+2*2^10*c.k,107400447704316+c.lower,107400832321787+c.upper)) = pointBounds35607 := by
 decide +kernel
def cuts35608 : List PrefixCut := [⟨24,132748201,132748281⟩,
⟨64,355759633,355759852⟩]
theorem checked35608 : checkPrefixCuts (2^48) 4671143937 10 Manual.Count131072.C035608.packed 64 cuts35608 = true := by
 decide +kernel
def pointBounds35608 : List (Nat × Nat × Nat) := [(4671193088,107400941946772,107401326564543)]
theorem point_links_checked35608 : (cuts35608.take 1).map (fun c => (4671143937-1+2*2^10*c.k,107400809198571+c.lower,107401193816262+c.upper)) = pointBounds35608 := by
 decide +kernel
def cuts35609 : List PrefixCut := [⟨32,177454262,177454373⟩,
⟨64,351170224,351170447⟩]
theorem checked35609 : checkPrefixCuts (2^48) 4671275009 10 Manual.Count131072.C035609.packed 64 cuts35609 = true := by
 decide +kernel
def pointBounds35609 : List (Nat × Nat × Nat) := [(4671340544,107401342412466,107401727030487)]
theorem point_links_checked35609 : (cuts35609.take 1).map (fun c => (4671275009-1+2*2^10*c.k,107401164958204+c.lower,107401549576114+c.upper)) = pointBounds35609 := by
 decide +kernel
def cuts35610 : List PrefixCut := [⟨40,226797249,226797390⟩,
⟨64,360077941,360078164⟩]
theorem checked35610 : checkPrefixCuts (2^48) 4671406081 10 Manual.Count131072.C035610.packed 64 cuts35610 = true := by
 decide +kernel
def pointBounds35610 : List (Nat × Nat × Nat) := [(4671488000,107401742925677,107402127543951)]
theorem point_links_checked35610 : (cuts35610.take 1).map (fun c => (4671406081-1+2*2^10*c.k,107401516128428+c.lower,107401900746561+c.upper)) = pointBounds35610 := by
 decide +kernel
def cuts35611 : List PrefixCut := [⟨48,267822474,267822642⟩,
⟨64,355187413,355187635⟩]
theorem checked35611 : checkPrefixCuts (2^48) 4671537153 10 Manual.Count131072.C035611.packed 64 cuts35611 = true := by
 decide +kernel
def pointBounds35611 : List (Nat × Nat × Nat) := [(4671635456,107402144028843,107402528647367)]
theorem point_links_checked35611 : (cuts35611.take 1).map (fun c => (4671537153-1+2*2^10*c.k,107401876206369+c.lower,107402260824725+c.upper)) = pointBounds35611 := by
 decide +kernel
def cuts35612 : List PrefixCut := [⟨56,314328074,314328267⟩,
⟨64,356502994,356503214⟩]
theorem checked35612 : checkPrefixCuts (2^48) 4671668225 10 Manual.Count131072.C035612.packed 64 cuts35612 = true := by
 decide +kernel
def pointBounds35612 : List (Nat × Nat × Nat) := [(4671782912,107402545721856,107402930340627)]
theorem point_links_checked35612 : (cuts35612.take 1).map (fun c => (4671668225-1+2*2^10*c.k,107402231393782+c.lower,107402616012360+c.upper)) = pointBounds35612 := by
 decide +kernel
def cuts35613 : List PrefixCut := [⟨64,354384260,354384482⟩]
theorem checked35613 : checkPrefixCuts (2^48) 4671799297 10 Manual.Count131072.C035613.packed 64 cuts35613 = true := by
 decide +kernel
def pointBounds35613 : List (Nat × Nat × Nat) := [(4671930368,107402942281036,107403326900056)]
theorem point_links_checked35613 : (cuts35613.take 1).map (fun c => (4671799297-1+2*2^10*c.k,107402587896776+c.lower,107402972515574+c.upper)) = pointBounds35613 := by
 decide +kernel
def cuts35614 : List PrefixCut := [⟨64,352205381,352205605⟩]
theorem checked35614 : checkPrefixCuts (2^48) 4671930369 10 Manual.Count131072.C035614.packed 64 cuts35614 = true := by
 decide +kernel
def cuts35615 : List PrefixCut := [⟨8,44160537,44160565⟩,
⟨64,350749607,350749834⟩]
theorem checked35615 : checkPrefixCuts (2^48) 4672061441 10 Manual.Count131072.C035615.packed 64 cuts35615 = true := by
 decide +kernel
def pointBounds35615 : List (Nat × Nat × Nat) := [(4672077824,107403338646954,107403723266226)]
theorem point_links_checked35615 : (cuts35615.take 1).map (fun c => (4672061441-1+2*2^10*c.k,107403294486417+c.lower,107403679105661+c.upper)) = pointBounds35615 := by
 decide +kernel
def cuts35616 : List PrefixCut := [⟨16,89101614,89101670⟩,
⟨64,358149790,358150009⟩]
theorem checked35616 : checkPrefixCuts (2^48) 4672192513 10 Manual.Count131072.C035616.packed 64 cuts35616 = true := by
 decide +kernel
def pointBounds35616 : List (Nat × Nat × Nat) := [(4672225280,107403734337638,107404118957165)]
theorem point_links_checked35616 : (cuts35616.take 1).map (fun c => (4672192513-1+2*2^10*c.k,107403645236024+c.lower,107404029855495+c.upper)) = pointBounds35616 := by
 decide +kernel
def cuts35617 : List PrefixCut := [⟨24,134521951,134522034⟩,
⟨64,358199974,358200195⟩]
theorem checked35617 : checkPrefixCuts (2^48) 4672323585 10 Manual.Count131072.C035617.packed 64 cuts35617 = true := by
 decide +kernel
def pointBounds35617 : List (Nat × Nat × Nat) := [(4672372736,107404137907765,107404522527538)]
theorem point_links_checked35617 : (cuts35617.take 1).map (fun c => (4672323585-1+2*2^10*c.k,107404003385814+c.lower,107404388005504+c.upper)) = pointBounds35617 := by
 decide +kernel
def cuts35618 : List PrefixCut := [⟨32,176987795,176987905⟩,
⟨64,352406865,352407084⟩]
theorem checked35618 : checkPrefixCuts (2^48) 4672454657 10 Manual.Count131072.C035618.packed 64 cuts35618 = true := by
 decide +kernel
def pointBounds35618 : List (Nat × Nat × Nat) := [(4672520192,107404538573583,107404923193604)]
theorem point_links_checked35618 : (cuts35618.take 1).map (fun c => (4672454657-1+2*2^10*c.k,107404361585788+c.lower,107404746205699+c.upper)) = pointBounds35618 := by
 decide +kernel
def cuts35619 : List PrefixCut := [⟨40,220776362,220776501⟩,
⟨64,356432954,356433171⟩]
theorem checked35619 : checkPrefixCuts (2^48) 4672585729 10 Manual.Count131072.C035619.packed 64 cuts35619 = true := by
 decide +kernel
def pointBounds35619 : List (Nat × Nat × Nat) := [(4672667648,107404934769015,107405319389284)]
theorem point_links_checked35619 : (cuts35619.take 1).map (fun c => (4672585729-1+2*2^10*c.k,107404713992653+c.lower,107405098612783+c.upper)) = pointBounds35619 := by
 decide +kernel
def cuts35620 : List PrefixCut := [⟨48,262152782,262152947⟩,
⟨64,350519683,350519904⟩]
theorem checked35620 : checkPrefixCuts (2^48) 4672716801 10 Manual.Count131072.C035620.packed 64 cuts35620 = true := by
 decide +kernel
def pointBounds35620 : List (Nat × Nat × Nat) := [(4672815104,107405332578389,107405717198901)]
theorem point_links_checked35620 : (cuts35620.take 1).map (fun c => (4672716801-1+2*2^10*c.k,107405070425607+c.lower,107405455045954+c.upper)) = pointBounds35620 := by
 decide +kernel
def cuts35621 : List PrefixCut := [⟨56,305755496,305755687⟩,
⟨64,351654320,351654538⟩]
theorem checked35621 : checkPrefixCuts (2^48) 4672847873 10 Manual.Count131072.C035621.packed 64 cuts35621 = true := by
 decide +kernel
def pointBounds35621 : List (Nat × Nat × Nat) := [(4672962560,107405726700786,107406111321545)]
theorem point_links_checked35621 : (cuts35621.take 1).map (fun c => (4672847873-1+2*2^10*c.k,107405420945290+c.lower,107405805565858+c.upper)) = pointBounds35621 := by
 decide +kernel
def cuts35622 : List PrefixCut := [⟨64,361824015,361824236⟩]
theorem checked35622 : checkPrefixCuts (2^48) 4672978945 10 Manual.Count131072.C035622.packed 64 cuts35622 = true := by
 decide +kernel
def pointBounds35622 : List (Nat × Nat × Nat) := [(4673110016,107406134423625,107406519044632)]
theorem point_links_checked35622 : (cuts35622.take 1).map (fun c => (4672978945-1+2*2^10*c.k,107405772599610+c.lower,107406157220396+c.upper)) = pointBounds35622 := by
 decide +kernel
def cuts35623 : List PrefixCut := [⟨64,358019173,358019393⟩]
theorem checked35623 : checkPrefixCuts (2^48) 4673110017 10 Manual.Count131072.C035623.packed 64 cuts35623 = true := by
 decide +kernel
def cuts35624 : List PrefixCut := [⟨8,43065230,43065258⟩,
⟨64,350299706,350299925⟩]
theorem checked35624 : checkPrefixCuts (2^48) 4673241089 10 Manual.Count131072.C035624.packed 64 cuts35624 = true := by
 decide +kernel
def pointBounds35624 : List (Nat × Nat × Nat) := [(4673257472,107406535508028,107406920129283)]
theorem point_links_checked35624 : (cuts35624.take 1).map (fun c => (4673241089-1+2*2^10*c.k,107406492442798+c.lower,107406877064025+c.upper)) = pointBounds35624 := by
 decide +kernel
def cuts35625 : List PrefixCut := [⟨16,93536096,93536153⟩,
⟨64,358541275,358541497⟩]
theorem checked35625 : checkPrefixCuts (2^48) 4673372161 10 Manual.Count131072.C035625.packed 64 cuts35625 = true := by
 decide +kernel
def pointBounds35625 : List (Nat × Nat × Nat) := [(4673404928,107406936278600,107407320900103)]
theorem point_links_checked35625 : (cuts35625.take 1).map (fun c => (4673372161-1+2*2^10*c.k,107406842742504+c.lower,107407227363950+c.upper)) = pointBounds35625 := by
 decide +kernel
def cuts35626 : List PrefixCut := [⟨24,134427773,134427856⟩,
⟨64,358350495,358350712⟩]
theorem checked35626 : checkPrefixCuts (2^48) 4673503233 10 Manual.Count131072.C035626.packed 64 cuts35626 = true := by
 decide +kernel
def pointBounds35626 : List (Nat × Nat × Nat) := [(4673552384,107407335711552,107407720333303)]
theorem point_links_checked35626 : (cuts35626.take 1).map (fun c => (4673503233-1+2*2^10*c.k,107407201283779+c.lower,107407585905447+c.upper)) = pointBounds35626 := by
 decide +kernel
def cuts35627 : List PrefixCut := [⟨32,177244247,177244357⟩,
⟨64,355329165,355329382⟩]
theorem checked35627 : checkPrefixCuts (2^48) 4673634305 10 Manual.Count131072.C035627.packed 64 cuts35627 = true := by
 decide +kernel
def pointBounds35627 : List (Nat × Nat × Nat) := [(4673699840,107407736878521,107408121500516)]
theorem point_links_checked35627 : (cuts35627.take 1).map (fun c => (4673634305-1+2*2^10*c.k,107407559634274+c.lower,107407944256159+c.upper)) = pointBounds35627 := by
 decide +kernel
def cuts35628 : List PrefixCut := [⟨40,223912474,223912612⟩,
⟨64,356885006,356885225⟩]
theorem checked35628 : checkPrefixCuts (2^48) 4673765377 10 Manual.Count131072.C035628.packed 64 cuts35628 = true := by
 decide +kernel
def pointBounds35628 : List (Nat × Nat × Nat) := [(4673847296,107408138875913,107408523498153)]
theorem point_links_checked35628 : (cuts35628.take 1).map (fun c => (4673765377-1+2*2^10*c.k,107407914963439+c.lower,107408299585541+c.upper)) = pointBounds35628 := by
 decide +kernel
def cuts35629 : List PrefixCut := [⟨48,266422619,266422783⟩,
⟨64,353382135,353382350⟩]
theorem checked35629 : checkPrefixCuts (2^48) 4673896449 10 Manual.Count131072.C035629.packed 64 cuts35629 = true := by
 decide +kernel
def pointBounds35629 : List (Nat × Nat × Nat) := [(4673994752,107408538271064,107408922893549)]
theorem point_links_checked35629 : (cuts35629.take 1).map (fun c => (4673896449-1+2*2^10*c.k,107408271848445+c.lower,107408656470766+c.upper)) = pointBounds35629 := by
 decide +kernel
def cuts35630 : List PrefixCut := [⟨56,313687657,313687857⟩,
⟨64,355961731,355961956⟩]
theorem checked35630 : checkPrefixCuts (2^48) 4674027521 10 Manual.Count131072.C035630.packed 64 cuts35630 = true := by
 decide +kernel
def pointBounds35630 : List (Nat × Nat × Nat) := [(4674142208,107408938918237,107409323540973)]
theorem point_links_checked35630 : (cuts35630.take 1).map (fun c => (4674027521-1+2*2^10*c.k,107408625230580+c.lower,107409009853116+c.upper)) = pointBounds35630 := by
 decide +kernel
def cuts35631 : List PrefixCut := [⟨64,355710857,355711072⟩]
theorem checked35631 : checkPrefixCuts (2^48) 4674158593 10 Manual.Count131072.C035631.packed 64 cuts35631 = true := by
 decide +kernel
def pointBounds35631 : List (Nat × Nat × Nat) := [(4674289664,107409336903168,107409721526144)]
theorem point_links_checked35631 : (cuts35631.take 1).map (fun c => (4674158593-1+2*2^10*c.k,107408981192311+c.lower,107409365815072+c.upper)) = pointBounds35631 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000175
