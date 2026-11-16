import PlattAssemblyKernel
import PlattCertificates.Count131072.C036624
import PlattCertificates.Count131072.C036625
import PlattCertificates.Count131072.C036626
import PlattCertificates.Count131072.C036627
import PlattCertificates.Count131072.C036628
import PlattCertificates.Count131072.C036629
import PlattCertificates.Count131072.C036630
import PlattCertificates.Count131072.C036631
import PlattCertificates.Count131072.C036632
import PlattCertificates.Count131072.C036633
import PlattCertificates.Count131072.C036634
import PlattCertificates.Count131072.C036635
import PlattCertificates.Count131072.C036636
import PlattCertificates.Count131072.C036637
import PlattCertificates.Count131072.C036638
import PlattCertificates.Count131072.C036639
import PlattCertificates.Count131072.C036640
import PlattCertificates.Count131072.C036641
import PlattCertificates.Count131072.C036642
import PlattCertificates.Count131072.C036643
import PlattCertificates.Count131072.C036644
import PlattCertificates.Count131072.C036645
import PlattCertificates.Count131072.C036646
import PlattCertificates.Count131072.C036647
import PlattCertificates.Count131072.C036648
import PlattCertificates.Count131072.C036649
import PlattCertificates.Count131072.C036650
import PlattCertificates.Count131072.C036651
import PlattCertificates.Count131072.C036652
import PlattCertificates.Count131072.C036653
import PlattCertificates.Count131072.C036654
import PlattCertificates.Count131072.C036655
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000207
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts36624 : List PrefixCut := [⟨64,344140943,344141155⟩]
theorem checked36624 : checkPrefixCuts (2^48) 4804313089 10 Manual.Count131072.C036624.packed 64 cuts36624 = true := by
 decide +kernel
def cuts36625 : List PrefixCut := [⟨9,49505376,49505408⟩,
⟨64,348818437,348818652⟩]
theorem checked36625 : checkPrefixCuts (2^48) 4804444161 10 Manual.Count131072.C036625.packed 64 cuts36625 = true := by
 decide +kernel
def pointBounds36625 : List (Nat × Nat × Nat) := [(4804462592,107756396452248,107756781288841)]
theorem point_links_checked36625 : (cuts36625.take 1).map (fun c => (4804444161-1+2*2^10*c.k,107756346946872+c.lower,107756731783433+c.upper)) = pointBounds36625 := by
 decide +kernel
def cuts36626 : List PrefixCut := [⟨19,104573378,104573442⟩,
⟨64,346172665,346172877⟩]
theorem checked36626 : checkPrefixCuts (2^48) 4804575233 10 Manual.Count131072.C036626.packed 64 cuts36626 = true := by
 decide +kernel
def pointBounds36626 : List (Nat × Nat × Nat) := [(4804614144,107756800338687,107757185175527)]
theorem point_links_checked36626 : (cuts36626.take 1).map (fun c => (4804575233-1+2*2^10*c.k,107756695765309+c.lower,107757080602085+c.upper)) = pointBounds36626 := by
 decide +kernel
def cuts36627 : List PrefixCut := [⟨29,155947424,155947518⟩,
⟨64,343351247,343351457⟩]
theorem checked36627 : checkPrefixCuts (2^48) 4804706305 10 Manual.Count131072.C036627.packed 64 cuts36627 = true := by
 decide +kernel
def pointBounds36627 : List (Nat × Nat × Nat) := [(4804765696,107757197885398,107757582722480)]
theorem point_links_checked36627 : (cuts36627.take 1).map (fun c => (4804706305-1+2*2^10*c.k,107757041937974+c.lower,107757426774962+c.upper)) = pointBounds36627 := by
 decide +kernel
def cuts36628 : List PrefixCut := [⟨39,212356422,212356551⟩,
⟨64,348614137,348614350⟩]
theorem checked36628 : checkPrefixCuts (2^48) 4804837377 10 Manual.Count131072.C036628.packed 64 cuts36628 = true := by
 decide +kernel
def pointBounds36628 : List (Nat × Nat × Nat) := [(4804917248,107757597645643,107757982482970)]
theorem point_links_checked36628 : (cuts36628.take 1).map (fun c => (4804837377-1+2*2^10*c.k,107757385289221+c.lower,107757770126419+c.upper)) = pointBounds36628 := by
 decide +kernel
def cuts36629 : List PrefixCut := [⟨49,260326617,260326781⟩,
⟨64,340169185,340169397⟩]
theorem checked36629 : checkPrefixCuts (2^48) 4804968449 10 Manual.Count131072.C036629.packed 64 cuts36629 = true := by
 decide +kernel
def pointBounds36629 : List (Nat × Nat × Nat) := [(4805068800,107757994229975,107758379067550)]
theorem point_links_checked36629 : (cuts36629.take 1).map (fun c => (4804968449-1+2*2^10*c.k,107757733903358+c.lower,107758118740769+c.upper)) = pointBounds36629 := by
 decide +kernel
def cuts36630 : List PrefixCut := [⟨59,314210439,314210632⟩,
⟨64,341155782,341155992⟩]
theorem checked36630 : checkPrefixCuts (2^48) 4805099521 10 Manual.Count131072.C036630.packed 64 cuts36630 = true := by
 decide +kernel
def pointBounds36630 : List (Nat × Nat × Nat) := [(4805220352,107758388282982,107758773120798)]
theorem point_links_checked36630 : (cuts36630.take 1).map (fun c => (4805099521-1+2*2^10*c.k,107758074072543+c.lower,107758458910166+c.upper)) = pointBounds36630 := by
 decide +kernel
def cuts36631 : List PrefixCut := [⟨64,343723774,343723982⟩]
theorem checked36631 : checkPrefixCuts (2^48) 4805230593 10 Manual.Count131072.C036631.packed 64 cuts36631 = true := by
 decide +kernel
def cuts36632 : List PrefixCut := [⟨5,26944551,26944567⟩,
⟨64,343304415,343304631⟩]
theorem checked36632 : checkPrefixCuts (2^48) 4805361665 10 Manual.Count131072.C036632.packed 64 cuts36632 = true := by
 decide +kernel
def pointBounds36632 : List (Nat × Nat × Nat) := [(4805371904,107758785896650,107759170734707)]
theorem point_links_checked36632 : (cuts36632.take 1).map (fun c => (4805361665-1+2*2^10*c.k,107758758952099+c.lower,107759143790140+c.upper)) = pointBounds36632 := by
 decide +kernel
def cuts36633 : List PrefixCut := [⟨15,81299861,81299911⟩,
⟨64,341772179,341772392⟩]
theorem checked36633 : checkPrefixCuts (2^48) 4805492737 10 Manual.Count131072.C036633.packed 64 cuts36633 = true := by
 decide +kernel
def pointBounds36633 : List (Nat × Nat × Nat) := [(4805523456,107759183556375,107759568394682)]
theorem point_links_checked36633 : (cuts36633.take 1).map (fun c => (4805492737-1+2*2^10*c.k,107759102256514+c.lower,107759487094771+c.upper)) = pointBounds36633 := by
 decide +kernel
def cuts36634 : List PrefixCut := [⟨25,138229137,138229220⟩,
⟨64,346214310,346214522⟩]
theorem checked36634 : checkPrefixCuts (2^48) 4805623809 10 Manual.Count131072.C036634.packed 64 cuts36634 = true := by
 decide +kernel
def pointBounds36634 : List (Nat × Nat × Nat) := [(4805675008,107759582257830,107759967096383)]
theorem point_links_checked36634 : (cuts36634.take 1).map (fun c => (4805623809-1+2*2^10*c.k,107759444028693+c.lower,107759828867163+c.upper)) = pointBounds36634 := by
 decide +kernel
def cuts36635 : List PrefixCut := [⟨35,185900994,185901104⟩,
⟨64,339527859,339528062⟩]
theorem checked36635 : checkPrefixCuts (2^48) 4805754881 10 Manual.Count131072.C036635.packed 64 cuts36635 = true := by
 decide +kernel
def pointBounds36635 : List (Nat × Nat × Nat) := [(4805826560,107759976143997,107760360982789)]
theorem point_links_checked36635 : (cuts36635.take 1).map (fun c => (4805754881-1+2*2^10*c.k,107759790243003+c.lower,107760175081685+c.upper)) = pointBounds36635 := by
 decide +kernel
def cuts36636 : List PrefixCut := [⟨45,242589576,242589720⟩,
⟨64,344321188,344321394⟩]
theorem checked36636 : checkPrefixCuts (2^48) 4805885953 10 Manual.Count131072.C036636.packed 64 cuts36636 = true := by
 decide +kernel
def pointBounds36636 : List (Nat × Nat × Nat) := [(4805978112,107760372360438,107760757199467)]
theorem point_links_checked36636 : (cuts36636.take 1).map (fun c => (4805885953-1+2*2^10*c.k,107760129770862+c.lower,107760514609747+c.upper)) = pointBounds36636 := by
 decide +kernel
def cuts36637 : List PrefixCut := [⟨55,292832532,292832710⟩,
⟨64,341383497,341383706⟩]
theorem checked36637 : checkPrefixCuts (2^48) 4806017025 10 Manual.Count131072.C036637.packed 64 cuts36637 = true := by
 decide +kernel
def pointBounds36637 : List (Nat × Nat × Nat) := [(4806129664,107760766924582,107761151763851)]
theorem point_links_checked36637 : (cuts36637.take 1).map (fun c => (4806017025-1+2*2^10*c.k,107760474092050+c.lower,107760858931141+c.upper)) = pointBounds36637 := by
 decide +kernel
def cuts36638 : List PrefixCut := [⟨64,345707925,345708133⟩]
theorem checked36638 : checkPrefixCuts (2^48) 4806148097 10 Manual.Count131072.C036638.packed 64 cuts36638 = true := by
 decide +kernel
def cuts36639 : List PrefixCut := [⟨1,4977938,4977941⟩,
⟨64,337265418,337265631⟩]
theorem checked36639 : checkPrefixCuts (2^48) 4806279169 10 Manual.Count131072.C036639.packed 64 cuts36639 = true := by
 decide +kernel
def pointBounds36639 : List (Nat × Nat × Nat) := [(4806281216,107761166161410,107761551000921)]
theorem point_links_checked36639 : (cuts36639.take 1).map (fun c => (4806279169-1+2*2^10*c.k,107761161183472+c.lower,107761546022980+c.upper)) = pointBounds36639 := by
 decide +kernel
def cuts36640 : List PrefixCut := [⟨11,61197559,61197598⟩,
⟨64,346860358,346860568⟩]
theorem checked36640 : checkPrefixCuts (2^48) 4806410241 10 Manual.Count131072.C036640.packed 64 cuts36640 = true := by
 decide +kernel
def pointBounds36640 : List (Nat × Nat × Nat) := [(4806432768,107761559646449,107761944486209)]
theorem point_links_checked36640 : (cuts36640.take 1).map (fun c => (4806410241-1+2*2^10*c.k,107761498448890+c.lower,107761883288611+c.upper)) = pointBounds36640 := by
 decide +kernel
def cuts36641 : List PrefixCut := [⟨21,112201984,112202052⟩,
⟨64,347787822,347788042⟩]
theorem checked36641 : checkPrefixCuts (2^48) 4806541313 10 Manual.Count131072.C036641.packed 64 cuts36641 = true := by
 decide +kernel
def pointBounds36641 : List (Nat × Nat × Nat) := [(4806584320,107761957511232,107762342351231)]
theorem point_links_checked36641 : (cuts36641.take 1).map (fun c => (4806541313-1+2*2^10*c.k,107761845309248+c.lower,107762230149179+c.upper)) = pointBounds36641 := by
 decide +kernel
def cuts36642 : List PrefixCut := [⟨31,169937660,169937767⟩,
⟨64,346490068,346490285⟩]
theorem checked36642 : checkPrefixCuts (2^48) 4806672385 10 Manual.Count131072.C036642.packed 64 cuts36642 = true := by
 decide +kernel
def pointBounds36642 : List (Nat × Nat × Nat) := [(4806735872,107762363034730,107762747874988)]
theorem point_links_checked36642 : (cuts36642.take 1).map (fun c => (4806672385-1+2*2^10*c.k,107762193097070+c.lower,107762577937221+c.upper)) = pointBounds36642 := by
 decide +kernel
def cuts36643 : List PrefixCut := [⟨41,219003533,219003663⟩,
⟨64,341034840,341035046⟩]
theorem checked36643 : checkPrefixCuts (2^48) 4806803457 10 Manual.Count131072.C036643.packed 64 cuts36643 = true := by
 decide +kernel
def pointBounds36643 : List (Nat × Nat × Nat) := [(4806887424,107762758590671,107763143431169)]
theorem point_links_checked36643 : (cuts36643.take 1).map (fun c => (4806803457-1+2*2^10*c.k,107762539587138+c.lower,107762924427506+c.upper)) = pointBounds36643 := by
 decide +kernel
def cuts36644 : List PrefixCut := [⟨51,276264244,276264414⟩,
⟨64,346471178,346471388⟩]
theorem checked36644 : checkPrefixCuts (2^48) 4806934529 10 Manual.Count131072.C036644.packed 64 cuts36644 = true := by
 decide +kernel
def pointBounds36644 : List (Nat × Nat × Nat) := [(4807038976,107763156886222,107763541726966)]
theorem point_links_checked36644 : (cuts36644.take 1).map (fun c => (4806934529-1+2*2^10*c.k,107762880621978+c.lower,107763265462552+c.upper)) = pointBounds36644 := by
 decide +kernel
def cuts36645 : List PrefixCut := [⟨61,325206988,325207185⟩,
⟨64,341601786,341601994⟩]
theorem checked36645 : checkPrefixCuts (2^48) 4807065601 10 Manual.Count131072.C036645.packed 64 cuts36645 = true := by
 decide +kernel
def pointBounds36645 : List (Nat × Nat × Nat) := [(4807190528,107763552300144,107763937141125)]
theorem point_links_checked36645 : (cuts36645.take 1).map (fun c => (4807065601-1+2*2^10*c.k,107763227093156+c.lower,107763611933940+c.upper)) = pointBounds36645 := by
 decide +kernel
def cuts36646 : List PrefixCut := [⟨64,341065488,341065694⟩]
theorem checked36646 : checkPrefixCuts (2^48) 4807196673 10 Manual.Count131072.C036646.packed 64 cuts36646 = true := by
 decide +kernel
def cuts36647 : List PrefixCut := [⟨7,38643747,38643771⟩,
⟨64,339416777,339416988⟩]
theorem checked36647 : checkPrefixCuts (2^48) 4807327745 10 Manual.Count131072.C036647.packed 64 cuts36647 = true := by
 decide +kernel
def pointBounds36647 : List (Nat × Nat × Nat) := [(4807342080,107763948404177,107764333245399)]
theorem point_links_checked36647 : (cuts36647.take 1).map (fun c => (4807327745-1+2*2^10*c.k,107763909760430+c.lower,107764294601628+c.upper)) = pointBounds36647 := by
 decide +kernel
def cuts36648 : List PrefixCut := [⟨17,93737606,93737666⟩,
⟨64,342861950,342862168⟩]
theorem checked36648 : checkPrefixCuts (2^48) 4807458817 10 Manual.Count131072.C036648.packed 64 cuts36648 = true := by
 decide +kernel
def pointBounds36648 : List (Nat × Nat × Nat) := [(4807493632,107764342914813,107764727756282)]
theorem point_links_checked36648 : (cuts36648.take 1).map (fun c => (4807458817-1+2*2^10*c.k,107764249177207+c.lower,107764634018616+c.upper)) = pointBounds36648 := by
 decide +kernel
def cuts36649 : List PrefixCut := [⟨27,144671351,144671441⟩,
⟨64,344491877,344492093⟩]
theorem checked36649 : checkPrefixCuts (2^48) 4807589889 10 Manual.Count131072.C036649.packed 64 cuts36649 = true := by
 decide +kernel
def pointBounds36649 : List (Nat × Nat × Nat) := [(4807645184,107764736710508,107765121552225)]
theorem point_links_checked36649 : (cuts36649.take 1).map (fun c => (4807589889-1+2*2^10*c.k,107764592039157+c.lower,107764976880784+c.upper)) = pointBounds36649 := by
 decide +kernel
def cuts36650 : List PrefixCut := [⟨37,199993022,199993143⟩,
⟨64,342433415,342433623⟩]
theorem checked36650 : checkPrefixCuts (2^48) 4807720961 10 Manual.Count131072.C036650.packed 64 cuts36650 = true := by
 decide +kernel
def pointBounds36650 : List (Nat × Nat × Nat) := [(4807796736,107765136524056,107765521366020)]
theorem point_links_checked36650 : (cuts36650.take 1).map (fun c => (4807720961-1+2*2^10*c.k,107764936531034+c.lower,107765321372877+c.upper)) = pointBounds36650 := by
 decide +kernel
def cuts36651 : List PrefixCut := [⟨47,255252932,255253084⟩,
⟨64,344941493,344941698⟩]
theorem checked36651 : checkPrefixCuts (2^48) 4807852033 10 Manual.Count131072.C036651.packed 64 cuts36651 = true := by
 decide +kernel
def pointBounds36651 : List (Nat × Nat × Nat) := [(4807948288,107765534217381,107765919059584)]
theorem point_links_checked36651 : (cuts36651.take 1).map (fun c => (4807852033-1+2*2^10*c.k,107765278964449+c.lower,107765663806500+c.upper)) = pointBounds36651 := by
 decide +kernel
def cuts36652 : List PrefixCut := [⟨57,309631436,309631626⟩,
⟨64,346278558,346278770⟩]
theorem checked36652 : checkPrefixCuts (2^48) 4807983105 10 Manual.Count131072.C036652.packed 64 cuts36652 = true := by
 decide +kernel
def pointBounds36652 : List (Nat × Nat × Nat) := [(4808099840,107765933537378,107766318379824)]
theorem point_links_checked36652 : (cuts36652.take 1).map (fun c => (4807983105-1+2*2^10*c.k,107765623905942+c.lower,107766008748198+c.upper)) = pointBounds36652 := by
 decide +kernel
def cuts36653 : List PrefixCut := [⟨64,343810358,343810566⟩]
theorem checked36653 : checkPrefixCuts (2^48) 4808114177 10 Manual.Count131072.C036653.packed 64 cuts36653 = true := by
 decide +kernel
def cuts36654 : List PrefixCut := [⟨3,16566822,16566832⟩,
⟨64,350708659,350708872⟩]
theorem checked36654 : checkPrefixCuts (2^48) 4808245249 10 Manual.Count131072.C036654.packed 64 cuts36654 = true := by
 decide +kernel
def pointBounds36654 : List (Nat × Nat × Nat) := [(4808251392,107766330561680,107766715404366)]
theorem point_links_checked36654 : (cuts36654.take 1).map (fun c => (4808245249-1+2*2^10*c.k,107766313994858+c.lower,107766698837534+c.upper)) = pointBounds36654 := by
 decide +kernel
def cuts36655 : List PrefixCut := [⟨13,70363016,70363059⟩,
⟨64,342094080,342094293⟩]
theorem checked36655 : checkPrefixCuts (2^48) 4808376321 10 Manual.Count131072.C036655.packed 64 cuts36655 = true := by
 decide +kernel
def pointBounds36655 : List (Nat × Nat × Nat) := [(4808402944,107766735066533,107767119909465)]
theorem point_links_checked36655 : (cuts36655.take 1).map (fun c => (4808376321-1+2*2^10*c.k,107766664703517+c.lower,107767049546406+c.upper)) = pointBounds36655 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000207
