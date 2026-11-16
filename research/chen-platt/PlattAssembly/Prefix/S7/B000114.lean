import PlattAssemblyKernel
import PlattCertificates.Count131072.C063648
import PlattCertificates.Count131072.C063649
import PlattCertificates.Count131072.C063650
import PlattCertificates.Count131072.C063651
import PlattCertificates.Count131072.C063652
import PlattCertificates.Count131072.C063653
import PlattCertificates.Count131072.C063654
import PlattCertificates.Count131072.C063655
import PlattCertificates.Count131072.C063656
import PlattCertificates.Count131072.C063657
import PlattCertificates.Count131072.C063658
import PlattCertificates.Count131072.C063659
import PlattCertificates.Count131072.C063660
import PlattCertificates.Count131072.C063661
import PlattCertificates.Count131072.C063662
import PlattCertificates.Count131072.C063663
import PlattCertificates.Count131072.C063664
import PlattCertificates.Count131072.C063665
import PlattCertificates.Count131072.C063666
import PlattCertificates.Count131072.C063667
import PlattCertificates.Count131072.C063668
import PlattCertificates.Count131072.C063669
import PlattCertificates.Count131072.C063670
import PlattCertificates.Count131072.C063671
import PlattCertificates.Count131072.C063672
import PlattCertificates.Count131072.C063673
import PlattCertificates.Count131072.C063674
import PlattCertificates.Count131072.C063675
import PlattCertificates.Count131072.C063676
import PlattCertificates.Count131072.C063677
import PlattCertificates.Count131072.C063678
import PlattCertificates.Count131072.C063679
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000114
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63648 : List PrefixCut := [⟨48,142753262,142753349⟩,
⟨64,190843161,190843277⟩]
theorem checked63648 : checkPrefixCuts (2^48) 8346402817 10 Manual.Count131072.C063648.packed 64 cuts63648 = true := by
 decide +kernel
def pointBounds63648 : List (Nat × Nat × Nat) := [(8346501120,114644816727756,114645205552589)]
theorem point_links_checked63648 : (cuts63648.take 1).map (fun c => (8346402817-1+2*2^10*c.k,114644673974494+c.lower,114645062799240+c.upper)) = pointBounds63648 := by
 decide +kernel
def cuts63649 : List PrefixCut := [⟨64,194313677,194313792⟩]
theorem checked63649 : checkPrefixCuts (2^48) 8346533889 10 Manual.Count131072.C063649.packed 64 cuts63649 = true := by
 decide +kernel
def cuts63650 : List PrefixCut := [⟨48,144704692,144704780⟩,
⟨64,194546657,194546774⟩]
theorem checked63650 : checkPrefixCuts (2^48) 8346664961 10 Manual.Count131072.C063650.packed 64 cuts63650 = true := by
 decide +kernel
def pointBounds63650 : List (Nat × Nat × Nat) := [(8346763264,114645203836024,114645592661089)]
theorem point_links_checked63650 : (cuts63650.take 1).map (fun c => (8346664961-1+2*2^10*c.k,114645059131332+c.lower,114645447956309+c.upper)) = pointBounds63650 := by
 decide +kernel
def cuts63651 : List PrefixCut := [⟨64,192688915,192689021⟩]
theorem checked63651 : checkPrefixCuts (2^48) 8346796033 10 Manual.Count131072.C063651.packed 64 cuts63651 = true := by
 decide +kernel
def cuts63652 : List PrefixCut := [⟨48,145273427,145273509⟩,
⟨64,193798687,193798796⟩]
theorem checked63652 : checkPrefixCuts (2^48) 8346927105 10 Manual.Count131072.C063652.packed 64 cuts63652 = true := by
 decide +kernel
def pointBounds63652 : List (Nat × Nat × Nat) := [(8347025408,114645591640331,114645980465613)]
theorem point_links_checked63652 : (cuts63652.take 1).map (fun c => (8346927105-1+2*2^10*c.k,114645446366904+c.lower,114645835192104+c.upper)) = pointBounds63652 := by
 decide +kernel
def cuts63653 : List PrefixCut := [⟨64,194807277,194807391⟩]
theorem checked63653 : checkPrefixCuts (2^48) 8347058177 10 Manual.Count131072.C063653.packed 64 cuts63653 = true := by
 decide +kernel
def cuts63654 : List PrefixCut := [⟨48,147629321,147629405⟩,
⟨64,196523982,196524092⟩]
theorem checked63654 : checkPrefixCuts (2^48) 8347189249 10 Manual.Count131072.C063654.packed 64 cuts63654 = true := by
 decide +kernel
def pointBounds63654 : List (Nat × Nat × Nat) := [(8347287552,114645982602189,114646371427696)]
theorem point_links_checked63654 : (cuts63654.take 1).map (fun c => (8347189249-1+2*2^10*c.k,114645834972868+c.lower,114646223798291+c.upper)) = pointBounds63654 := by
 decide +kernel
def cuts63655 : List PrefixCut := [⟨64,192069836,192069948⟩]
theorem checked63655 : checkPrefixCuts (2^48) 8347320321 10 Manual.Count131072.C063655.packed 64 cuts63655 = true := by
 decide +kernel
def cuts63656 : List PrefixCut := [⟨48,144724792,144724874⟩,
⟨64,194831817,194831927⟩]
theorem checked63656 : checkPrefixCuts (2^48) 8347451393 10 Manual.Count131072.C063656.packed 64 cuts63656 = true := by
 decide +kernel
def pointBounds63656 : List (Nat × Nat × Nat) := [(8347549696,114646368291478,114646757117205)]
theorem point_links_checked63656 : (cuts63656.take 1).map (fun c => (8347451393-1+2*2^10*c.k,114646223566686+c.lower,114646612392331+c.upper)) = pointBounds63656 := by
 decide +kernel
def cuts63657 : List PrefixCut := [⟨64,195300828,195300938⟩]
theorem checked63657 : checkPrefixCuts (2^48) 8347582465 10 Manual.Count131072.C063657.packed 64 cuts63657 = true := by
 decide +kernel
def cuts63658 : List PrefixCut := [⟨48,142056473,142056555⟩,
⟨64,191622432,191622539⟩]
theorem checked63658 : checkPrefixCuts (2^48) 8347713537 10 Manual.Count131072.C063658.packed 64 cuts63658 = true := by
 decide +kernel
def pointBounds63658 : List (Nat × Nat × Nat) := [(8347811840,114646755755804,114647144581751)]
theorem point_links_checked63658 : (cuts63658.take 1).map (fun c => (8347713537-1+2*2^10*c.k,114646613699331+c.lower,114647002525196+c.upper)) = pointBounds63658 := by
 decide +kernel
def cuts63659 : List PrefixCut := [⟨64,195800472,195800584⟩]
theorem checked63659 : checkPrefixCuts (2^48) 8347844609 10 Manual.Count131072.C063659.packed 64 cuts63659 = true := by
 decide +kernel
def cuts63660 : List PrefixCut := [⟨48,147716562,147716639⟩,
⟨64,196674053,196674159⟩]
theorem checked63660 : checkPrefixCuts (2^48) 8347975681 10 Manual.Count131072.C063660.packed 64 cuts63660 = true := by
 decide +kernel
def pointBounds63660 : List (Nat × Nat × Nat) := [(8348073984,114647148838797,114647537664958)]
theorem point_links_checked63660 : (cuts63660.take 1).map (fun c => (8347975681-1+2*2^10*c.k,114647001122235+c.lower,114647389948319+c.upper)) = pointBounds63660 := by
 decide +kernel
def cuts63661 : List PrefixCut := [⟨64,191579685,191579798⟩]
theorem checked63661 : checkPrefixCuts (2^48) 8348106753 10 Manual.Count131072.C063661.packed 64 cuts63661 = true := by
 decide +kernel
def cuts63662 : List PrefixCut := [⟨48,146127239,146127326⟩,
⟨64,194240287,194240400⟩]
theorem checked63662 : checkPrefixCuts (2^48) 8348237825 10 Manual.Count131072.C063662.packed 64 cuts63662 = true := by
 decide +kernel
def pointBounds63662 : List (Nat × Nat × Nat) := [(8348336128,114647535503212,114647924329602)]
theorem point_links_checked63662 : (cuts63662.take 1).map (fun c => (8348237825-1+2*2^10*c.k,114647389375973+c.lower,114647778202276+c.upper)) = pointBounds63662 := by
 decide +kernel
def cuts63663 : List PrefixCut := [⟨64,196327624,196327733⟩]
theorem checked63663 : checkPrefixCuts (2^48) 8348368897 10 Manual.Count131072.C063663.packed 64 cuts63663 = true := by
 decide +kernel
def cuts63664 : List PrefixCut := [⟨48,144099729,144099810⟩,
⟨64,193492443,193492551⟩]
theorem checked63664 : checkPrefixCuts (2^48) 8348499969 10 Manual.Count131072.C063664.packed 64 cuts63664 = true := by
 decide +kernel
def pointBounds63664 : List (Nat × Nat × Nat) := [(8348598272,114647924043613,114648312870219)]
theorem point_links_checked63664 : (cuts63664.take 1).map (fun c => (8348499969-1+2*2^10*c.k,114647779943884+c.lower,114648168770409+c.upper)) = pointBounds63664 := by
 decide +kernel
def cuts63665 : List PrefixCut := [⟨64,190859670,190859780⟩]
theorem checked63665 : checkPrefixCuts (2^48) 8348631041 10 Manual.Count131072.C063665.packed 64 cuts63665 = true := by
 decide +kernel
def cuts63666 : List PrefixCut := [⟨48,143555785,143555865⟩,
⟨64,192205235,192205343⟩]
theorem checked63666 : checkPrefixCuts (2^48) 8348762113 10 Manual.Count131072.C063666.packed 64 cuts63666 = true := by
 decide +kernel
def pointBounds63666 : List (Nat × Nat × Nat) := [(8348860416,114648307851782,114648696678605)]
theorem point_links_checked63666 : (cuts63666.take 1).map (fun c => (8348762113-1+2*2^10*c.k,114648164295997+c.lower,114648553122740+c.upper)) = pointBounds63666 := by
 decide +kernel
def cuts63667 : List PrefixCut := [⟨64,194494757,194494873⟩]
theorem checked63667 : checkPrefixCuts (2^48) 8348893185 10 Manual.Count131072.C063667.packed 64 cuts63667 = true := by
 decide +kernel
def cuts63668 : List PrefixCut := [⟨48,144663815,144663901⟩,
⟨64,192603764,192603878⟩]
theorem checked63668 : checkPrefixCuts (2^48) 8349024257 10 Manual.Count131072.C063668.packed 64 cuts63668 = true := by
 decide +kernel
def pointBounds63668 : List (Nat × Nat × Nat) := [(8349122560,114648695659804,114649084486857)]
theorem point_links_checked63668 : (cuts63668.take 1).map (fun c => (8349024257-1+2*2^10*c.k,114648550995989+c.lower,114648939822956+c.upper)) = pointBounds63668 := by
 decide +kernel
def cuts63669 : List PrefixCut := [⟨64,192533325,192533438⟩]
theorem checked63669 : checkPrefixCuts (2^48) 8349155329 10 Manual.Count131072.C063669.packed 64 cuts63669 = true := by
 decide +kernel
def cuts63670 : List PrefixCut := [⟨48,144996389,144996479⟩,
⟨64,192462867,192462985⟩]
theorem checked63670 : checkPrefixCuts (2^48) 8349286401 10 Manual.Count131072.C063670.packed 64 cuts63670 = true := by
 decide +kernel
def pointBounds63670 : List (Nat × Nat × Nat) := [(8349384704,114649081129467,114649469956751)]
theorem point_links_checked63670 : (cuts63670.take 1).map (fun c => (8349286401-1+2*2^10*c.k,114648936133078+c.lower,114649324960272+c.upper)) = pointBounds63670 := by
 decide +kernel
def cuts63671 : List PrefixCut := [⟨64,192426135,192426246⟩]
theorem checked63671 : checkPrefixCuts (2^48) 8349417473 10 Manual.Count131072.C063671.packed 64 cuts63671 = true := by
 decide +kernel
def cuts63672 : List PrefixCut := [⟨48,145194101,145194183⟩,
⟨64,192996197,192996305⟩]
theorem checked63672 : checkPrefixCuts (2^48) 8349548545 10 Manual.Count131072.C063672.packed 64 cuts63672 = true := by
 decide +kernel
def pointBounds63672 : List (Nat × Nat × Nat) := [(8349646848,114649466216181,114649855043686)]
theorem point_links_checked63672 : (cuts63672.take 1).map (fun c => (8349548545-1+2*2^10*c.k,114649321022080+c.lower,114649709849503+c.upper)) = pointBounds63672 := by
 decide +kernel
def cuts63673 : List PrefixCut := [⟨64,193599958,193600067⟩]
theorem checked63673 : checkPrefixCuts (2^48) 8349679617 10 Manual.Count131072.C063673.packed 64 cuts63673 = true := by
 decide +kernel
def cuts63674 : List PrefixCut := [⟨48,145088416,145088502⟩,
⟨64,194911604,194911716⟩]
theorem checked63674 : checkPrefixCuts (2^48) 8349810689 10 Manual.Count131072.C063674.packed 64 cuts63674 = true := by
 decide +kernel
def pointBounds63674 : List (Nat × Nat × Nat) := [(8349908992,114649852706651,114650241534377)]
theorem point_links_checked63674 : (cuts63674.take 1).map (fun c => (8349810689-1+2*2^10*c.k,114649707618235+c.lower,114650096445875+c.upper)) = pointBounds63674 := by
 decide +kernel
def cuts63675 : List PrefixCut := [⟨64,190998243,190998356⟩]
theorem checked63675 : checkPrefixCuts (2^48) 8349941761 10 Manual.Count131072.C063675.packed 64 cuts63675 = true := by
 decide +kernel
def cuts63676 : List PrefixCut := [⟨48,143971463,143971543⟩,
⟨64,192444734,192444840⟩]
theorem checked63676 : checkPrefixCuts (2^48) 8350072833 10 Manual.Count131072.C063676.packed 64 cuts63676 = true := by
 decide +kernel
def pointBounds63676 : List (Nat × Nat × Nat) := [(8350171136,114650237499545,114650626327490)]
theorem point_links_checked63676 : (cuts63676.take 1).map (fun c => (8350072833-1+2*2^10*c.k,114650093528082+c.lower,114650482355947+c.upper)) = pointBounds63676 := by
 decide +kernel
def cuts63677 : List PrefixCut := [⟨64,195778849,195778962⟩]
theorem checked63677 : checkPrefixCuts (2^48) 8350203905 10 Manual.Count131072.C063677.packed 64 cuts63677 = true := by
 decide +kernel
def cuts63678 : List PrefixCut := [⟨48,142618609,142618696⟩,
⟨64,190382494,190382609⟩]
theorem checked63678 : checkPrefixCuts (2^48) 8350334977 10 Manual.Count131072.C063678.packed 64 cuts63678 = true := by
 decide +kernel
def pointBounds63678 : List (Nat × Nat × Nat) := [(8350433280,114650624370274,114651013198445)]
theorem point_links_checked63678 : (cuts63678.take 1).map (fun c => (8350334977-1+2*2^10*c.k,114650481751665+c.lower,114650870579749+c.upper)) = pointBounds63678 := by
 decide +kernel
def cuts63679 : List PrefixCut := [⟨64,192132310,192132423⟩]
theorem checked63679 : checkPrefixCuts (2^48) 8350466049 10 Manual.Count131072.C063679.packed 64 cuts63679 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000114
