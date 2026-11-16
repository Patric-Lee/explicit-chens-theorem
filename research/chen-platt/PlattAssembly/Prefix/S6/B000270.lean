import PlattAssemblyKernel
import PlattCertificates.Count131072.C058640
import PlattCertificates.Count131072.C058641
import PlattCertificates.Count131072.C058642
import PlattCertificates.Count131072.C058643
import PlattCertificates.Count131072.C058644
import PlattCertificates.Count131072.C058645
import PlattCertificates.Count131072.C058646
import PlattCertificates.Count131072.C058647
import PlattCertificates.Count131072.C058648
import PlattCertificates.Count131072.C058649
import PlattCertificates.Count131072.C058650
import PlattCertificates.Count131072.C058651
import PlattCertificates.Count131072.C058652
import PlattCertificates.Count131072.C058653
import PlattCertificates.Count131072.C058654
import PlattCertificates.Count131072.C058655
import PlattCertificates.Count131072.C058656
import PlattCertificates.Count131072.C058657
import PlattCertificates.Count131072.C058658
import PlattCertificates.Count131072.C058659
import PlattCertificates.Count131072.C058660
import PlattCertificates.Count131072.C058661
import PlattCertificates.Count131072.C058662
import PlattCertificates.Count131072.C058663
import PlattCertificates.Count131072.C058664
import PlattCertificates.Count131072.C058665
import PlattCertificates.Count131072.C058666
import PlattCertificates.Count131072.C058667
import PlattCertificates.Count131072.C058668
import PlattCertificates.Count131072.C058669
import PlattCertificates.Count131072.C058670
import PlattCertificates.Count131072.C058671
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000270
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts58640 : List PrefixCut := [⟨64,211598658,211598779⟩]
theorem checked58640 : checkPrefixCuts (2^48) 7689994241 10 Manual.Count131072.C058640.packed 64 cuts58640 = true := by
 decide +kernel
def cuts58641 : List PrefixCut := [⟨42,141905621,141905699⟩,
⟨64,212363709,212363827⟩]
theorem checked58641 : checkPrefixCuts (2^48) 7690125313 10 Manual.Count131072.C058641.packed 64 cuts58641 = true := by
 decide +kernel
def pointBounds58641 : List (Nat × Nat × Nat) := [(7690211328,113633910691927,113634298937726)]
theorem point_links_checked58641 : (cuts58641.take 1).map (fun c => (7690125313-1+2*2^10*c.k,113633768786306+c.lower,113634157032027+c.upper)) = pointBounds58641 := by
 decide +kernel
def cuts58642 : List PrefixCut := [⟨64,209431999,209432121⟩]
theorem checked58642 : checkPrefixCuts (2^48) 7690256385 10 Manual.Count131072.C058642.packed 64 cuts58642 = true := by
 decide +kernel
def cuts58643 : List PrefixCut := [⟨32,106581287,106581346⟩,
⟨64,209757828,209757946⟩]
theorem checked58643 : checkPrefixCuts (2^48) 7690387457 10 Manual.Count131072.C058643.packed 64 cuts58643 = true := by
 decide +kernel
def pointBounds58643 : List (Nat × Nat × Nat) := [(7690452992,113634297163301,113634685409321)]
theorem point_links_checked58643 : (cuts58643.take 1).map (fun c => (7690387457-1+2*2^10*c.k,113634190582014+c.lower,113634578827975+c.upper)) = pointBounds58643 := by
 decide +kernel
def cuts58644 : List PrefixCut := [⟨64,211840441,211840564⟩]
theorem checked58644 : checkPrefixCuts (2^48) 7690518529 10 Manual.Count131072.C058644.packed 64 cuts58644 = true := by
 decide +kernel
def cuts58645 : List PrefixCut := [⟨22,70710268,70710307⟩,
⟨64,212715189,212715305⟩]
theorem checked58645 : checkPrefixCuts (2^48) 7690649601 10 Manual.Count131072.C058645.packed 64 cuts58645 = true := by
 decide +kernel
def pointBounds58645 : List (Nat × Nat × Nat) := [(7690694656,113634682890551,113635071136792)]
theorem point_links_checked58645 : (cuts58645.take 1).map (fun c => (7690649601-1+2*2^10*c.k,113634612180283+c.lower,113635000426485+c.upper)) = pointBounds58645 := by
 decide +kernel
def cuts58646 : List PrefixCut := [⟨64,210186275,210186394⟩]
theorem checked58646 : checkPrefixCuts (2^48) 7690780673 10 Manual.Count131072.C058646.packed 64 cuts58646 = true := by
 decide +kernel
def cuts58647 : List PrefixCut := [⟨12,40001964,40001988⟩,
⟨64,212012601,212012725⟩]
theorem checked58647 : checkPrefixCuts (2^48) 7690911745 10 Manual.Count131072.C058647.packed 64 cuts58647 = true := by
 decide +kernel
def pointBounds58647 : List (Nat × Nat × Nat) := [(7690936320,113635075083711,113635463330172)]
theorem point_links_checked58647 : (cuts58647.take 1).map (fun c => (7690911745-1+2*2^10*c.k,113635035081747+c.lower,113635423328184+c.upper)) = pointBounds58647 := by
 decide +kernel
def cuts58648 : List PrefixCut := [⟨64,212338372,212338494⟩]
theorem checked58648 : checkPrefixCuts (2^48) 7691042817 10 Manual.Count131072.C058648.packed 64 cuts58648 = true := by
 decide +kernel
def cuts58649 : List PrefixCut := [⟨2,6514287,6514291⟩,
⟨64,210065727,210065844⟩]
theorem checked58649 : checkPrefixCuts (2^48) 7691173889 10 Manual.Count131072.C058649.packed 64 cuts58649 = true := by
 decide +kernel
def pointBounds58649 : List (Nat × Nat × Nat) := [(7691177984,113635465947007,113635854193694)]
theorem point_links_checked58649 : (cuts58649.take 1).map (fun c => (7691173889-1+2*2^10*c.k,113635459432720+c.lower,113635847679403+c.upper)) = pointBounds58649 := by
 decide +kernel
def cuts58650 : List PrefixCut := [⟨56,184408430,184408532⟩,
⟨64,210647707,210647823⟩]
theorem checked58650 : checkPrefixCuts (2^48) 7691304961 10 Manual.Count131072.C058650.packed 64 cuts58650 = true := by
 decide +kernel
def pointBounds58650 : List (Nat × Nat × Nat) := [(7691419648,113635853906877,113636242153779)]
theorem point_links_checked58650 : (cuts58650.take 1).map (fun c => (7691304961-1+2*2^10*c.k,113635669498447+c.lower,113636057745247+c.upper)) = pointBounds58650 := by
 decide +kernel
def cuts58651 : List PrefixCut := [⟨64,208924108,208924231⟩]
theorem checked58651 : checkPrefixCuts (2^48) 7691436033 10 Manual.Count131072.C058651.packed 64 cuts58651 = true := by
 decide +kernel
def cuts58652 : List PrefixCut := [⟨46,152601293,152601380⟩,
⟨64,211555393,211555514⟩]
theorem checked58652 : checkPrefixCuts (2^48) 7691567105 10 Manual.Count131072.C058652.packed 64 cuts58652 = true := by
 decide +kernel
def pointBounds58652 : List (Nat × Nat × Nat) := [(7691661312,113636241671555,113636629918681)]
theorem point_links_checked58652 : (cuts58652.take 1).map (fun c => (7691567105-1+2*2^10*c.k,113636089070262+c.lower,113636477317301+c.upper)) = pointBounds58652 := by
 decide +kernel
def cuts58653 : List PrefixCut := [⟨64,210270969,210271091⟩]
theorem checked58653 : checkPrefixCuts (2^48) 7691698177 10 Manual.Count131072.C058653.packed 64 cuts58653 = true := by
 decide +kernel
def cuts58654 : List PrefixCut := [⟨36,119954599,119954668⟩,
⟨64,212902154,212902278⟩]
theorem checked58654 : checkPrefixCuts (2^48) 7691829249 10 Manual.Count131072.C058654.packed 64 cuts58654 = true := by
 decide +kernel
def pointBounds58654 : List (Nat × Nat × Nat) := [(7691902976,113636630851223,113637019098574)]
theorem point_links_checked58654 : (cuts58654.take 1).map (fun c => (7691829249-1+2*2^10*c.k,113636510896624+c.lower,113636899143906+c.upper)) = pointBounds58654 := by
 decide +kernel
def cuts58655 : List PrefixCut := [⟨64,211764136,211764258⟩]
theorem checked58655 : checkPrefixCuts (2^48) 7691960321 10 Manual.Count131072.C058655.packed 64 cuts58655 = true := by
 decide +kernel
def cuts58656 : List PrefixCut := [⟨26,85590181,85590228⟩,
⟨64,210260243,210260361⟩]
theorem checked58656 : checkPrefixCuts (2^48) 7692091393 10 Manual.Count131072.C058656.packed 64 cuts58656 = true := by
 decide +kernel
def pointBounds58656 : List (Nat × Nat × Nat) := [(7692144640,113637021153095,113637409400670)]
theorem point_links_checked58656 : (cuts58656.take 1).map (fun c => (7692091393-1+2*2^10*c.k,113636935562914+c.lower,113637323810442+c.upper)) = pointBounds58656 := by
 decide +kernel
def cuts58657 : List PrefixCut := [⟨64,214501299,214501422⟩]
theorem checked58657 : checkPrefixCuts (2^48) 7692222465 10 Manual.Count131072.C058657.packed 64 cuts58657 = true := by
 decide +kernel
def cuts58658 : List PrefixCut := [⟨16,54338289,54338321⟩,
⟨64,209338309,209338431⟩]
theorem checked58658 : checkPrefixCuts (2^48) 7692353537 10 Manual.Count131072.C058658.packed 64 cuts58658 = true := by
 decide +kernel
def pointBounds58658 : List (Nat × Nat × Nat) := [(7692386304,113637414662745,113637802910546)]
theorem point_links_checked58658 : (cuts58658.take 1).map (fun c => (7692353537-1+2*2^10*c.k,113637360324456+c.lower,113637748572225+c.upper)) = pointBounds58658 := by
 decide +kernel
def cuts58659 : List PrefixCut := [⟨64,209664037,209664156⟩]
theorem checked58659 : checkPrefixCuts (2^48) 7692484609 10 Manual.Count131072.C058659.packed 64 cuts58659 = true := by
 decide +kernel
def cuts58660 : List PrefixCut := [⟨6,19722141,19722152⟩,
⟨64,209806839,209806961⟩]
theorem checked58660 : checkPrefixCuts (2^48) 7692615681 10 Manual.Count131072.C058660.packed 64 cuts58660 = true := by
 decide +kernel
def pointBounds58660 : List (Nat × Nat × Nat) := [(7692627968,113637799048943,113638187296964)]
theorem point_links_checked58660 : (cuts58660.take 1).map (fun c => (7692615681-1+2*2^10*c.k,113637779326802+c.lower,113638167574812+c.upper)) = pointBounds58660 := by
 decide +kernel
def cuts58661 : List PrefixCut := [⟨60,195387151,195387264⟩,
⟨64,207534713,207534833⟩]
theorem checked58661 : checkPrefixCuts (2^48) 7692746753 10 Manual.Count131072.C058661.packed 64 cuts58661 = true := by
 decide +kernel
def pointBounds58661 : List (Nat × Nat × Nat) := [(7692869632,113638184520792,113638572769037)]
theorem point_links_checked58661 : (cuts58661.take 1).map (fun c => (7692746753-1+2*2^10*c.k,113637989133641+c.lower,113638377381773+c.upper)) = pointBounds58661 := by
 decide +kernel
def cuts58662 : List PrefixCut := [⟨64,209287442,209287560⟩]
theorem checked58662 : checkPrefixCuts (2^48) 7692877825 10 Manual.Count131072.C058662.packed 64 cuts58662 = true := by
 decide +kernel
def cuts58663 : List PrefixCut := [⟨50,165195538,165195634⟩,
⟨64,211588926,211589050⟩]
theorem checked58663 : checkPrefixCuts (2^48) 7693008897 10 Manual.Count131072.C058663.packed 64 cuts58663 = true := by
 decide +kernel
def pointBounds58663 : List (Nat × Nat × Nat) := [(7693111296,113638571151334,113638959399800)]
theorem point_links_checked58663 : (cuts58663.take 1).map (fun c => (7693008897-1+2*2^10*c.k,113638405955796+c.lower,113638794204166+c.upper)) = pointBounds58663 := by
 decide +kernel
def cuts58664 : List PrefixCut := [⟨64,210194990,210195114⟩]
theorem checked58664 : checkPrefixCuts (2^48) 7693139969 10 Manual.Count131072.C058664.packed 64 cuts58664 = true := by
 decide +kernel
def cuts58665 : List PrefixCut := [⟨40,134896125,134896202⟩,
⟨64,211984188,211984311⟩]
theorem checked58665 : checkPrefixCuts (2^48) 7693271041 10 Manual.Count131072.C058665.packed 64 cuts58665 = true := by
 decide +kernel
def pointBounds58665 : List (Nat × Nat × Nat) := [(7693352960,113638962635837,113639350884532)]
theorem point_links_checked58665 : (cuts58665.take 1).map (fun c => (7693271041-1+2*2^10*c.k,113638827739712+c.lower,113639215988330+c.upper)) = pointBounds58665 := by
 decide +kernel
def cuts58666 : List PrefixCut := [⟨64,212529330,212529450⟩]
theorem checked58666 : checkPrefixCuts (2^48) 7693402113 10 Manual.Count131072.C058666.packed 64 cuts58666 = true := by
 decide +kernel
def cuts58667 : List PrefixCut := [⟨30,98488868,98488926⟩,
⟨64,212013516,212013639⟩]
theorem checked58667 : checkPrefixCuts (2^48) 7693533185 10 Manual.Count131072.C058667.packed 64 cuts58667 = true := by
 decide +kernel
def pointBounds58667 : List (Nat × Nat × Nat) := [(7693594624,113639350742098,113639738991017)]
theorem point_links_checked58667 : (cuts58667.take 1).map (fun c => (7693533185-1+2*2^10*c.k,113639252253230+c.lower,113639640502091+c.upper)) = pointBounds58667 := by
 decide +kernel
def cuts58668 : List PrefixCut := [⟨64,210107497,210107620⟩]
theorem checked58668 : checkPrefixCuts (2^48) 7693664257 10 Manual.Count131072.C058668.packed 64 cuts58668 = true := by
 decide +kernel
def cuts58669 : List PrefixCut := [⟨20,65522957,65522995⟩,
⟨64,208750305,208750421⟩]
theorem checked58669 : checkPrefixCuts (2^48) 7693795329 10 Manual.Count131072.C058669.packed 64 cuts58669 = true := by
 decide +kernel
def pointBounds58669 : List (Nat × Nat × Nat) := [(7693836288,113639739897200,113640128146345)]
theorem point_links_checked58669 : (cuts58669.take 1).map (fun c => (7693795329-1+2*2^10*c.k,113639674374243+c.lower,113640062623350+c.upper)) = pointBounds58669 := by
 decide +kernel
def cuts58670 : List PrefixCut := [⟨64,211124683,211124804⟩]
theorem checked58670 : checkPrefixCuts (2^48) 7693926401 10 Manual.Count131072.C058670.packed 64 cuts58670 = true := by
 decide +kernel
def cuts58671 : List PrefixCut := [⟨10,32376277,32376297⟩,
⟨64,212182002,212182127⟩]
theorem checked58671 : checkPrefixCuts (2^48) 7694057473 10 Manual.Count131072.C058671.packed 64 cuts58671 = true := by
 decide +kernel
def pointBounds58671 : List (Nat × Nat × Nat) := [(7694077952,113640126625508,113640514874872)]
theorem point_links_checked58671 : (cuts58671.take 1).map (fun c => (7694057473-1+2*2^10*c.k,113640094249231+c.lower,113640482498575+c.upper)) = pointBounds58671 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000270
