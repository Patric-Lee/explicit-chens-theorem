import PlattAssemblyKernel
import PlattCertificates.Count131072.C060576
import PlattCertificates.Count131072.C060577
import PlattCertificates.Count131072.C060578
import PlattCertificates.Count131072.C060579
import PlattCertificates.Count131072.C060580
import PlattCertificates.Count131072.C060581
import PlattCertificates.Count131072.C060582
import PlattCertificates.Count131072.C060583
import PlattCertificates.Count131072.C060584
import PlattCertificates.Count131072.C060585
import PlattCertificates.Count131072.C060586
import PlattCertificates.Count131072.C060587
import PlattCertificates.Count131072.C060588
import PlattCertificates.Count131072.C060589
import PlattCertificates.Count131072.C060590
import PlattCertificates.Count131072.C060591
import PlattCertificates.Count131072.C060592
import PlattCertificates.Count131072.C060593
import PlattCertificates.Count131072.C060594
import PlattCertificates.Count131072.C060595
import PlattCertificates.Count131072.C060596
import PlattCertificates.Count131072.C060597
import PlattCertificates.Count131072.C060598
import PlattCertificates.Count131072.C060599
import PlattCertificates.Count131072.C060600
import PlattCertificates.Count131072.C060601
import PlattCertificates.Count131072.C060602
import PlattCertificates.Count131072.C060603
import PlattCertificates.Count131072.C060604
import PlattCertificates.Count131072.C060605
import PlattCertificates.Count131072.C060606
import PlattCertificates.Count131072.C060607
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60576 : List PrefixCut := [⟨30,96272460,96272516⟩,
⟨64,203882713,203882832⟩]
theorem checked60576 : checkPrefixCuts (2^48) 7943749633 10 Manual.Count131072.C060576.packed 64 cuts60576 = true := by
 decide +kernel
def pointBounds60576 : List (Nat × Nat × Nat) := [(7943811072,114034822266308,114035210740997)]
theorem point_links_checked60576 : (cuts60576.take 1).map (fun c => (7943749633-1+2*2^10*c.k,114034725993848+c.lower,114035114468481+c.upper)) = pointBounds60576 := by
 decide +kernel
def cuts60577 : List PrefixCut := [⟨64,205190356,205190473⟩]
theorem checked60577 : checkPrefixCuts (2^48) 7943880705 10 Manual.Count131072.C060577.packed 64 cuts60577 = true := by
 decide +kernel
def cuts60578 : List PrefixCut := [⟨24,75258051,75258092⟩,
⟨64,201891789,201891901⟩]
theorem checked60578 : checkPrefixCuts (2^48) 7944011777 10 Manual.Count131072.C060578.packed 64 cuts60578 = true := by
 decide +kernel
def pointBounds60578 : List (Nat × Nat × Nat) := [(7944060928,114035210324968,114035598799878)]
theorem point_links_checked60578 : (cuts60578.take 1).map (fun c => (7944011777-1+2*2^10*c.k,114035135066917+c.lower,114035523541786+c.upper)) = pointBounds60578 := by
 decide +kernel
def cuts60579 : List PrefixCut := [⟨64,205431606,205431723⟩]
theorem checked60579 : checkPrefixCuts (2^48) 7944142849 10 Manual.Count131072.C060579.packed 64 cuts60579 = true := by
 decide +kernel
def cuts60580 : List PrefixCut := [⟨18,57362924,57362958⟩,
⟨64,203089779,203089897⟩]
theorem checked60580 : checkPrefixCuts (2^48) 7944273921 10 Manual.Count131072.C060580.packed 64 cuts60580 = true := by
 decide +kernel
def pointBounds60580 : List (Nat × Nat × Nat) := [(7944310784,114035599753236,114035988228368)]
theorem point_links_checked60580 : (cuts60580.take 1).map (fun c => (7944273921-1+2*2^10*c.k,114035542390312+c.lower,114035930865410+c.upper)) = pointBounds60580 := by
 decide +kernel
def cuts60581 : List PrefixCut := [⟨64,206346012,206346123⟩]
theorem checked60581 : checkPrefixCuts (2^48) 7944404993 10 Manual.Count131072.C060581.packed 64 cuts60581 = true := by
 decide +kernel
def cuts60582 : List PrefixCut := [⟨12,38406059,38406082⟩,
⟨64,201134439,201134557⟩]
theorem checked60582 : checkPrefixCuts (2^48) 7944536065 10 Manual.Count131072.C060582.packed 64 cuts60582 = true := by
 decide +kernel
def pointBounds60582 : List (Nat × Nat × Nat) := [(7944560640,114035990232162,114036378707512)]
theorem point_links_checked60582 : (cuts60582.take 1).map (fun c => (7944536065-1+2*2^10*c.k,114035951826103+c.lower,114036340301430+c.upper)) = pointBounds60582 := by
 decide +kernel
def cuts60583 : List PrefixCut := [⟨64,204815761,204815876⟩]
theorem checked60583 : checkPrefixCuts (2^48) 7944667137 10 Manual.Count131072.C060583.packed 64 cuts60583 = true := by
 decide +kernel
def cuts60584 : List PrefixCut := [⟨6,19273269,19273280⟩,
⟨64,204883235,204883350⟩]
theorem checked60584 : checkPrefixCuts (2^48) 7944798209 10 Manual.Count131072.C060584.packed 64 cuts60584 = true := by
 decide +kernel
def pointBounds60584 : List (Nat × Nat × Nat) := [(7944810496,114036377049572,114036765525143)]
theorem point_links_checked60584 : (cuts60584.take 1).map (fun c => (7944798209-1+2*2^10*c.k,114036357776303+c.lower,114036746251863+c.upper)) = pointBounds60584 := by
 decide +kernel
def cuts60585 : List PrefixCut := [⟨64,203746145,203746261⟩]
theorem checked60585 : checkPrefixCuts (2^48) 7944929281 10 Manual.Count131072.C060585.packed 64 cuts60585 = true := by
 decide +kernel
def pointBounds60585 : List (Nat × Nat × Nat) := [(7945060352,114036766405683,114037154881474)]
theorem point_links_checked60585 : (cuts60585.take 1).map (fun c => (7944929281-1+2*2^10*c.k,114036562659538+c.lower,114036951135213+c.upper)) = pointBounds60585 := by
 decide +kernel
def cuts60586 : List PrefixCut := [⟨64,202750802,202750923⟩]
theorem checked60586 : checkPrefixCuts (2^48) 7945060353 10 Manual.Count131072.C060586.packed 64 cuts60586 = true := by
 decide +kernel
def cuts60587 : List PrefixCut := [⟨58,185105105,185105209⟩,
⟨64,205439926,205440042⟩]
theorem checked60587 : checkPrefixCuts (2^48) 7945191425 10 Manual.Count131072.C060587.packed 64 cuts60587 = true := by
 decide +kernel
def pointBounds60587 : List (Nat × Nat × Nat) := [(7945310208,114037154261590,114037542737606)]
theorem point_links_checked60587 : (cuts60587.take 1).map (fun c => (7945191425-1+2*2^10*c.k,114036969156485+c.lower,114037357632397+c.upper)) = pointBounds60587 := by
 decide +kernel
def cuts60588 : List PrefixCut := [⟨64,206463887,206464004⟩]
theorem checked60588 : checkPrefixCuts (2^48) 7945322497 10 Manual.Count131072.C060588.packed 64 cuts60588 = true := by
 decide +kernel
def cuts60589 : List PrefixCut := [⟨52,164127116,164127208⟩,
⟨64,202173969,202174083⟩]
theorem checked60589 : checkPrefixCuts (2^48) 7945453569 10 Manual.Count131072.C060589.packed 64 cuts60589 = true := by
 decide +kernel
def pointBounds60589 : List (Nat × Nat × Nat) := [(7945560064,114037545187414,114037933663651)]
theorem point_links_checked60589 : (cuts60589.take 1).map (fun c => (7945453569-1+2*2^10*c.k,114037381060298+c.lower,114037769536443+c.upper)) = pointBounds60589 := by
 decide +kernel
def cuts60590 : List PrefixCut := [⟨64,202418620,202418732⟩]
theorem checked60590 : checkPrefixCuts (2^48) 7945584641 10 Manual.Count131072.C060590.packed 64 cuts60590 = true := by
 decide +kernel
def cuts60591 : List PrefixCut := [⟨46,144957176,144957255⟩,
⟨64,202592408,202592519⟩]
theorem checked60591 : checkPrefixCuts (2^48) 7945715713 10 Manual.Count131072.C060591.packed 64 cuts60591 = true := by
 decide +kernel
def pointBounds60591 : List (Nat × Nat × Nat) := [(7945809920,114037930610063,114038319086513)]
theorem point_links_checked60591 : (cuts60591.take 1).map (fun c => (7945715713-1+2*2^10*c.k,114037785652887+c.lower,114038174129258+c.upper)) = pointBounds60591 := by
 decide +kernel
def cuts60592 : List PrefixCut := [⟨64,206839918,206840035⟩]
theorem checked60592 : checkPrefixCuts (2^48) 7945846785 10 Manual.Count131072.C060592.packed 64 cuts60592 = true := by
 decide +kernel
def cuts60593 : List PrefixCut := [⟨40,126744869,126744943⟩,
⟨64,202018945,202019067⟩]
theorem checked60593 : checkPrefixCuts (2^48) 7945977857 10 Manual.Count131072.C060593.packed 64 cuts60593 = true := by
 decide +kernel
def pointBounds60593 : List (Nat × Nat × Nat) := [(7946059776,114038321830082,114038710306755)]
theorem point_links_checked60593 : (cuts60593.take 1).map (fun c => (7945977857-1+2*2^10*c.k,114038195085213+c.lower,114038583561812+c.upper)) = pointBounds60593 := by
 decide +kernel
def cuts60594 : List PrefixCut := [⟨64,203574224,203574338⟩]
theorem checked60594 : checkPrefixCuts (2^48) 7946108929 10 Manual.Count131072.C060594.packed 64 cuts60594 = true := by
 decide +kernel
def cuts60595 : List PrefixCut := [⟨34,108498340,108498401⟩,
⟨64,205200268,205200386⟩]
theorem checked60595 : checkPrefixCuts (2^48) 7946240001 10 Manual.Count131072.C060595.packed 64 cuts60595 = true := by
 decide +kernel
def pointBounds60595 : List (Nat × Nat × Nat) := [(7946309632,114038709176722,114039097653618)]
theorem point_links_checked60595 : (cuts60595.take 1).map (fun c => (7946240001-1+2*2^10*c.k,114038600678382+c.lower,114038989155217+c.upper)) = pointBounds60595 := by
 decide +kernel
def cuts60596 : List PrefixCut := [⟨64,206082431,206082549⟩]
theorem checked60596 : checkPrefixCuts (2^48) 7946371073 10 Manual.Count131072.C060596.packed 64 cuts60596 = true := by
 decide +kernel
def cuts60597 : List PrefixCut := [⟨28,88446496,88446545⟩,
⟨64,203139089,203139202⟩]
theorem checked60597 : checkPrefixCuts (2^48) 7946502145 10 Manual.Count131072.C060597.packed 64 cuts60597 = true := by
 decide +kernel
def pointBounds60597 : List (Nat × Nat × Nat) := [(7946559488,114039100407577,114039488884697)]
theorem point_links_checked60597 : (cuts60597.take 1).map (fun c => (7946502145-1+2*2^10*c.k,114039011961081+c.lower,114039400438152+c.upper)) = pointBounds60597 := by
 decide +kernel
def cuts60598 : List PrefixCut := [⟨64,201258474,201258589⟩]
theorem checked60598 : checkPrefixCuts (2^48) 7946633217 10 Manual.Count131072.C060598.packed 64 cuts60598 = true := by
 decide +kernel
def cuts60599 : List PrefixCut := [⟨22,66943730,66943768⟩,
⟨64,199767491,199767603⟩]
theorem checked60599 : checkPrefixCuts (2^48) 7946764289 10 Manual.Count131072.C060599.packed 64 cuts60599 = true := by
 decide +kernel
def pointBounds60599 : List (Nat × Nat × Nat) := [(7946809344,114039483302374,114039871779711)]
theorem point_links_checked60599 : (cuts60599.take 1).map (fun c => (7946764289-1+2*2^10*c.k,114039416358644+c.lower,114039804835943+c.upper)) = pointBounds60599 := by
 decide +kernel
def cuts60600 : List PrefixCut := [⟨64,205006265,205006383⟩]
theorem checked60600 : checkPrefixCuts (2^48) 7946895361 10 Manual.Count131072.C060600.packed 64 cuts60600 = true := by
 decide +kernel
def cuts60601 : List PrefixCut := [⟨16,51817740,51817769⟩,
⟨64,204577863,204577981⟩]
theorem checked60601 : checkPrefixCuts (2^48) 7947026433 10 Manual.Count131072.C060601.packed 64 cuts60601 = true := by
 decide +kernel
def pointBounds60601 : List (Nat × Nat × Nat) := [(7947059200,114039872950140,114040261427698)]
theorem point_links_checked60601 : (cuts60601.take 1).map (fun c => (7947026433-1+2*2^10*c.k,114039821132400+c.lower,114040209609929+c.upper)) = pointBounds60601 := by
 decide +kernel
def cuts60602 : List PrefixCut := [⟨64,202838994,202839112⟩]
theorem checked60602 : checkPrefixCuts (2^48) 7947157505 10 Manual.Count131072.C060602.packed 64 cuts60602 = true := by
 decide +kernel
def cuts60603 : List PrefixCut := [⟨10,32973862,32973882⟩,
⟨64,205102382,205102499⟩]
theorem checked60603 : checkPrefixCuts (2^48) 7947288577 10 Manual.Count131072.C060603.packed 64 cuts60603 = true := by
 decide +kernel
def pointBounds60603 : List (Nat × Nat × Nat) := [(7947309056,114040261523119,114040650000904)]
theorem point_links_checked60603 : (cuts60603.take 1).map (fun c => (7947288577-1+2*2^10*c.k,114040228549257+c.lower,114040617027022+c.upper)) = pointBounds60603 := by
 decide +kernel
def cuts60604 : List PrefixCut := [⟨64,205169813,205169931⟩]
theorem checked60604 : checkPrefixCuts (2^48) 7947419649 10 Manual.Count131072.C060604.packed 64 cuts60604 = true := by
 decide +kernel
def cuts60605 : List PrefixCut := [⟨4,13139537,13139545⟩,
⟨64,204387289,204387408⟩]
theorem checked60605 : checkPrefixCuts (2^48) 7947550721 10 Manual.Count131072.C060605.packed 64 cuts60605 = true := by
 decide +kernel
def pointBounds60605 : List (Nat × Nat × Nat) := [(7947558912,114040651960989,114041040438997)]
theorem point_links_checked60605 : (cuts60605.take 1).map (fun c => (7947550721-1+2*2^10*c.k,114040638821452+c.lower,114041027299452+c.upper)) = pointBounds60605 := by
 decide +kernel
def cuts60606 : List PrefixCut := [⟨62,196734172,196734283⟩,
⟨64,203250605,203250720⟩]
theorem checked60606 : checkPrefixCuts (2^48) 7947681793 10 Manual.Count131072.C060606.packed 64 cuts60606 = true := by
 decide +kernel
def pointBounds60606 : List (Nat × Nat × Nat) := [(7947808768,114041039942913,114041428421143)]
theorem point_links_checked60606 : (cuts60606.take 1).map (fun c => (7947681793-1+2*2^10*c.k,114040843208741+c.lower,114041231686860+c.upper)) = pointBounds60606 := by
 decide +kernel
def cuts60607 : List PrefixCut := [⟨64,204132619,204132735⟩]
theorem checked60607 : checkPrefixCuts (2^48) 7947812865 10 Manual.Count131072.C060607.packed 64 cuts60607 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000018
