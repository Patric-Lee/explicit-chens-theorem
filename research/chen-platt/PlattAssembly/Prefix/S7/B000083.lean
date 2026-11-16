import PlattAssemblyKernel
import PlattCertificates.Count131072.C062656
import PlattCertificates.Count131072.C062657
import PlattCertificates.Count131072.C062658
import PlattCertificates.Count131072.C062659
import PlattCertificates.Count131072.C062660
import PlattCertificates.Count131072.C062661
import PlattCertificates.Count131072.C062662
import PlattCertificates.Count131072.C062663
import PlattCertificates.Count131072.C062664
import PlattCertificates.Count131072.C062665
import PlattCertificates.Count131072.C062666
import PlattCertificates.Count131072.C062667
import PlattCertificates.Count131072.C062668
import PlattCertificates.Count131072.C062669
import PlattCertificates.Count131072.C062670
import PlattCertificates.Count131072.C062671
import PlattCertificates.Count131072.C062672
import PlattCertificates.Count131072.C062673
import PlattCertificates.Count131072.C062674
import PlattCertificates.Count131072.C062675
import PlattCertificates.Count131072.C062676
import PlattCertificates.Count131072.C062677
import PlattCertificates.Count131072.C062678
import PlattCertificates.Count131072.C062679
import PlattCertificates.Count131072.C062680
import PlattCertificates.Count131072.C062681
import PlattCertificates.Count131072.C062682
import PlattCertificates.Count131072.C062683
import PlattCertificates.Count131072.C062684
import PlattCertificates.Count131072.C062685
import PlattCertificates.Count131072.C062686
import PlattCertificates.Count131072.C062687
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000083
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62656 : List PrefixCut := [⟨64,194925188,194925301⟩]
theorem checked62656 : checkPrefixCuts (2^48) 8216379393 10 Manual.Count131072.C062656.packed 64 cuts62656 = true := by
 decide +kernel
def cuts62657 : List PrefixCut := [⟨42,126031694,126031763⟩,
⟨64,193449036,193449145⟩]
theorem checked62657 : checkPrefixCuts (2^48) 8216510465 10 Manual.Count131072.C062657.packed 64 cuts62657 = true := by
 decide +kernel
def pointBounds62657 : List (Nat × Nat × Nat) := [(8216596480,114451463551637,114451852265180)]
theorem point_links_checked62657 : (cuts62657.take 1).map (fun c => (8216510465-1+2*2^10*c.k,114451337519943+c.lower,114451726233417+c.upper)) = pointBounds62657 := by
 decide +kernel
def cuts62658 : List PrefixCut := [⟨64,199235286,199235398⟩]
theorem checked62658 : checkPrefixCuts (2^48) 8216641537 10 Manual.Count131072.C062658.packed 64 cuts62658 = true := by
 decide +kernel
def cuts62659 : List PrefixCut := [⟨40,122396566,122396636⟩,
⟨64,195977797,195977911⟩]
theorem checked62659 : checkPrefixCuts (2^48) 8216772609 10 Manual.Count131072.C062659.packed 64 cuts62659 = true := by
 decide +kernel
def pointBounds62659 : List (Nat × Nat × Nat) := [(8216854528,114451852600831,114452241314596)]
theorem point_links_checked62659 : (cuts62659.take 1).map (fun c => (8216772609-1+2*2^10*c.k,114451730204265+c.lower,114452118917960+c.upper)) = pointBounds62659 := by
 decide +kernel
def cuts62660 : List PrefixCut := [⟨64,197755941,197756057⟩]
theorem checked62660 : checkPrefixCuts (2^48) 8216903681 10 Manual.Count131072.C062660.packed 64 cuts62660 = true := by
 decide +kernel
def cuts62661 : List PrefixCut := [⟨38,117322974,117323043⟩,
⟨64,196553887,196553999⟩]
theorem checked62661 : checkPrefixCuts (2^48) 8217034753 10 Manual.Count131072.C062661.packed 64 cuts62661 = true := by
 decide +kernel
def pointBounds62661 : List (Nat × Nat × Nat) := [(8217112576,114452241260977,114452629974971)]
theorem point_links_checked62661 : (cuts62661.take 1).map (fun c => (8217034753-1+2*2^10*c.k,114452123938003+c.lower,114452512651928+c.upper)) = pointBounds62661 := by
 decide +kernel
def cuts62662 : List PrefixCut := [⟨64,195694376,195694491⟩]
theorem checked62662 : checkPrefixCuts (2^48) 8217165825 10 Manual.Count131072.C062662.packed 64 cuts62662 = true := by
 decide +kernel
def cuts62663 : List PrefixCut := [⟨36,108995585,108995648⟩,
⟨64,193841566,193841677⟩]
theorem checked62663 : checkPrefixCuts (2^48) 8217296897 10 Manual.Count131072.C062663.packed 64 cuts62663 = true := by
 decide +kernel
def pointBounds62663 : List (Nat × Nat × Nat) := [(8217370624,114452625181851,114453013896066)]
theorem point_links_checked62663 : (cuts62663.take 1).map (fun c => (8217296897-1+2*2^10*c.k,114452516186266+c.lower,114452904900418+c.upper)) = pointBounds62663 := by
 decide +kernel
def cuts62664 : List PrefixCut := [⟨64,194523542,194523652⟩]
theorem checked62664 : checkPrefixCuts (2^48) 8217427969 10 Manual.Count131072.C062664.packed 64 cuts62664 = true := by
 decide +kernel
def cuts62665 : List PrefixCut := [⟨34,107382260,107382317⟩,
⟨64,199863850,199863964⟩]
theorem checked62665 : checkPrefixCuts (2^48) 8217559041 10 Manual.Count131072.C062665.packed 64 cuts62665 = true := by
 decide +kernel
def pointBounds62665 : List (Nat × Nat × Nat) := [(8217628672,114453011933634,114453400648064)]
theorem point_links_checked62665 : (cuts62665.take 1).map (fun c => (8217559041-1+2*2^10*c.k,114452904551374+c.lower,114453293265747+c.upper)) = pointBounds62665 := by
 decide +kernel
def cuts62666 : List PrefixCut := [⟨64,196332689,196332802⟩]
theorem checked62666 : checkPrefixCuts (2^48) 8217690113 10 Manual.Count131072.C062666.packed 64 cuts62666 = true := by
 decide +kernel
def cuts62667 : List PrefixCut := [⟨32,98473434,98473495⟩,
⟨64,197151597,197151712⟩]
theorem checked62667 : checkPrefixCuts (2^48) 8217821185 10 Manual.Count131072.C062667.packed 64 cuts62667 = true := by
 decide +kernel
def pointBounds62667 : List (Nat × Nat × Nat) := [(8217886720,114453399221347,114453787936008)]
theorem point_links_checked62667 : (cuts62667.take 1).map (fun c => (8217821185-1+2*2^10*c.k,114453300747913+c.lower,114453689462513+c.upper)) = pointBounds62667 := by
 decide +kernel
def cuts62668 : List PrefixCut := [⟨64,194750890,194751003⟩]
theorem checked62668 : checkPrefixCuts (2^48) 8217952257 10 Manual.Count131072.C062668.packed 64 cuts62668 = true := by
 decide +kernel
def cuts62669 : List PrefixCut := [⟨30,92784729,92784781⟩,
⟨64,197796069,197796183⟩]
theorem checked62669 : checkPrefixCuts (2^48) 8218083329 10 Manual.Count131072.C062669.packed 64 cuts62669 = true := by
 decide +kernel
def pointBounds62669 : List (Nat × Nat × Nat) := [(8218144768,114453785435129,114454174150009)]
theorem point_links_checked62669 : (cuts62669.take 1).map (fun c => (8218083329-1+2*2^10*c.k,114453692650400+c.lower,114454081365228+c.upper)) = pointBounds62669 := by
 decide +kernel
def cuts62670 : List PrefixCut := [⟨64,196320174,196320291⟩]
theorem checked62670 : checkPrefixCuts (2^48) 8218214401 10 Manual.Count131072.C062670.packed 64 cuts62670 = true := by
 decide +kernel
def cuts62671 : List PrefixCut := [⟨28,87199135,87199186⟩,
⟨64,197550027,197550140⟩]
theorem checked62671 : checkPrefixCuts (2^48) 8218345473 10 Manual.Count131072.C062671.packed 64 cuts62671 = true := by
 decide +kernel
def pointBounds62671 : List (Nat × Nat × Nat) := [(8218402816,114454173965778,114454562680888)]
theorem point_links_checked62671 : (cuts62671.take 1).map (fun c => (8218345473-1+2*2^10*c.k,114454086766643+c.lower,114454475481702+c.upper)) = pointBounds62671 := by
 decide +kernel
def cuts62672 : List PrefixCut := [⟨64,198540078,198540190⟩]
theorem checked62672 : checkPrefixCuts (2^48) 8218476545 10 Manual.Count131072.C062672.packed 64 cuts62672 = true := by
 decide +kernel
def cuts62673 : List PrefixCut := [⟨26,77572581,77572622⟩,
⟨64,196447752,196447863⟩]
theorem checked62673 : checkPrefixCuts (2^48) 8218607617 10 Manual.Count131072.C062673.packed 64 cuts62673 = true := by
 decide +kernel
def pointBounds62673 : List (Nat × Nat × Nat) := [(8218660864,114454560429329,114454949144654)]
theorem point_links_checked62673 : (cuts62673.take 1).map (fun c => (8218607617-1+2*2^10*c.k,114454482856748+c.lower,114454871572032+c.upper)) = pointBounds62673 := by
 decide +kernel
def cuts62674 : List PrefixCut := [⟨64,197506323,197506432⟩]
theorem checked62674 : checkPrefixCuts (2^48) 8218738689 10 Manual.Count131072.C062674.packed 64 cuts62674 = true := by
 decide +kernel
def cuts62675 : List PrefixCut := [⟨24,72672761,72672804⟩,
⟨64,196441500,196441612⟩]
theorem checked62675 : checkPrefixCuts (2^48) 8218869761 10 Manual.Count131072.C062675.packed 64 cuts62675 = true := by
 decide +kernel
def pointBounds62675 : List (Nat × Nat × Nat) := [(8218918912,114454949483584,114455338199131)]
theorem point_links_checked62675 : (cuts62675.take 1).map (fun c => (8218869761-1+2*2^10*c.k,114454876810823+c.lower,114455265526327+c.upper)) = pointBounds62675 := by
 decide +kernel
def cuts62676 : List PrefixCut := [⟨64,195650701,195650821⟩]
theorem checked62676 : checkPrefixCuts (2^48) 8219000833 10 Manual.Count131072.C062676.packed 64 cuts62676 = true := by
 decide +kernel
def cuts62677 : List PrefixCut := [⟨22,67704761,67704799⟩,
⟨64,196640715,196640824⟩]
theorem checked62677 : checkPrefixCuts (2^48) 8219131905 10 Manual.Count131072.C062677.packed 64 cuts62677 = true := by
 decide +kernel
def pointBounds62677 : List (Nat × Nat × Nat) := [(8219176960,114455336607785,114455725323559)]
theorem point_links_checked62677 : (cuts62677.take 1).map (fun c => (8219131905-1+2*2^10*c.k,114455268903024+c.lower,114455657618760+c.upper)) = pointBounds62677 := by
 decide +kernel
def cuts62678 : List PrefixCut := [⟨64,197938921,197939033⟩]
theorem checked62678 : checkPrefixCuts (2^48) 8219262977 10 Manual.Count131072.C062678.packed 64 cuts62678 = true := by
 decide +kernel
def cuts62679 : List PrefixCut := [⟨20,60956325,60956359⟩,
⟨64,197319333,197319449⟩]
theorem checked62679 : checkPrefixCuts (2^48) 8219394049 10 Manual.Count131072.C062679.packed 64 cuts62679 = true := by
 decide +kernel
def pointBounds62679 : List (Nat × Nat × Nat) := [(8219435008,114455724438985,114456113154976)]
theorem point_links_checked62679 : (cuts62679.take 1).map (fun c => (8219394049-1+2*2^10*c.k,114455663482660+c.lower,114456052198617+c.upper)) = pointBounds62679 := by
 decide +kernel
def cuts62680 : List PrefixCut := [⟨64,197487421,197487532⟩]
theorem checked62680 : checkPrefixCuts (2^48) 8219525121 10 Manual.Count131072.C062680.packed 64 cuts62680 = true := by
 decide +kernel
def cuts62681 : List PrefixCut := [⟨18,55612329,55612361⟩,
⟨64,199675868,199675984⟩]
theorem checked62681 : checkPrefixCuts (2^48) 8219656193 10 Manual.Count131072.C062681.packed 64 cuts62681 = true := by
 decide +kernel
def pointBounds62681 : List (Nat × Nat × Nat) := [(8219693056,114456113901743,114456502617959)]
theorem point_links_checked62681 : (cuts62681.take 1).map (fun c => (8219656193-1+2*2^10*c.k,114456058289414+c.lower,114456447005598+c.upper)) = pointBounds62681 := by
 decide +kernel
def cuts62682 : List PrefixCut := [⟨64,197549605,197549719⟩]
theorem checked62682 : checkPrefixCuts (2^48) 8219787265 10 Manual.Count131072.C062682.packed 64 cuts62682 = true := by
 decide +kernel
def cuts62683 : List PrefixCut := [⟨16,49001679,49001706⟩,
⟨64,195115217,195115331⟩]
theorem checked62683 : checkPrefixCuts (2^48) 8219918337 10 Manual.Count131072.C062683.packed 64 cuts62683 = true := by
 decide +kernel
def pointBounds62683 : List (Nat × Nat × Nat) := [(8219951104,114456504516566,114456893233007)]
theorem point_links_checked62683 : (cuts62683.take 1).map (fun c => (8219918337-1+2*2^10*c.k,114456455514887+c.lower,114456844231301+c.upper)) = pointBounds62683 := by
 decide +kernel
def cuts62684 : List PrefixCut := [⟨64,196070885,196070997⟩]
theorem checked62684 : checkPrefixCuts (2^48) 8220049409 10 Manual.Count131072.C062684.packed 64 cuts62684 = true := by
 decide +kernel
def cuts62685 : List PrefixCut := [⟨14,43144763,43144789⟩,
⟨64,196718358,196718474⟩]
theorem checked62685 : checkPrefixCuts (2^48) 8220180481 10 Manual.Count131072.C062685.packed 64 cuts62685 = true := by
 decide +kernel
def pointBounds62685 : List (Nat × Nat × Nat) := [(8220209152,114456889845752,114457278562418)]
theorem point_links_checked62685 : (cuts62685.take 1).map (fun c => (8220180481-1+2*2^10*c.k,114456846700989+c.lower,114457235417629+c.upper)) = pointBounds62685 := by
 decide +kernel
def cuts62686 : List PrefixCut := [⟨64,196954906,196955018⟩]
theorem checked62686 : checkPrefixCuts (2^48) 8220311553 10 Manual.Count131072.C062686.packed 64 cuts62686 = true := by
 decide +kernel
def cuts62687 : List PrefixCut := [⟨12,35952833,35952853⟩,
⟨64,194760364,194760474⟩]
theorem checked62687 : checkPrefixCuts (2^48) 8220442625 10 Manual.Count131072.C062687.packed 64 cuts62687 = true := by
 decide +kernel
def pointBounds62687 : List (Nat × Nat × Nat) := [(8220467200,114457276327086,114457665043974)]
theorem point_links_checked62687 : (cuts62687.take 1).map (fun c => (8220442625-1+2*2^10*c.k,114457240374253+c.lower,114457629091121+c.upper)) = pointBounds62687 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000083
