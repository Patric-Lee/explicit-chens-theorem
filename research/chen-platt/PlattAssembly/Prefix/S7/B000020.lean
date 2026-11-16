import PlattAssemblyKernel
import PlattCertificates.Count131072.C060640
import PlattCertificates.Count131072.C060641
import PlattCertificates.Count131072.C060642
import PlattCertificates.Count131072.C060643
import PlattCertificates.Count131072.C060644
import PlattCertificates.Count131072.C060645
import PlattCertificates.Count131072.C060646
import PlattCertificates.Count131072.C060647
import PlattCertificates.Count131072.C060648
import PlattCertificates.Count131072.C060649
import PlattCertificates.Count131072.C060650
import PlattCertificates.Count131072.C060651
import PlattCertificates.Count131072.C060652
import PlattCertificates.Count131072.C060653
import PlattCertificates.Count131072.C060654
import PlattCertificates.Count131072.C060655
import PlattCertificates.Count131072.C060656
import PlattCertificates.Count131072.C060657
import PlattCertificates.Count131072.C060658
import PlattCertificates.Count131072.C060659
import PlattCertificates.Count131072.C060660
import PlattCertificates.Count131072.C060661
import PlattCertificates.Count131072.C060662
import PlattCertificates.Count131072.C060663
import PlattCertificates.Count131072.C060664
import PlattCertificates.Count131072.C060665
import PlattCertificates.Count131072.C060666
import PlattCertificates.Count131072.C060667
import PlattCertificates.Count131072.C060668
import PlattCertificates.Count131072.C060669
import PlattCertificates.Count131072.C060670
import PlattCertificates.Count131072.C060671
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60640 : List PrefixCut := [⟨64,206428510,206428627⟩]
theorem checked60640 : checkPrefixCuts (2^48) 7952138241 10 Manual.Count131072.C060640.packed 64 cuts60640 = true := by
 decide +kernel
def cuts60641 : List PrefixCut := [⟨18,56172600,56172632⟩,
⟨64,203982841,203982956⟩]
theorem checked60641 : checkPrefixCuts (2^48) 7952269313 10 Manual.Count131072.C060641.packed 64 cuts60641 = true := by
 decide +kernel
def pointBounds60641 : List (Nat × Nat × Nat) := [(7952306176,114048029355572,114048417837801)]
theorem point_links_checked60641 : (cuts60641.take 1).map (fun c => (7952269313-1+2*2^10*c.k,114047973182972+c.lower,114048361665169+c.upper)) = pointBounds60641 := by
 decide +kernel
def cuts60642 : List PrefixCut := [⟨64,201431028,201431149⟩]
theorem checked60642 : checkPrefixCuts (2^48) 7952400385 10 Manual.Count131072.C060642.packed 64 cuts60642 = true := by
 decide +kernel
def cuts60643 : List PrefixCut := [⟨12,38190473,38190496⟩,
⟨64,201392351,201392472⟩]
theorem checked60643 : checkPrefixCuts (2^48) 7952531457 10 Manual.Count131072.C060643.packed 64 cuts60643 = true := by
 decide +kernel
def pointBounds60643 : List (Nat × Nat × Nat) := [(7952556032,114048416787314,114048805269770)]
theorem point_links_checked60643 : (cuts60643.take 1).map (fun c => (7952531457-1+2*2^10*c.k,114048378596841+c.lower,114048767079274+c.upper)) = pointBounds60643 := by
 decide +kernel
def cuts60644 : List PrefixCut := [⟨64,204326689,204326802⟩]
theorem checked60644 : checkPrefixCuts (2^48) 7952662529 10 Manual.Count131072.C060644.packed 64 cuts60644 = true := by
 decide +kernel
def cuts60645 : List PrefixCut := [⟨6,18829174,18829184⟩,
⟨64,203332317,203332434⟩]
theorem checked60645 : checkPrefixCuts (2^48) 7952793601 10 Manual.Count131072.C060645.packed 64 cuts60645 = true := by
 decide +kernel
def pointBounds60645 : List (Nat × Nat × Nat) := [(7952805888,114048803145055,114049191627732)]
theorem point_links_checked60645 : (cuts60645.take 1).map (fun c => (7952793601-1+2*2^10*c.k,114048784315881+c.lower,114049172798548+c.upper)) = pointBounds60645 := by
 decide +kernel
def cuts60646 : List PrefixCut := [⟨64,202904266,202904386⟩]
theorem checked60646 : checkPrefixCuts (2^48) 7952924673 10 Manual.Count131072.C060646.packed 64 cuts60646 = true := by
 decide +kernel
def pointBounds60646 : List (Nat × Nat × Nat) := [(7953055744,114049190552464,114049579035368)]
theorem point_links_checked60646 : (cuts60646.take 1).map (fun c => (7952924673-1+2*2^10*c.k,114048987648198+c.lower,114049376130982+c.upper)) = pointBounds60646 := by
 decide +kernel
def cuts60647 : List PrefixCut := [⟨64,203821098,203821211⟩]
theorem checked60647 : checkPrefixCuts (2^48) 7953055745 10 Manual.Count131072.C060647.packed 64 cuts60647 = true := by
 decide +kernel
def cuts60648 : List PrefixCut := [⟨58,184140407,184140512⟩,
⟨64,203782359,203782473⟩]
theorem checked60648 : checkPrefixCuts (2^48) 7953186817 10 Manual.Count131072.C060648.packed 64 cuts60648 = true := by
 decide +kernel
def pointBounds60648 : List (Nat × Nat × Nat) := [(7953305600,114049578513969,114049966997091)]
theorem point_links_checked60648 : (cuts60648.take 1).map (fun c => (7953186817-1+2*2^10*c.k,114049394373562+c.lower,114049782856579+c.upper)) = pointBounds60648 := by
 decide +kernel
def cuts60649 : List PrefixCut := [⟨64,205229997,205230114⟩]
theorem checked60649 : checkPrefixCuts (2^48) 7953317889 10 Manual.Count131072.C060649.packed 64 cuts60649 = true := by
 decide +kernel
def cuts60650 : List PrefixCut := [⟨52,164846893,164846984⟩,
⟨64,202218486,202218598⟩]
theorem checked60650 : checkPrefixCuts (2^48) 7953448961 10 Manual.Count131072.C060650.packed 64 cuts60650 = true := by
 decide +kernel
def pointBounds60650 : List (Nat × Nat × Nat) := [(7953555456,114049968232811,114050356716150)]
theorem point_links_checked60650 : (cuts60650.take 1).map (fun c => (7953448961-1+2*2^10*c.k,114049803385918+c.lower,114050191869166+c.upper)) = pointBounds60650 := by
 decide +kernel
def cuts60651 : List PrefixCut := [⟨64,204550857,204550973⟩]
theorem checked60651 : checkPrefixCuts (2^48) 7953580033 10 Manual.Count131072.C060651.packed 64 cuts60651 = true := by
 decide +kernel
def cuts60652 : List PrefixCut := [⟨46,147430231,147430316⟩,
⟨64,202317989,202318104⟩]
theorem checked60652 : checkPrefixCuts (2^48) 7953711105 10 Manual.Count131072.C060652.packed 64 cuts60652 = true := by
 decide +kernel
def pointBounds60652 : List (Nat × Nat × Nat) := [(7953805312,114050357585492,114050746069053)]
theorem point_links_checked60652 : (cuts60652.take 1).map (fun c => (7953711105-1+2*2^10*c.k,114050210155261+c.lower,114050598638737+c.upper)) = pointBounds60652 := by
 decide +kernel
def cuts60653 : List PrefixCut := [⟨64,206065817,206065937⟩]
theorem checked60653 : checkPrefixCuts (2^48) 7953842177 10 Manual.Count131072.C060653.packed 64 cuts60653 = true := by
 decide +kernel
def cuts60654 : List PrefixCut := [⟨40,128351475,128351550⟩,
⟨64,204257636,204257753⟩]
theorem checked60654 : checkPrefixCuts (2^48) 7953973249 10 Manual.Count131072.C060654.packed 64 cuts60654 = true := by
 decide +kernel
def pointBounds60654 : List (Nat × Nat × Nat) := [(7954055168,114050746890542,114051135374328)]
theorem point_links_checked60654 : (cuts60654.take 1).map (fun c => (7953973249-1+2*2^10*c.k,114050618539067+c.lower,114051007022778+c.upper)) = pointBounds60654 := by
 decide +kernel
def cuts60655 : List PrefixCut := [⟨64,201812558,201812677⟩]
theorem checked60655 : checkPrefixCuts (2^48) 7954104321 10 Manual.Count131072.C060655.packed 64 cuts60655 = true := by
 decide +kernel
def cuts60656 : List PrefixCut := [⟨34,108389281,108389346⟩,
⟨64,204286280,204286401⟩]
theorem checked60656 : checkPrefixCuts (2^48) 7954235393 10 Manual.Count131072.C060656.packed 64 cuts60656 = true := by
 decide +kernel
def pointBounds60656 : List (Nat × Nat × Nat) := [(7954305024,114051132998542,114051521482554)]
theorem point_links_checked60656 : (cuts60656.take 1).map (fun c => (7954235393-1+2*2^10*c.k,114051024609261+c.lower,114051413093208+c.upper)) = pointBounds60656 := by
 decide +kernel
def cuts60657 : List PrefixCut := [⟨64,202265914,202266026⟩]
theorem checked60657 : checkPrefixCuts (2^48) 7954366465 10 Manual.Count131072.C060657.packed 64 cuts60657 = true := by
 decide +kernel
def cuts60658 : List PrefixCut := [⟨28,87402192,87402239⟩,
⟨64,201094877,201094985⟩]
theorem checked60658 : checkPrefixCuts (2^48) 7954497537 10 Manual.Count131072.C060658.packed 64 cuts60658 = true := by
 decide +kernel
def pointBounds60658 : List (Nat × Nat × Nat) := [(7954554880,114051518563647,114051907047874)]
theorem point_links_checked60658 : (cuts60658.take 1).map (fun c => (7954497537-1+2*2^10*c.k,114051431161455+c.lower,114051819645635+c.upper)) = pointBounds60658 := by
 decide +kernel
def cuts60659 : List PrefixCut := [⟨64,200171559,200171677⟩]
theorem checked60659 : checkPrefixCuts (2^48) 7954628609 10 Manual.Count131072.C060659.packed 64 cuts60659 = true := by
 decide +kernel
def cuts60660 : List PrefixCut := [⟨22,68008743,68008783⟩,
⟨64,198682116,198682233⟩]
theorem checked60660 : checkPrefixCuts (2^48) 7954759681 10 Manual.Count131072.C060660.packed 64 cuts60660 = true := by
 decide +kernel
def pointBounds60660 : List (Nat × Nat × Nat) := [(7954804736,114051900436634,114052288921080)]
theorem point_links_checked60660 : (cuts60660.take 1).map (fun c => (7954759681-1+2*2^10*c.k,114051832427891+c.lower,114052220912297+c.upper)) = pointBounds60660 := by
 decide +kernel
def cuts60661 : List PrefixCut := [⟨64,203880247,203880355⟩]
theorem checked60661 : checkPrefixCuts (2^48) 7954890753 10 Manual.Count131072.C060661.packed 64 cuts60661 = true := by
 decide +kernel
def cuts60662 : List PrefixCut := [⟨16,51341059,51341088⟩,
⟨64,204372241,204372359⟩]
theorem checked60662 : checkPrefixCuts (2^48) 7955021825 10 Manual.Count131072.C060662.packed 64 cuts60662 = true := by
 decide +kernel
def pointBounds60662 : List (Nat × Nat × Nat) := [(7955054592,114052286331313,114052674815973)]
theorem point_links_checked60662 : (cuts60662.take 1).map (fun c => (7955021825-1+2*2^10*c.k,114052234990254+c.lower,114052623474885+c.upper)) = pointBounds60662 := by
 decide +kernel
def cuts60663 : List PrefixCut := [⟨64,204545777,204545893⟩]
theorem checked60663 : checkPrefixCuts (2^48) 7955152897 10 Manual.Count131072.C060663.packed 64 cuts60663 = true := by
 decide +kernel
def cuts60664 : List PrefixCut := [⟨10,32268461,32268481⟩,
⟨64,205002372,205002491⟩]
theorem checked60664 : checkPrefixCuts (2^48) 7955283969 10 Manual.Count131072.C060664.packed 64 cuts60664 = true := by
 decide +kernel
def pointBounds60664 : List (Nat × Nat × Nat) := [(7955304448,114052676176733,114053064661618)]
theorem point_links_checked60664 : (cuts60664.take 1).map (fun c => (7955283969-1+2*2^10*c.k,114052643908272+c.lower,114053032393137+c.upper)) = pointBounds60664 := by
 decide +kernel
def cuts60665 : List PrefixCut := [⟨64,202345393,202345508⟩]
theorem checked60665 : checkPrefixCuts (2^48) 7955415041 10 Manual.Count131072.C060665.packed 64 cuts60665 = true := by
 decide +kernel
def cuts60666 : List PrefixCut := [⟨4,12454094,12454100⟩,
⟨64,202412826,202412943⟩]
theorem checked60666 : checkPrefixCuts (2^48) 7955546113 10 Manual.Count131072.C060666.packed 64 cuts60666 = true := by
 decide +kernel
def pointBounds60666 : List (Nat × Nat × Nat) := [(7955554304,114053063710131,114053452195236)]
theorem point_links_checked60666 : (cuts60666.take 1).map (fun c => (7955546113-1+2*2^10*c.k,114053051256037+c.lower,114053439741136+c.upper)) = pointBounds60666 := by
 decide +kernel
def cuts60667 : List PrefixCut := [⟨62,191547855,191547966⟩,
⟨64,197668561,197668676⟩]
theorem checked60667 : checkPrefixCuts (2^48) 7955677185 10 Manual.Count131072.C060667.packed 64 cuts60667 = true := by
 decide +kernel
def pointBounds60667 : List (Nat × Nat × Nat) := [(7955804160,114053445216718,114053833702045)]
theorem point_links_checked60667 : (cuts60667.take 1).map (fun c => (7955677185-1+2*2^10*c.k,114053253668863+c.lower,114053642154079+c.upper)) = pointBounds60667 := by
 decide +kernel
def cuts60668 : List PrefixCut := [⟨64,203998220,203998338⟩]
theorem checked60668 : checkPrefixCuts (2^48) 7955808257 10 Manual.Count131072.C060668.packed 64 cuts60668 = true := by
 decide +kernel
def cuts60669 : List PrefixCut := [⟨56,177531634,177531735⟩,
⟨64,202544355,202544469⟩]
theorem checked60669 : checkPrefixCuts (2^48) 7955939329 10 Manual.Count131072.C060669.packed 64 cuts60669 = true := by
 decide +kernel
def pointBounds60669 : List (Nat × Nat × Nat) := [(7956054016,114053832867278,114054221352828)]
theorem point_links_checked60669 : (cuts60669.take 1).map (fun c => (7955939329-1+2*2^10*c.k,114053655335644+c.lower,114054043821093+c.upper)) = pointBounds60669 := by
 decide +kernel
def cuts60670 : List PrefixCut := [⟨64,203107054,203107168⟩]
theorem checked60670 : checkPrefixCuts (2^48) 7956070401 10 Manual.Count131072.C060670.packed 64 cuts60670 = true := by
 decide +kernel
def cuts60671 : List PrefixCut := [⟨50,160615313,160615399⟩,
⟨64,206181572,206181686⟩]
theorem checked60671 : checkPrefixCuts (2^48) 7956201473 10 Manual.Count131072.C060671.packed 64 cuts60671 = true := by
 decide +kernel
def pointBounds60671 : List (Nat × Nat × Nat) := [(7956303872,114054221602366,114054610088129)]
theorem point_links_checked60671 : (cuts60671.take 1).map (fun c => (7956201473-1+2*2^10*c.k,114054060987053+c.lower,114054449472730+c.upper)) = pointBounds60671 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000020
