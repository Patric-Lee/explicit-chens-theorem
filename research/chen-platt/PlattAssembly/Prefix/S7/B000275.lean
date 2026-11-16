import PlattAssemblyKernel
import PlattCertificates.Count131072.C068800
import PlattCertificates.Count131072.C068801
import PlattCertificates.Count131072.C068802
import PlattCertificates.Count131072.C068803
import PlattCertificates.Count131072.C068804
import PlattCertificates.Count131072.C068805
import PlattCertificates.Count131072.C068806
import PlattCertificates.Count131072.C068807
import PlattCertificates.Count131072.C068808
import PlattCertificates.Count131072.C068809
import PlattCertificates.Count131072.C068810
import PlattCertificates.Count131072.C068811
import PlattCertificates.Count131072.C068812
import PlattCertificates.Count131072.C068813
import PlattCertificates.Count131072.C068814
import PlattCertificates.Count131072.C068815
import PlattCertificates.Count131072.C068816
import PlattCertificates.Count131072.C068817
import PlattCertificates.Count131072.C068818
import PlattCertificates.Count131072.C068819
import PlattCertificates.Count131072.C068820
import PlattCertificates.Count131072.C068821
import PlattCertificates.Count131072.C068822
import PlattCertificates.Count131072.C068823
import PlattCertificates.Count131072.C068824
import PlattCertificates.Count131072.C068825
import PlattCertificates.Count131072.C068826
import PlattCertificates.Count131072.C068827
import PlattCertificates.Count131072.C068828
import PlattCertificates.Count131072.C068829
import PlattCertificates.Count131072.C068830
import PlattCertificates.Count131072.C068831
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000275
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68800 : List PrefixCut := [⟨7,19312669,19312679⟩,
⟨64,178243220,178243321⟩]
theorem checked68800 : checkPrefixCuts (2^48) 9021685761 10 Manual.Count131072.C068800.packed 64 cuts68800 = true := by
 decide +kernel
def pointBounds68800 : List (Nat × Nat × Nat) := [(9021700096,115601633883062,115602023263607)]
theorem point_links_checked68800 : (cuts68800.take 1).map (fun c => (9021685761-1+2*2^10*c.k,115601614570393+c.lower,115602003950928+c.upper)) = pointBounds68800 := by
 decide +kernel
def cuts68801 : List PrefixCut := [⟨64,176056702,176056800⟩]
theorem checked68801 : checkPrefixCuts (2^48) 9021816833 10 Manual.Count131072.C068801.packed 64 cuts68801 = true := by
 decide +kernel
def cuts68802 : List PrefixCut := [⟨17,47453443,47453469⟩,
⟨64,178955624,178955726⟩]
theorem checked68802 : checkPrefixCuts (2^48) 9021947905 10 Manual.Count131072.C068802.packed 64 cuts68802 = true := by
 decide +kernel
def pointBounds68802 : List (Nat × Nat × Nat) := [(9021982720,115602016323758,115602405704518)]
theorem point_links_checked68802 : (cuts68802.take 1).map (fun c => (9021947905-1+2*2^10*c.k,115601968870315+c.lower,115602358251049+c.upper)) = pointBounds68802 := by
 decide +kernel
def cuts68803 : List PrefixCut := [⟨64,179826565,179826669⟩]
theorem checked68803 : checkPrefixCuts (2^48) 9022078977 10 Manual.Count131072.C068803.packed 64 cuts68803 = true := by
 decide +kernel
def cuts68804 : List PrefixCut := [⟨27,74313406,74313449⟩,
⟨64,177328137,177328239⟩]
theorem checked68804 : checkPrefixCuts (2^48) 9022210049 10 Manual.Count131072.C068804.packed 64 cuts68804 = true := by
 decide +kernel
def pointBounds68804 : List (Nat × Nat × Nat) := [(9022265344,115602401965910,115602791346893)]
theorem point_links_checked68804 : (cuts68804.take 1).map (fun c => (9022210049-1+2*2^10*c.k,115602327652504+c.lower,115602717033444+c.upper)) = pointBounds68804 := by
 decide +kernel
def cuts68805 : List PrefixCut := [⟨64,178885430,178885529⟩]
theorem checked68805 : checkPrefixCuts (2^48) 9022341121 10 Manual.Count131072.C068805.packed 64 cuts68805 = true := by
 decide +kernel
def cuts68806 : List PrefixCut := [⟨37,100079855,100079913⟩,
⟨64,175201591,175201697⟩]
theorem checked68806 : checkPrefixCuts (2^48) 9022472193 10 Manual.Count131072.C068806.packed 64 cuts68806 = true := by
 decide +kernel
def pointBounds68806 : List (Nat × Nat × Nat) := [(9022547968,115602783945926,115603173327125)]
theorem point_links_checked68806 : (cuts68806.take 1).map (fun c => (9022472193-1+2*2^10*c.k,115602683866071+c.lower,115603073247212+c.upper)) = pointBounds68806 := by
 decide +kernel
def cuts68807 : List PrefixCut := [⟨64,179223400,179223497⟩]
theorem checked68807 : checkPrefixCuts (2^48) 9022603265 10 Manual.Count131072.C068807.packed 64 cuts68807 = true := by
 decide +kernel
def cuts68808 : List PrefixCut := [⟨47,130929691,130929766⟩,
⟨64,179158387,179158487⟩]
theorem checked68808 : checkPrefixCuts (2^48) 9022734337 10 Manual.Count131072.C068808.packed 64 cuts68808 = true := by
 decide +kernel
def pointBounds68808 : List (Nat × Nat × Nat) := [(9022830592,115603169220753,115603558602172)]
theorem point_links_checked68808 : (cuts68808.take 1).map (fun c => (9022734337-1+2*2^10*c.k,115603038291062+c.lower,115603427672406+c.upper)) = pointBounds68808 := by
 decide +kernel
def cuts68809 : List PrefixCut := [⟨64,179498934,179499042⟩]
theorem checked68809 : checkPrefixCuts (2^48) 9022865409 10 Manual.Count131072.C068809.packed 64 cuts68809 = true := by
 decide +kernel
def cuts68810 : List PrefixCut := [⟨57,160529870,160529970⟩,
⟨64,179465144,179465255⟩]
theorem checked68810 : checkPrefixCuts (2^48) 9022996481 10 Manual.Count131072.C068810.packed 64 cuts68810 = true := by
 decide +kernel
def pointBounds68810 : List (Nat × Nat × Nat) := [(9023113216,115603557478253,115603946859905)]
theorem point_links_checked68810 : (cuts68810.take 1).map (fun c => (9022996481-1+2*2^10*c.k,115603396948383+c.lower,115603786329935+c.upper)) = pointBounds68810 := by
 decide +kernel
def cuts68811 : List PrefixCut := [⟨64,177996376,177996480⟩]
theorem checked68811 : checkPrefixCuts (2^48) 9023127553 10 Manual.Count131072.C068811.packed 64 cuts68811 = true := by
 decide +kernel
def cuts68812 : List PrefixCut := [⟨64,178368134,178368245⟩]
theorem checked68812 : checkPrefixCuts (2^48) 9023258625 10 Manual.Count131072.C068812.packed 64 cuts68812 = true := by
 decide +kernel
def cuts68813 : List PrefixCut := [⟨3,8484744,8484748⟩,
⟨64,181235359,181235464⟩]
theorem checked68813 : checkPrefixCuts (2^48) 9023389697 10 Manual.Count131072.C068813.packed 64 cuts68813 = true := by
 decide +kernel
def pointBounds68813 : List (Nat × Nat × Nat) := [(9023395840,115603941262781,115604330644663)]
theorem point_links_checked68813 : (cuts68813.take 1).map (fun c => (9023389697-1+2*2^10*c.k,115603932778037+c.lower,115604322159915+c.upper)) = pointBounds68813 := by
 decide +kernel
def cuts68814 : List PrefixCut := [⟨64,177739083,177739191⟩]
theorem checked68814 : checkPrefixCuts (2^48) 9023520769 10 Manual.Count131072.C068814.packed 64 cuts68814 = true := by
 decide +kernel
def cuts68815 : List PrefixCut := [⟨13,37400367,37400390⟩,
⟨64,178422735,178422842⟩]
theorem checked68815 : checkPrefixCuts (2^48) 9023651841 10 Manual.Count131072.C068815.packed 64 cuts68815 = true := by
 decide +kernel
def pointBounds68815 : List (Nat × Nat × Nat) := [(9023678464,115604329152846,115604718534960)]
theorem point_links_checked68815 : (cuts68815.take 1).map (fun c => (9023651841-1+2*2^10*c.k,115604291752479+c.lower,115604681134570+c.upper)) = pointBounds68815 := by
 decide +kernel
def cuts68816 : List PrefixCut := [⟨64,177203644,177203746⟩]
theorem checked68816 : checkPrefixCuts (2^48) 9023782913 10 Manual.Count131072.C068816.packed 64 cuts68816 = true := by
 decide +kernel
def cuts68817 : List PrefixCut := [⟨23,63818885,63818922⟩,
⟨64,177045124,177045227⟩]
theorem checked68817 : checkPrefixCuts (2^48) 9023913985 10 Manual.Count131072.C068817.packed 64 cuts68817 = true := by
 decide +kernel
def pointBounds68817 : List (Nat × Nat × Nat) := [(9023961088,115604711197743,115605100580080)]
theorem point_links_checked68817 : (cuts68817.take 1).map (fun c => (9023913985-1+2*2^10*c.k,115604647378858+c.lower,115605036761158+c.upper)) = pointBounds68817 := by
 decide +kernel
def cuts68818 : List PrefixCut := [⟨64,181128623,181128729⟩]
theorem checked68818 : checkPrefixCuts (2^48) 9024045057 10 Manual.Count131072.C068818.packed 64 cuts68818 = true := by
 decide +kernel
def cuts68819 : List PrefixCut := [⟨33,92419183,92419239⟩,
⟨64,179410484,179410592⟩]
theorem checked68819 : checkPrefixCuts (2^48) 9024176129 10 Manual.Count131072.C068819.packed 64 cuts68819 = true := by
 decide +kernel
def pointBounds68819 : List (Nat × Nat × Nat) := [(9024243712,115605097971788,115605487354353)]
theorem point_links_checked68819 : (cuts68819.take 1).map (fun c => (9024176129-1+2*2^10*c.k,115605005552605+c.lower,115605394935114+c.upper)) = pointBounds68819 := by
 decide +kernel
def cuts68820 : List PrefixCut := [⟨64,178784071,178784177⟩]
theorem checked68820 : checkPrefixCuts (2^48) 9024307201 10 Manual.Count131072.C068820.packed 64 cuts68820 = true := by
 decide +kernel
def cuts68821 : List PrefixCut := [⟨43,118210641,118210711⟩,
⟨64,175288190,175288290⟩]
theorem checked68821 : checkPrefixCuts (2^48) 9024438273 10 Manual.Count131072.C068821.packed 64 cuts68821 = true := by
 decide +kernel
def pointBounds68821 : List (Nat × Nat × Nat) := [(9024526336,115605481957801,115605871340594)]
theorem point_links_checked68821 : (cuts68821.take 1).map (fun c => (9024438273-1+2*2^10*c.k,115605363747160+c.lower,115605753129883+c.upper)) = pointBounds68821 := by
 decide +kernel
def cuts68822 : List PrefixCut := [⟨64,180088833,180088940⟩]
theorem checked68822 : checkPrefixCuts (2^48) 9024569345 10 Manual.Count131072.C068822.packed 64 cuts68822 = true := by
 decide +kernel
def cuts68823 : List PrefixCut := [⟨53,148335843,148335932⟩,
⟨64,178932227,178932335⟩]
theorem checked68823 : checkPrefixCuts (2^48) 9024700417 10 Manual.Count131072.C068823.packed 64 cuts68823 = true := by
 decide +kernel
def pointBounds68823 : List (Nat × Nat × Nat) := [(9024808960,115605867460026,115606256843045)]
theorem point_links_checked68823 : (cuts68823.take 1).map (fun c => (9024700417-1+2*2^10*c.k,115605719124183+c.lower,115606108507113+c.upper)) = pointBounds68823 := by
 decide +kernel
def cuts68824 : List PrefixCut := [⟨64,178867252,178867360⟩]
theorem checked68824 : checkPrefixCuts (2^48) 9024831489 10 Manual.Count131072.C068824.packed 64 cuts68824 = true := by
 decide +kernel
def cuts68825 : List PrefixCut := [⟨63,176120102,176120205⟩,
⟨64,178708709,178708813⟩]
theorem checked68825 : checkPrefixCuts (2^48) 9024962561 10 Manual.Count131072.C068825.packed 64 cuts68825 = true := by
 decide +kernel
def pointBounds68825 : List (Nat × Nat × Nat) := [(9025091584,115606253043764,115606642427013)]
theorem point_links_checked68825 : (cuts68825.take 1).map (fun c => (9024962561-1+2*2^10*c.k,115606076923662+c.lower,115606466306808+c.upper)) = pointBounds68825 := by
 decide +kernel
def cuts68826 : List PrefixCut := [⟨64,179891254,179891355⟩]
theorem checked68826 : checkPrefixCuts (2^48) 9025093633 10 Manual.Count131072.C068826.packed 64 cuts68826 = true := by
 decide +kernel
def cuts68827 : List PrefixCut := [⟨64,178734712,178734818⟩]
theorem checked68827 : checkPrefixCuts (2^48) 9025224705 10 Manual.Count131072.C068827.packed 64 cuts68827 = true := by
 decide +kernel
def cuts68828 : List PrefixCut := [⟨9,24668990,24669006⟩,
⟨64,175519855,175519960⟩]
theorem checked68828 : checkPrefixCuts (2^48) 9025355777 10 Manual.Count131072.C068828.packed 64 cuts68828 = true := by
 decide +kernel
def pointBounds68828 : List (Nat × Nat × Nat) := [(9025374208,115606638927327,115607028310800)]
theorem point_links_checked68828 : (cuts68828.take 1).map (fun c => (9025355777-1+2*2^10*c.k,115606614258337+c.lower,115607003641794+c.upper)) = pointBounds68828 := by
 decide +kernel
def cuts68829 : List PrefixCut := [⟨64,178916638,178916739⟩]
theorem checked68829 : checkPrefixCuts (2^48) 9025486849 10 Manual.Count131072.C068829.packed 64 cuts68829 = true := by
 decide +kernel
def cuts68830 : List PrefixCut := [⟨19,53203576,53203606⟩,
⟨64,179381827,179381928⟩]
theorem checked68830 : checkPrefixCuts (2^48) 9025617921 10 Manual.Count131072.C068830.packed 64 cuts68830 = true := by
 decide +kernel
def pointBounds68830 : List (Nat × Nat × Nat) := [(9025656832,115607021898406,115607411282099)]
theorem point_links_checked68830 : (cuts68830.take 1).map (fun c => (9025617921-1+2*2^10*c.k,115606968694830+c.lower,115607358078493+c.upper)) = pointBounds68830 := by
 decide +kernel
def cuts68831 : List PrefixCut := [⟨64,181655763,181655868⟩]
theorem checked68831 : checkPrefixCuts (2^48) 9025748993 10 Manual.Count131072.C068831.packed 64 cuts68831 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000275
