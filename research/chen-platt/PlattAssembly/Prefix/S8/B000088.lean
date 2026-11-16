import PlattAssemblyKernel
import PlattCertificates.Count131072.C072816
import PlattCertificates.Count131072.C072817
import PlattCertificates.Count131072.C072818
import PlattCertificates.Count131072.C072819
import PlattCertificates.Count131072.C072820
import PlattCertificates.Count131072.C072821
import PlattCertificates.Count131072.C072822
import PlattCertificates.Count131072.C072823
import PlattCertificates.Count131072.C072824
import PlattCertificates.Count131072.C072825
import PlattCertificates.Count131072.C072826
import PlattCertificates.Count131072.C072827
import PlattCertificates.Count131072.C072828
import PlattCertificates.Count131072.C072829
import PlattCertificates.Count131072.C072830
import PlattCertificates.Count131072.C072831
import PlattCertificates.Count131072.C072832
import PlattCertificates.Count131072.C072833
import PlattCertificates.Count131072.C072834
import PlattCertificates.Count131072.C072835
import PlattCertificates.Count131072.C072836
import PlattCertificates.Count131072.C072837
import PlattCertificates.Count131072.C072838
import PlattCertificates.Count131072.C072839
import PlattCertificates.Count131072.C072840
import PlattCertificates.Count131072.C072841
import PlattCertificates.Count131072.C072842
import PlattCertificates.Count131072.C072843
import PlattCertificates.Count131072.C072844
import PlattCertificates.Count131072.C072845
import PlattCertificates.Count131072.C072846
import PlattCertificates.Count131072.C072847
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000088
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72816 : List PrefixCut := [⟨64,166471099,166471196⟩]
theorem checked72816 : checkPrefixCuts (2^48) 9548070913 10 Manual.Count131072.C072816.packed 64 cuts72816 = true := by
 decide +kernel
def cuts72817 : List PrefixCut := [⟨42,112109501,112109569⟩,
⟨64,169180892,169180995⟩]
theorem checked72817 : checkPrefixCuts (2^48) 9548201985 10 Manual.Count131072.C072817.packed 64 cuts72817 = true := by
 decide +kernel
def pointBounds72817 : List (Nat × Nat × Nat) := [(9548288000,116297336761283,116297726552706)]
theorem point_links_checked72817 : (cuts72817.take 1).map (fun c => (9548201985-1+2*2^10*c.k,116297224651782+c.lower,116297614443137+c.upper)) = pointBounds72817 := by
 decide +kernel
def cuts72818 : List PrefixCut := [⟨64,165169469,165169559⟩]
theorem checked72818 : checkPrefixCuts (2^48) 9548333057 10 Manual.Count131072.C072818.packed 64 cuts72818 = true := by
 decide +kernel
def cuts72819 : List PrefixCut := [⟨60,158151409,158151507⟩,
⟨64,168881460,168881563⟩]
theorem checked72819 : checkPrefixCuts (2^48) 9548464129 10 Manual.Count131072.C072819.packed 64 cuts72819 = true := by
 decide +kernel
def pointBounds72819 : List (Nat × Nat × Nat) := [(9548587008,116297717153552,116298106945198)]
theorem point_links_checked72819 : (cuts72819.take 1).map (fun c => (9548464129-1+2*2^10*c.k,116297559002143+c.lower,116297948793691+c.upper)) = pointBounds72819 := by
 decide +kernel
def cuts72820 : List PrefixCut := [⟨64,166344042,166344147⟩]
theorem checked72820 : checkPrefixCuts (2^48) 9548595201 10 Manual.Count131072.C072820.packed 64 cuts72820 = true := by
 decide +kernel
def cuts72821 : List PrefixCut := [⟨64,168582049,168582147⟩]
theorem checked72821 : checkPrefixCuts (2^48) 9548726273 10 Manual.Count131072.C072821.packed 64 cuts72821 = true := by
 decide +kernel
def cuts72822 : List PrefixCut := [⟨14,36640277,36640296⟩,
⟨64,168196532,168196630⟩]
theorem checked72822 : checkPrefixCuts (2^48) 9548857345 10 Manual.Count131072.C072822.packed 64 cuts72822 = true := by
 decide +kernel
def pointBounds72822 : List (Nat × Nat × Nat) := [(9548886016,116298099449971,116298489241844)]
theorem point_links_checked72822 : (cuts72822.take 1).map (fun c => (9548857345-1+2*2^10*c.k,116298062809694+c.lower,116298452601548+c.upper)) = pointBounds72822 := by
 decide +kernel
def cuts72823 : List PrefixCut := [⟨64,169343818,169343921⟩]
theorem checked72823 : checkPrefixCuts (2^48) 9548988417 10 Manual.Count131072.C072823.packed 64 cuts72823 = true := by
 decide +kernel
def cuts72824 : List PrefixCut := [⟨32,84332060,84332106⟩,
⟨64,168015063,168015163⟩]
theorem checked72824 : checkPrefixCuts (2^48) 9549119489 10 Manual.Count131072.C072824.packed 64 cuts72824 = true := by
 decide +kernel
def pointBounds72824 : List (Nat × Nat × Nat) := [(9549185024,116298484682104,116298874474205)]
theorem point_links_checked72824 : (cuts72824.take 1).map (fun c => (9549119489-1+2*2^10*c.k,116298400350044+c.lower,116298790142099+c.upper)) = pointBounds72824 := by
 decide +kernel
def cuts72825 : List PrefixCut := [⟨64,167482188,167482292⟩]
theorem checked72825 : checkPrefixCuts (2^48) 9549250561 10 Manual.Count131072.C072825.packed 64 cuts72825 = true := by
 decide +kernel
def cuts72826 : List PrefixCut := [⟨50,130665154,130665236⟩,
⟨64,167951485,167951586⟩]
theorem checked72826 : checkPrefixCuts (2^48) 9549381633 10 Manual.Count131072.C072826.packed 64 cuts72826 = true := by
 decide +kernel
def pointBounds72826 : List (Nat × Nat × Nat) := [(9549484032,116298866512449,116299256304790)]
theorem point_links_checked72826 : (cuts72826.take 1).map (fun c => (9549381633-1+2*2^10*c.k,116298735847295+c.lower,116299125639554+c.upper)) = pointBounds72826 := by
 decide +kernel
def cuts72827 : List PrefixCut := [⟨64,167507057,167507165⟩]
theorem checked72827 : checkPrefixCuts (2^48) 9549512705 10 Manual.Count131072.C072827.packed 64 cuts72827 = true := by
 decide +kernel
def cuts72828 : List PrefixCut := [⟨64,166708954,166709048⟩]
theorem checked72828 : checkPrefixCuts (2^48) 9549643777 10 Manual.Count131072.C072828.packed 64 cuts72828 = true := by
 decide +kernel
def cuts72829 : List PrefixCut := [⟨4,10728716,10728722⟩,
⟨64,168298277,168298385⟩]
theorem checked72829 : checkPrefixCuts (2^48) 9549774849 10 Manual.Count131072.C072829.packed 64 cuts72829 = true := by
 decide +kernel
def pointBounds72829 : List (Nat × Nat × Nat) := [(9549783040,116299248743507,116299638536075)]
theorem point_links_checked72829 : (cuts72829.take 1).map (fun c => (9549774849-1+2*2^10*c.k,116299238014791+c.lower,116299627807353+c.upper)) = pointBounds72829 := by
 decide +kernel
def cuts72830 : List PrefixCut := [⟨64,169887552,169887653⟩]
theorem checked72830 : checkPrefixCuts (2^48) 9549905921 10 Manual.Count131072.C072830.packed 64 cuts72830 = true := by
 decide +kernel
def cuts72831 : List PrefixCut := [⟨22,58151469,58151502⟩,
⟨64,170032585,170032687⟩]
theorem checked72831 : checkPrefixCuts (2^48) 9550036993 10 Manual.Count131072.C072831.packed 64 cuts72831 = true := by
 decide +kernel
def pointBounds72831 : List (Nat × Nat × Nat) := [(9550082048,116299634352089,116300024144893)]
theorem point_links_checked72831 : (cuts72831.take 1).map (fun c => (9550036993-1+2*2^10*c.k,116299576200620+c.lower,116299965993391+c.upper)) = pointBounds72831 := by
 decide +kernel
def cuts72832 : List PrefixCut := [⟨64,166522959,166523060⟩]
theorem checked72832 : checkPrefixCuts (2^48) 9550168065 10 Manual.Count131072.C072832.packed 64 cuts72832 = true := by
 decide +kernel
def cuts72833 : List PrefixCut := [⟨40,104923032,104923090⟩,
⟨64,169821608,169821705⟩]
theorem checked72833 : checkPrefixCuts (2^48) 9550299137 10 Manual.Count131072.C072833.packed 64 cuts72833 = true := by
 decide +kernel
def pointBounds72833 : List (Nat × Nat × Nat) := [(9550381056,116300017679196,116300407472228)]
theorem point_links_checked72833 : (cuts72833.take 1).map (fun c => (9550299137-1+2*2^10*c.k,116299912756164+c.lower,116300302549138+c.upper)) = pointBounds72833 := by
 decide +kernel
def cuts72834 : List PrefixCut := [⟨64,168080421,168080513⟩]
theorem checked72834 : checkPrefixCuts (2^48) 9550430209 10 Manual.Count131072.C072834.packed 64 cuts72834 = true := by
 decide +kernel
def cuts72835 : List PrefixCut := [⟨58,152399167,152399262⟩,
⟨64,168048636,168048740⟩]
theorem checked72835 : checkPrefixCuts (2^48) 9550561281 10 Manual.Count131072.C072835.packed 64 cuts72835 = true := by
 decide +kernel
def pointBounds72835 : List (Nat × Nat × Nat) := [(9550680064,116300403057360,116300792850618)]
theorem point_links_checked72835 : (cuts72835.take 1).map (fun c => (9550561281-1+2*2^10*c.k,116300250658193+c.lower,116300640451356+c.upper)) = pointBounds72835 := by
 decide +kernel
def cuts72836 : List PrefixCut := [⟨64,166896945,166897048⟩]
theorem checked72836 : checkPrefixCuts (2^48) 9550692353 10 Manual.Count131072.C072836.packed 64 cuts72836 = true := by
 decide +kernel
def cuts72837 : List PrefixCut := [⟨64,167660902,167660999⟩]
theorem checked72837 : checkPrefixCuts (2^48) 9550823425 10 Manual.Count131072.C072837.packed 64 cuts72837 = true := by
 decide +kernel
def cuts72838 : List PrefixCut := [⟨12,31681140,31681156⟩,
⟨64,169250023,169250116⟩]
theorem checked72838 : checkPrefixCuts (2^48) 9550954497 10 Manual.Count131072.C072838.packed 64 cuts72838 = true := by
 decide +kernel
def pointBounds72838 : List (Nat × Nat × Nat) := [(9550979072,116300784945816,116301174739299)]
theorem point_links_checked72838 : (cuts72838.take 1).map (fun c => (9550954497-1+2*2^10*c.k,116300753264676+c.lower,116301143058143+c.upper)) = pointBounds72838 := by
 decide +kernel
def cuts72839 : List PrefixCut := [⟨64,170338097,170338196⟩]
theorem checked72839 : checkPrefixCuts (2^48) 9551085569 10 Manual.Count131072.C072839.packed 64 cuts72839 = true := by
 decide +kernel
def cuts72840 : List PrefixCut := [⟨30,78891090,78891134⟩,
⟨64,168154988,168155087⟩]
theorem checked72840 : checkPrefixCuts (2^48) 9551216641 10 Manual.Count131072.C072840.packed 64 cuts72840 = true := by
 decide +kernel
def pointBounds72840 : List (Nat × Nat × Nat) := [(9551278080,116301171743886,116301561537589)]
theorem point_links_checked72840 : (cuts72840.take 1).map (fun c => (9551216641-1+2*2^10*c.k,116301092852796+c.lower,116301482646455+c.upper)) = pointBounds72840 := by
 decide +kernel
def cuts72841 : List PrefixCut := [⟨64,168182146,168182246⟩]
theorem checked72841 : checkPrefixCuts (2^48) 9551347713 10 Manual.Count131072.C072841.packed 64 cuts72841 = true := by
 decide +kernel
def cuts72842 : List PrefixCut := [⟨48,126098271,126098339⟩,
⟨64,167531537,167531628⟩]
theorem checked72842 : checkPrefixCuts (2^48) 9551478785 10 Manual.Count131072.C072842.packed 64 cuts72842 = true := by
 decide +kernel
def pointBounds72842 : List (Nat × Nat × Nat) := [(9551577088,116301555288201,116301945082127)]
theorem point_links_checked72842 : (cuts72842.take 1).map (fun c => (9551478785-1+2*2^10*c.k,116301429189930+c.lower,116301818983788+c.upper)) = pointBounds72842 := by
 decide +kernel
def cuts72843 : List PrefixCut := [⟨64,167264009,167264109⟩]
theorem checked72843 : checkPrefixCuts (2^48) 9551609857 10 Manual.Count131072.C072843.packed 64 cuts72843 = true := by
 decide +kernel
def cuts72844 : List PrefixCut := [⟨64,167320640,167320742⟩]
theorem checked72844 : checkPrefixCuts (2^48) 9551740929 10 Manual.Count131072.C072844.packed 64 cuts72844 = true := by
 decide +kernel
def cuts72845 : List PrefixCut := [⟨2,5245309,5245312⟩,
⟨64,170324073,170324164⟩]
theorem checked72845 : checkPrefixCuts (2^48) 9551872001 10 Manual.Count131072.C072845.packed 64 cuts72845 = true := by
 decide +kernel
def pointBounds72845 : List (Nat × Nat × Nat) := [(9551876096,116301936551425,116302326345579)]
theorem point_links_checked72845 : (cuts72845.take 1).map (fun c => (9551872001-1+2*2^10*c.k,116301931306116+c.lower,116302321100267+c.upper)) = pointBounds72845 := by
 decide +kernel
def cuts72846 : List PrefixCut := [⟨64,170203869,170203969⟩]
theorem checked72846 : checkPrefixCuts (2^48) 9552003073 10 Manual.Count131072.C072846.packed 64 cuts72846 = true := by
 decide +kernel
def cuts72847 : List PrefixCut := [⟨20,50801388,50801420⟩,
⟨64,167696817,167696916⟩]
theorem checked72847 : checkPrefixCuts (2^48) 9552134145 10 Manual.Count131072.C072847.packed 64 cuts72847 = true := by
 decide +kernel
def pointBounds72847 : List (Nat × Nat × Nat) := [(9552175104,116302322635446,116302712429820)]
theorem point_links_checked72847 : (cuts72847.take 1).map (fun c => (9552134145-1+2*2^10*c.k,116302271834058+c.lower,116302661628400+c.upper)) = pointBounds72847 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000088
