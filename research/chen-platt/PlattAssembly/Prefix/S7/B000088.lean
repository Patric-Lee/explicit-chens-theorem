import PlattAssemblyKernel
import PlattCertificates.Count131072.C062816
import PlattCertificates.Count131072.C062817
import PlattCertificates.Count131072.C062818
import PlattCertificates.Count131072.C062819
import PlattCertificates.Count131072.C062820
import PlattCertificates.Count131072.C062821
import PlattCertificates.Count131072.C062822
import PlattCertificates.Count131072.C062823
import PlattCertificates.Count131072.C062824
import PlattCertificates.Count131072.C062825
import PlattCertificates.Count131072.C062826
import PlattCertificates.Count131072.C062827
import PlattCertificates.Count131072.C062828
import PlattCertificates.Count131072.C062829
import PlattCertificates.Count131072.C062830
import PlattCertificates.Count131072.C062831
import PlattCertificates.Count131072.C062832
import PlattCertificates.Count131072.C062833
import PlattCertificates.Count131072.C062834
import PlattCertificates.Count131072.C062835
import PlattCertificates.Count131072.C062836
import PlattCertificates.Count131072.C062837
import PlattCertificates.Count131072.C062838
import PlattCertificates.Count131072.C062839
import PlattCertificates.Count131072.C062840
import PlattCertificates.Count131072.C062841
import PlattCertificates.Count131072.C062842
import PlattCertificates.Count131072.C062843
import PlattCertificates.Count131072.C062844
import PlattCertificates.Count131072.C062845
import PlattCertificates.Count131072.C062846
import PlattCertificates.Count131072.C062847
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000088
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62816 : List PrefixCut := [⟨64,196239970,196240083⟩]
theorem checked62816 : checkPrefixCuts (2^48) 8237350913 10 Manual.Count131072.C062816.packed 64 cuts62816 = true := by
 decide +kernel
def cuts62817 : List PrefixCut := [⟨8,24192348,24192362⟩,
⟨64,196100169,196100280⟩]
theorem checked62817 : checkPrefixCuts (2^48) 8237481985 10 Manual.Count131072.C062817.packed 64 cuts62817 = true := by
 decide +kernel
def pointBounds62817 : List (Nat × Nat × Nat) := [(8237498368,114482795339585,114483184071170)]
theorem point_links_checked62817 : (cuts62817.take 1).map (fun c => (8237481985-1+2*2^10*c.k,114482771147237+c.lower,114483159878808+c.upper)) = pointBounds62817 := by
 decide +kernel
def cuts62818 : List PrefixCut := [⟨64,193602686,193602795⟩]
theorem checked62818 : checkPrefixCuts (2^48) 8237613057 10 Manual.Count131072.C062818.packed 64 cuts62818 = true := by
 decide +kernel
def cuts62819 : List PrefixCut := [⟨6,18519546,18519558⟩,
⟨64,195786405,195786521⟩]
theorem checked62819 : checkPrefixCuts (2^48) 8237744129 10 Manual.Count131072.C062819.packed 64 cuts62819 = true := by
 decide +kernel
def pointBounds62819 : List (Nat × Nat × Nat) := [(8237756416,114483179369638,114483568101441)]
theorem point_links_checked62819 : (cuts62819.take 1).map (fun c => (8237744129-1+2*2^10*c.k,114483160850092+c.lower,114483549581883+c.upper)) = pointBounds62819 := by
 decide +kernel
def cuts62820 : List PrefixCut := [⟨64,197935882,197936001⟩]
theorem checked62820 : checkPrefixCuts (2^48) 8237875201 10 Manual.Count131072.C062820.packed 64 cuts62820 = true := by
 decide +kernel
def cuts62821 : List PrefixCut := [⟨4,12027075,12027081⟩,
⟨64,195472667,195472777⟩]
theorem checked62821 : checkPrefixCuts (2^48) 8238006273 10 Manual.Count131072.C062821.packed 64 cuts62821 = true := by
 decide +kernel
def pointBounds62821 : List (Nat × Nat × Nat) := [(8238014464,114483566599454,114483955331486)]
theorem point_links_checked62821 : (cuts62821.take 1).map (fun c => (8238006273-1+2*2^10*c.k,114483554572379+c.lower,114483943304405+c.upper)) = pointBounds62821 := by
 decide +kernel
def cuts62822 : List PrefixCut := [⟨64,197553728,197553843⟩]
theorem checked62822 : checkPrefixCuts (2^48) 8238137345 10 Manual.Count131072.C062822.packed 64 cuts62822 = true := by
 decide +kernel
def cuts62823 : List PrefixCut := [⟨2,6389182,6389185⟩,
⟨64,197516451,197516561⟩]
theorem checked62823 : checkPrefixCuts (2^48) 8238268417 10 Manual.Count131072.C062823.packed 64 cuts62823 = true := by
 decide +kernel
def pointBounds62823 : List (Nat × Nat × Nat) := [(8238272512,114483953987956,114484342720210)]
theorem point_links_checked62823 : (cuts62823.take 1).map (fun c => (8238268417-1+2*2^10*c.k,114483947598774+c.lower,114484336331025+c.upper)) = pointBounds62823 := by
 decide +kernel
def cuts62824 : List PrefixCut := [⟨64,197581639,197581745⟩]
theorem checked62824 : checkPrefixCuts (2^48) 8238399489 10 Manual.Count131072.C062824.packed 64 cuts62824 = true := by
 decide +kernel
def pointBounds62824 : List (Nat × Nat × Nat) := [(8238530560,114484342696864,114484731429331)]
theorem point_links_checked62824 : (cuts62824.take 1).map (fun c => (8238399489-1+2*2^10*c.k,114484145115225+c.lower,114484533847586+c.upper)) = pointBounds62824 := by
 decide +kernel
def cuts62825 : List PrefixCut := [⟨64,197373499,197373613⟩]
theorem checked62825 : checkPrefixCuts (2^48) 8238530561 10 Manual.Count131072.C062825.packed 64 cuts62825 = true := by
 decide +kernel
def cuts62826 : List PrefixCut := [⟨62,191425706,191425817⟩,
⟨64,198258624,198258739⟩]
theorem checked62826 : checkPrefixCuts (2^48) 8238661633 10 Manual.Count131072.C062826.packed 64 cuts62826 = true := by
 decide +kernel
def pointBounds62826 : List (Nat × Nat × Nat) := [(8238788608,114484731496069,114485120228761)]
theorem point_links_checked62826 : (cuts62826.take 1).map (fun c => (8238661633-1+2*2^10*c.k,114484540070363+c.lower,114484928802944+c.upper)) = pointBounds62826 := by
 decide +kernel
def cuts62827 : List PrefixCut := [⟨64,194804893,194805011⟩]
theorem checked62827 : checkPrefixCuts (2^48) 8238792705 10 Manual.Count131072.C062827.packed 64 cuts62827 = true := by
 decide +kernel
def cuts62828 : List PrefixCut := [⟨60,181102209,181102318⟩,
⟨64,192991111,192991226⟩]
theorem checked62828 : checkPrefixCuts (2^48) 8238923777 10 Manual.Count131072.C062828.packed 64 cuts62828 = true := by
 decide +kernel
def pointBounds62828 : List (Nat × Nat × Nat) := [(8239046656,114485114236089,114485502969012)]
theorem point_links_checked62828 : (cuts62828.take 1).map (fun c => (8238923777-1+2*2^10*c.k,114484933133880+c.lower,114485321866694+c.upper)) = pointBounds62828 := by
 decide +kernel
def cuts62829 : List PrefixCut := [⟨64,196165211,196165325⟩]
theorem checked62829 : checkPrefixCuts (2^48) 8239054849 10 Manual.Count131072.C062829.packed 64 cuts62829 = true := by
 decide +kernel
def cuts62830 : List PrefixCut := [⟨58,174195631,174195732⟩,
⟨64,192950806,192950917⟩]
theorem checked62830 : checkPrefixCuts (2^48) 8239185921 10 Manual.Count131072.C062830.packed 64 cuts62830 = true := by
 decide +kernel
def pointBounds62830 : List (Nat × Nat × Nat) := [(8239304704,114485496485833,114485885218977)]
theorem point_links_checked62830 : (cuts62830.take 1).map (fun c => (8239185921-1+2*2^10*c.k,114485322290202+c.lower,114485711023245+c.upper)) = pointBounds62830 := by
 decide +kernel
def cuts62831 : List PrefixCut := [⟨64,194690016,194690131⟩]
theorem checked62831 : checkPrefixCuts (2^48) 8239316993 10 Manual.Count131072.C062831.packed 64 cuts62831 = true := by
 decide +kernel
def cuts62832 : List PrefixCut := [⟨56,170124896,170124993⟩,
⟨64,194721071,194721182⟩]
theorem checked62832 : checkPrefixCuts (2^48) 8239448065 10 Manual.Count131072.C062832.packed 64 cuts62832 = true := by
 decide +kernel
def pointBounds62832 : List (Nat × Nat × Nat) := [(8239562752,114485880055920,114486268789286)]
theorem point_links_checked62832 : (cuts62832.take 1).map (fun c => (8239448065-1+2*2^10*c.k,114485709931024+c.lower,114486098664293+c.upper)) = pointBounds62832 := by
 decide +kernel
def cuts62833 : List PrefixCut := [⟨64,195947774,195947889⟩]
theorem checked62833 : checkPrefixCuts (2^48) 8239579137 10 Manual.Count131072.C062833.packed 64 cuts62833 = true := by
 decide +kernel
def cuts62834 : List PrefixCut := [⟨54,164312241,164312333⟩,
⟨64,196388741,196388850⟩]
theorem checked62834 : checkPrefixCuts (2^48) 8239710209 10 Manual.Count131072.C062834.packed 64 cuts62834 = true := by
 decide +kernel
def pointBounds62834 : List (Nat × Nat × Nat) := [(8239820800,114486264912110,114486653645697)]
theorem point_links_checked62834 : (cuts62834.take 1).map (fun c => (8239710209-1+2*2^10*c.k,114486100599869+c.lower,114486489333364+c.upper)) = pointBounds62834 := by
 decide +kernel
def cuts62835 : List PrefixCut := [⟨64,198571860,198571974⟩]
theorem checked62835 : checkPrefixCuts (2^48) 8239841281 10 Manual.Count131072.C062835.packed 64 cuts62835 = true := by
 decide +kernel
def cuts62836 : List PrefixCut := [⟨52,161061899,161061994⟩,
⟨64,197509762,197509878⟩]
theorem checked62836 : checkPrefixCuts (2^48) 8239972353 10 Manual.Count131072.C062836.packed 64 cuts62836 = true := by
 decide +kernel
def pointBounds62836 : List (Nat × Nat × Nat) := [(8240078848,114486656622369,114487045356182)]
theorem point_links_checked62836 : (cuts62836.take 1).map (fun c => (8239972353-1+2*2^10*c.k,114486495560470+c.lower,114486884294188+c.upper)) = pointBounds62836 := by
 decide +kernel
def cuts62837 : List PrefixCut := [⟨64,199556155,199556269⟩]
theorem checked62837 : checkPrefixCuts (2^48) 8240103425 10 Manual.Count131072.C062837.packed 64 cuts62837 = true := by
 decide +kernel
def cuts62838 : List PrefixCut := [⟨50,154976622,154976707⟩,
⟨64,198118330,198118435⟩]
theorem checked62838 : checkPrefixCuts (2^48) 8240234497 10 Manual.Count131072.C062838.packed 64 cuts62838 = true := by
 decide +kernel
def pointBounds62838 : List (Nat × Nat × Nat) := [(8240336896,114487047603009,114487436337042)]
theorem point_links_checked62838 : (cuts62838.take 1).map (fun c => (8240234497-1+2*2^10*c.k,114486892626387+c.lower,114487281360335+c.upper)) = pointBounds62838 := by
 decide +kernel
def cuts62839 : List PrefixCut := [⟨64,194801847,194801959⟩]
theorem checked62839 : checkPrefixCuts (2^48) 8240365569 10 Manual.Count131072.C062839.packed 64 cuts62839 = true := by
 decide +kernel
def cuts62840 : List PrefixCut := [⟨48,146876443,146876527⟩,
⟨64,195789326,195789437⟩]
theorem checked62840 : checkPrefixCuts (2^48) 8240496641 10 Manual.Count131072.C062840.packed 64 cuts62840 = true := by
 decide +kernel
def pointBounds62840 : List (Nat × Nat × Nat) := [(8240594944,114487432423007,114487821157256)]
theorem point_links_checked62840 : (cuts62840.take 1).map (fun c => (8240496641-1+2*2^10*c.k,114487285546564+c.lower,114487674280729+c.upper)) = pointBounds62840 := by
 decide +kernel
def cuts62841 : List PrefixCut := [⟨64,198143022,198143142⟩]
theorem checked62841 : checkPrefixCuts (2^48) 8240627713 10 Manual.Count131072.C062841.packed 64 cuts62841 = true := by
 decide +kernel
def cuts62842 : List PrefixCut := [⟨46,140177181,140177265⟩,
⟨64,195339060,195339177⟩]
theorem checked62842 : checkPrefixCuts (2^48) 8240758785 10 Manual.Count131072.C062842.packed 64 cuts62842 = true := by
 decide +kernel
def pointBounds62842 : List (Nat × Nat × Nat) := [(8240852992,114487819656093,114488208390573)]
theorem point_links_checked62842 : (cuts62842.take 1).map (fun c => (8240758785-1+2*2^10*c.k,114487679478912+c.lower,114488068213308+c.upper)) = pointBounds62842 := by
 decide +kernel
def cuts62843 : List PrefixCut := [⟨64,194721159,194721272⟩]
theorem checked62843 : checkPrefixCuts (2^48) 8240889857 10 Manual.Count131072.C062843.packed 64 cuts62843 = true := by
 decide +kernel
def cuts62844 : List PrefixCut := [⟨44,133785748,133785821⟩,
⟨64,193659262,193659369⟩]
theorem checked62844 : checkPrefixCuts (2^48) 8241020929 10 Manual.Count131072.C062844.packed 64 cuts62844 = true := by
 decide +kernel
def pointBounds62844 : List (Nat × Nat × Nat) := [(8241111040,114488203324879,114488592059578)]
theorem point_links_checked62844 : (cuts62844.take 1).map (fun c => (8241020929-1+2*2^10*c.k,114488069539131+c.lower,114488458273757+c.upper)) = pointBounds62844 := by
 decide +kernel
def cuts62845 : List PrefixCut := [⟨64,194919881,194919996⟩]
theorem checked62845 : checkPrefixCuts (2^48) 8241152001 10 Manual.Count131072.C062845.packed 64 cuts62845 = true := by
 decide +kernel
def cuts62846 : List PrefixCut := [⟨42,131288277,131288350⟩,
⟨64,197614967,197615079⟩]
theorem checked62846 : checkPrefixCuts (2^48) 8241283073 10 Manual.Count131072.C062846.packed 64 cuts62846 = true := by
 decide +kernel
def pointBounds62846 : List (Nat × Nat × Nat) := [(8241369088,114488589406551,114488978141472)]
theorem point_links_checked62846 : (cuts62846.take 1).map (fun c => (8241283073-1+2*2^10*c.k,114488458118274+c.lower,114488846853122+c.upper)) = pointBounds62846 := by
 decide +kernel
def cuts62847 : List PrefixCut := [⟨64,198363191,198363310⟩]
theorem checked62847 : checkPrefixCuts (2^48) 8241414145 10 Manual.Count131072.C062847.packed 64 cuts62847 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000088
