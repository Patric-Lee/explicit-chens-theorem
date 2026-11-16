import PlattAssemblyKernel
import PlattCertificates.Count131072.C043808
import PlattCertificates.Count131072.C043809
import PlattCertificates.Count131072.C043810
import PlattCertificates.Count131072.C043811
import PlattCertificates.Count131072.C043812
import PlattCertificates.Count131072.C043813
import PlattCertificates.Count131072.C043814
import PlattCertificates.Count131072.C043815
import PlattCertificates.Count131072.C043816
import PlattCertificates.Count131072.C043817
import PlattCertificates.Count131072.C043818
import PlattCertificates.Count131072.C043819
import PlattCertificates.Count131072.C043820
import PlattCertificates.Count131072.C043821
import PlattCertificates.Count131072.C043822
import PlattCertificates.Count131072.C043823
import PlattCertificates.Count131072.C043824
import PlattCertificates.Count131072.C043825
import PlattCertificates.Count131072.C043826
import PlattCertificates.Count131072.C043827
import PlattCertificates.Count131072.C043828
import PlattCertificates.Count131072.C043829
import PlattCertificates.Count131072.C043830
import PlattCertificates.Count131072.C043831
import PlattCertificates.Count131072.C043832
import PlattCertificates.Count131072.C043833
import PlattCertificates.Count131072.C043834
import PlattCertificates.Count131072.C043835
import PlattCertificates.Count131072.C043836
import PlattCertificates.Count131072.C043837
import PlattCertificates.Count131072.C043838
import PlattCertificates.Count131072.C043839
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000119
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts43808 : List PrefixCut := [⟨64,287598206,287598370⟩]
theorem checked43808 : checkPrefixCuts (2^48) 5745934337 10 Manual.Count131072.C043808.packed 64 cuts43808 = true := by
 decide +kernel
def cuts43809 : List PrefixCut := [⟨22,97285171,97285228⟩,
⟨64,285779163,285779328⟩]
theorem checked43809 : checkPrefixCuts (2^48) 5746065409 10 Manual.Count131072.C043809.packed 64 cuts43809 = true := by
 decide +kernel
def pointBounds43809 : List (Nat × Nat × Nat) := [(5746110464,110007213069518,110007599244738)]
theorem point_links_checked43809 : (cuts43809.take 1).map (fun c => (5746065409-1+2*2^10*c.k,110007115784347+c.lower,110007501959510+c.upper)) = pointBounds43809 := by
 decide +kernel
def cuts43810 : List PrefixCut := [⟨46,204019006,204019127⟩,
⟨64,283421418,283421583⟩]
theorem checked43810 : checkPrefixCuts (2^48) 5746196481 10 Manual.Count131072.C043810.packed 64 cuts43810 = true := by
 decide +kernel
def pointBounds43810 : List (Nat × Nat × Nat) := [(5746290688,110007605582516,110007991757965)]
theorem point_links_checked43810 : (cuts43810.take 1).map (fun c => (5746196481-1+2*2^10*c.k,110007401563510+c.lower,110007787738838+c.upper)) = pointBounds43810 := by
 decide +kernel
def cuts43811 : List PrefixCut := [⟨64,288019364,288019531⟩]
theorem checked43811 : checkPrefixCuts (2^48) 5746327553 10 Manual.Count131072.C043811.packed 64 cuts43811 = true := by
 decide +kernel
def cuts43812 : List PrefixCut := [⟨6,25813657,25813672⟩,
⟨64,282918656,282918822⟩]
theorem checked43812 : checkPrefixCuts (2^48) 5746458625 10 Manual.Count131072.C043812.packed 64 cuts43812 = true := by
 decide +kernel
def pointBounds43812 : List (Nat × Nat × Nat) := [(5746470912,110007998817949,110008384993624)]
theorem point_links_checked43812 : (cuts43812.take 1).map (fun c => (5746458625-1+2*2^10*c.k,110007973004292+c.lower,110008359179952+c.upper)) = pointBounds43812 := by
 decide +kernel
def cuts43813 : List PrefixCut := [⟨30,133668997,133669076⟩,
⟨64,288985802,288985970⟩]
theorem checked43813 : checkPrefixCuts (2^48) 5746589697 10 Manual.Count131072.C043813.packed 64 cuts43813 = true := by
 decide +kernel
def pointBounds43813 : List (Nat × Nat × Nat) := [(5746651136,110008389591945,110008775767850)]
theorem point_links_checked43813 : (cuts43813.take 1).map (fun c => (5746589697-1+2*2^10*c.k,110008255922948+c.lower,110008642098774+c.upper)) = pointBounds43813 := by
 decide +kernel
def cuts43814 : List PrefixCut := [⟨54,243477652,243477788⟩,
⟨64,288244510,288244671⟩]
theorem checked43814 : checkPrefixCuts (2^48) 5746720769 10 Manual.Count131072.C043814.packed 64 cuts43814 = true := by
 decide +kernel
def pointBounds43814 : List (Nat × Nat × Nat) := [(5746831360,110008788386402,110009174562532)]
theorem point_links_checked43814 : (cuts43814.take 1).map (fun c => (5746720769-1+2*2^10*c.k,110008544908750+c.lower,110008931084744+c.upper)) = pointBounds43814 := by
 decide +kernel
def cuts43815 : List PrefixCut := [⟨64,283927842,283928006⟩]
theorem checked43815 : checkPrefixCuts (2^48) 5746851841 10 Manual.Count131072.C043815.packed 64 cuts43815 = true := by
 decide +kernel
def cuts43816 : List PrefixCut := [⟨14,61662964,61663000⟩,
⟨64,284117313,284117477⟩]
theorem checked43816 : checkPrefixCuts (2^48) 5746982913 10 Manual.Count131072.C043816.packed 64 cuts43816 = true := by
 decide +kernel
def pointBounds43816 : List (Nat × Nat × Nat) := [(5747011584,110009178744066,110009564920421)]
theorem point_links_checked43816 : (cuts43816.take 1).map (fun c => (5746982913-1+2*2^10*c.k,110009117081102+c.lower,110009503257421+c.upper)) = pointBounds43816 := by
 decide +kernel
def cuts43817 : List PrefixCut := [⟨38,169948129,169948231⟩,
⟨64,285873964,285874134⟩]
theorem checked43817 : checkPrefixCuts (2^48) 5747113985 10 Manual.Count131072.C043817.packed 64 cuts43817 = true := by
 decide +kernel
def pointBounds43817 : List (Nat × Nat × Nat) := [(5747191808,110009571146544,110009957323129)]
theorem point_links_checked43817 : (cuts43817.take 1).map (fun c => (5747113985-1+2*2^10*c.k,110009401198415+c.lower,110009787374898+c.upper)) = pointBounds43817 := by
 decide +kernel
def cuts43818 : List PrefixCut := [⟨62,283271861,283272027⟩,
⟨64,291891377,291891548⟩]
theorem checked43818 : checkPrefixCuts (2^48) 5747245057 10 Manual.Count131072.C043818.packed 64 cuts43818 = true := by
 decide +kernel
def pointBounds43818 : List (Nat × Nat × Nat) := [(5747372032,110009970344240,110010356521059)]
theorem point_links_checked43818 : (cuts43818.take 1).map (fun c => (5747245057-1+2*2^10*c.k,110009687072379+c.lower,110010073249032+c.upper)) = pointBounds43818 := by
 decide +kernel
def cuts43819 : List PrefixCut := [⟨64,287477065,287477227⟩]
theorem checked43819 : checkPrefixCuts (2^48) 5747376129 10 Manual.Count131072.C043819.packed 64 cuts43819 = true := by
 decide +kernel
def cuts43820 : List PrefixCut := [⟨22,98485091,98485147⟩,
⟨64,280124617,280124779⟩]
theorem checked43820 : checkPrefixCuts (2^48) 5747507201 10 Manual.Count131072.C043820.packed 64 cuts43820 = true := by
 decide +kernel
def pointBounds43820 : List (Nat × Nat × Nat) := [(5747552256,110010364925912,110010751102954)]
theorem point_links_checked43820 : (cuts43820.take 1).map (fun c => (5747507201-1+2*2^10*c.k,110010266440821+c.lower,110010652617807+c.upper)) = pointBounds43820 := by
 decide +kernel
def cuts43821 : List PrefixCut := [⟨46,205828781,205828898⟩,
⟨64,286827324,286827491⟩]
theorem checked43821 : checkPrefixCuts (2^48) 5747638273 10 Manual.Count131072.C043821.packed 64 cuts43821 = true := by
 decide +kernel
def pointBounds43821 : List (Nat × Nat × Nat) := [(5747732480,110010752394219,110011138571484)]
theorem point_links_checked43821 : (cuts43821.take 1).map (fun c => (5747638273-1+2*2^10*c.k,110010546565438+c.lower,110010932742586+c.upper)) = pointBounds43821 := by
 decide +kernel
def cuts43822 : List PrefixCut := [⟨64,283686637,283686806⟩]
theorem checked43822 : checkPrefixCuts (2^48) 5747769345 10 Manual.Count131072.C043822.packed 64 cuts43822 = true := by
 decide +kernel
def cuts43823 : List PrefixCut := [⟨6,26149970,26149986⟩,
⟨64,284267809,284267975⟩]
theorem checked43823 : checkPrefixCuts (2^48) 5747900417 10 Manual.Count131072.C043823.packed 64 cuts43823 = true := by
 decide +kernel
def pointBounds43823 : List (Nat × Nat × Nat) := [(5747912704,110011143229369,110011529406869)]
theorem point_links_checked43823 : (cuts43823.take 1).map (fun c => (5747900417-1+2*2^10*c.k,110011117079399+c.lower,110011503256883+c.upper)) = pointBounds43823 := by
 decide +kernel
def cuts43824 : List PrefixCut := [⟨30,134125144,134125225⟩,
⟨64,284457210,284457377⟩]
theorem checked43824 : checkPrefixCuts (2^48) 5748031489 10 Manual.Count131072.C043824.packed 64 cuts43824 = true := by
 decide +kernel
def pointBounds43824 : List (Nat × Nat × Nat) := [(5748092928,110011535472352,110011921650083)]
theorem point_links_checked43824 : (cuts43824.take 1).map (fun c => (5748031489-1+2*2^10*c.k,110011401347208+c.lower,110011787524858+c.upper)) = pointBounds43824 := by
 decide +kernel
def cuts43825 : List PrefixCut := [⟨54,243759361,243759502⟩,
⟨64,288319126,288319294⟩]
theorem checked43825 : checkPrefixCuts (2^48) 5748162561 10 Manual.Count131072.C043825.packed 64 cuts43825 = true := by
 decide +kernel
def pointBounds43825 : List (Nat × Nat × Nat) := [(5748273152,110011929563779,110012315741737)]
theorem point_links_checked43825 : (cuts43825.take 1).map (fun c => (5748162561-1+2*2^10*c.k,110011685804418+c.lower,110012071982235+c.upper)) = pointBounds43825 := by
 decide +kernel
def cuts43826 : List PrefixCut := [⟨64,283856658,283856826⟩]
theorem checked43826 : checkPrefixCuts (2^48) 5748293633 10 Manual.Count131072.C043826.packed 64 cuts43826 = true := by
 decide +kernel
def cuts43827 : List PrefixCut := [⟨14,63997839,63997877⟩,
⟨64,289383238,289383404⟩]
theorem checked43827 : checkPrefixCuts (2^48) 5748424705 10 Manual.Count131072.C043827.packed 64 cuts43827 = true := by
 decide +kernel
def pointBounds43827 : List (Nat × Nat × Nat) := [(5748453376,110012321978041,110012708156232)]
theorem point_links_checked43827 : (cuts43827.take 1).map (fun c => (5748424705-1+2*2^10*c.k,110012257980202+c.lower,110012644158355+c.upper)) = pointBounds43827 := by
 decide +kernel
def cuts43828 : List PrefixCut := [⟨38,169415860,169415956⟩,
⟨64,284529197,284529362⟩]
theorem checked43828 : checkPrefixCuts (2^48) 5748555777 10 Manual.Count131072.C043828.packed 64 cuts43828 = true := by
 decide +kernel
def pointBounds43828 : List (Nat × Nat × Nat) := [(5748633600,110012716779300,110013102957715)]
theorem point_links_checked43828 : (cuts43828.take 1).map (fun c => (5748555777-1+2*2^10*c.k,110012547363440+c.lower,110012933541759+c.upper)) = pointBounds43828 := by
 decide +kernel
def cuts43829 : List PrefixCut := [⟨62,273457216,273457381⟩,
⟨64,282172495,282172664⟩]
theorem checked43829 : checkPrefixCuts (2^48) 5748686849 10 Manual.Count131072.C043829.packed 64 cuts43829 = true := by
 decide +kernel
def pointBounds43829 : List (Nat × Nat × Nat) := [(5748813824,110013105349853,110013491528502)]
theorem point_links_checked43829 : (cuts43829.take 1).map (fun c => (5748686849-1+2*2^10*c.k,110012831892637+c.lower,110013218071121+c.upper)) = pointBounds43829 := by
 decide +kernel
def cuts43830 : List PrefixCut := [⟨64,289950994,289951162⟩]
theorem checked43830 : checkPrefixCuts (2^48) 5748817921 10 Manual.Count131072.C043830.packed 64 cuts43830 = true := by
 decide +kernel
def cuts43831 : List PrefixCut := [⟨22,96550919,96550974⟩,
⟨64,284509707,284509875⟩]
theorem checked43831 : checkPrefixCuts (2^48) 5748948993 10 Manual.Count131072.C043831.packed 64 cuts43831 = true := by
 decide +kernel
def pointBounds43831 : List (Nat × Nat × Nat) := [(5748994048,110013500567045,110013886745921)]
theorem point_links_checked43831 : (cuts43831.take 1).map (fun c => (5748948993-1+2*2^10*c.k,110013404016126+c.lower,110013790194947+c.upper)) = pointBounds43831 := by
 decide +kernel
def cuts43832 : List PrefixCut := [⟨46,203084370,203084486⟩,
⟨64,282349039,282349200⟩]
theorem checked43832 : checkPrefixCuts (2^48) 5749080065 10 Manual.Count131072.C043832.packed 64 cuts43832 = true := by
 decide +kernel
def pointBounds43832 : List (Nat × Nat × Nat) := [(5749174272,110013891610203,110014277789308)]
theorem point_links_checked43832 : (cuts43832.take 1).map (fun c => (5749080065-1+2*2^10*c.k,110013688525833+c.lower,110014074704822+c.upper)) = pointBounds43832 := by
 decide +kernel
def cuts43833 : List PrefixCut := [⟨64,287189461,287189627⟩]
theorem checked43833 : checkPrefixCuts (2^48) 5749211137 10 Manual.Count131072.C043833.packed 64 cuts43833 = true := by
 decide +kernel
def cuts43834 : List PrefixCut := [⟨6,26290286,26290303⟩,
⟨64,282776788,282776952⟩]
theorem checked43834 : checkPrefixCuts (2^48) 5749342209 10 Manual.Count131072.C043834.packed 64 cuts43834 = true := by
 decide +kernel
def pointBounds43834 : List (Nat × Nat × Nat) := [(5749354496,110014284354619,110014670533952)]
theorem point_links_checked43834 : (cuts43834.take 1).map (fun c => (5749342209-1+2*2^10*c.k,110014258064333+c.lower,110014644243649+c.upper)) = pointBounds43834 := by
 decide +kernel
def cuts43835 : List PrefixCut := [⟨30,133406128,133406202⟩,
⟨64,285365004,285365165⟩]
theorem checked43835 : checkPrefixCuts (2^48) 5749473281 10 Manual.Count131072.C043835.packed 64 cuts43835 = true := by
 decide +kernel
def pointBounds43835 : List (Nat × Nat × Nat) := [(5749534720,110014674247249,110015060426803)]
theorem point_links_checked43835 : (cuts43835.take 1).map (fun c => (5749473281-1+2*2^10*c.k,110014540841121+c.lower,110014927020601+c.upper)) = pointBounds43835 := by
 decide +kernel
def cuts43836 : List PrefixCut := [⟨54,241446352,241446491⟩,
⟨64,286778215,286778381⟩]
theorem checked43836 : checkPrefixCuts (2^48) 5749604353 10 Manual.Count131072.C043836.packed 64 cuts43836 = true := by
 decide +kernel
def pointBounds43836 : List (Nat × Nat × Nat) := [(5749714944,110015067652477,110015453832257)]
theorem point_links_checked43836 : (cuts43836.take 1).map (fun c => (5749604353-1+2*2^10*c.k,110014826206125+c.lower,110015212385766+c.upper)) = pointBounds43836 := by
 decide +kernel
def cuts43837 : List PrefixCut := [⟨64,287261191,287261355⟩]
theorem checked43837 : checkPrefixCuts (2^48) 5749735425 10 Manual.Count131072.C043837.packed 64 cuts43837 = true := by
 decide +kernel
def cuts43838 : List PrefixCut := [⟨14,61044604,61044640⟩,
⟨64,280303335,280303505⟩]
theorem checked43838 : checkPrefixCuts (2^48) 5749866497 10 Manual.Count131072.C043838.packed 64 cuts43838 = true := by
 decide +kernel
def pointBounds43838 : List (Nat × Nat × Nat) := [(5749895168,110015461290135,110015847470142)]
theorem point_links_checked43838 : (cuts43838.take 1).map (fun c => (5749866497-1+2*2^10*c.k,110015400245531+c.lower,110015786425502+c.upper)) = pointBounds43838 := by
 decide +kernel
def cuts43839 : List PrefixCut := [⟨38,170352430,170352528⟩,
⟨64,287101254,287101419⟩]
theorem checked43839 : checkPrefixCuts (2^48) 5749997569 10 Manual.Count131072.C043839.packed 64 cuts43839 = true := by
 decide +kernel
def pointBounds43839 : List (Nat × Nat × Nat) := [(5750075392,110015850901296,110016237081535)]
theorem point_links_checked43839 : (cuts43839.take 1).map (fun c => (5749997569-1+2*2^10*c.k,110015680548866+c.lower,110016066729007+c.upper)) = pointBounds43839 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000119
