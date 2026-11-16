import PlattAssemblyKernel
import PlattCertificates.Count131072.C040800
import PlattCertificates.Count131072.C040801
import PlattCertificates.Count131072.C040802
import PlattCertificates.Count131072.C040803
import PlattCertificates.Count131072.C040804
import PlattCertificates.Count131072.C040805
import PlattCertificates.Count131072.C040806
import PlattCertificates.Count131072.C040807
import PlattCertificates.Count131072.C040808
import PlattCertificates.Count131072.C040809
import PlattCertificates.Count131072.C040810
import PlattCertificates.Count131072.C040811
import PlattCertificates.Count131072.C040812
import PlattCertificates.Count131072.C040813
import PlattCertificates.Count131072.C040814
import PlattCertificates.Count131072.C040815
import PlattCertificates.Count131072.C040816
import PlattCertificates.Count131072.C040817
import PlattCertificates.Count131072.C040818
import PlattCertificates.Count131072.C040819
import PlattCertificates.Count131072.C040820
import PlattCertificates.Count131072.C040821
import PlattCertificates.Count131072.C040822
import PlattCertificates.Count131072.C040823
import PlattCertificates.Count131072.C040824
import PlattCertificates.Count131072.C040825
import PlattCertificates.Count131072.C040826
import PlattCertificates.Count131072.C040827
import PlattCertificates.Count131072.C040828
import PlattCertificates.Count131072.C040829
import PlattCertificates.Count131072.C040830
import PlattCertificates.Count131072.C040831
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40800 : List PrefixCut := [⟨33,157102420,157102510⟩,
⟨64,305998129,305998305⟩]
theorem checked40800 : checkPrefixCuts (2^48) 5351669761 10 Manual.Count131072.C040800.packed 64 cuts40800 = true := by
 decide +kernel
def pointBounds40800 : List (Nat × Nat × Nat) := [(5351737344,109115132601599,109115518254757)]
theorem point_links_checked40800 : (cuts40800.take 1).map (fun c => (5351669761-1+2*2^10*c.k,109114975499179+c.lower,109115361152247+c.upper)) = pointBounds40800 := by
 decide +kernel
def cuts40801 : List PrefixCut := [⟨51,247349163,247349311⟩,
⟨64,307831418,307831603⟩]
theorem checked40801 : checkPrefixCuts (2^48) 5351800833 10 Manual.Count131072.C040801.packed 64 cuts40801 = true := by
 decide +kernel
def pointBounds40801 : List (Nat × Nat × Nat) := [(5351905280,109115528846471,109115914499863)]
theorem point_links_checked40801 : (cuts40801.take 1).map (fun c => (5351800833-1+2*2^10*c.k,109115281497308+c.lower,109115667150552+c.upper)) = pointBounds40801 := by
 decide +kernel
def cuts40802 : List PrefixCut := [⟨64,304194981,304195164⟩]
theorem checked40802 : checkPrefixCuts (2^48) 5351931905 10 Manual.Count131072.C040802.packed 64 cuts40802 = true := by
 decide +kernel
def cuts40803 : List PrefixCut := [⟨5,23403352,23403364⟩,
⟨64,305291976,305292157⟩]
theorem checked40803 : checkPrefixCuts (2^48) 5352062977 10 Manual.Count131072.C040803.packed 64 cuts40803 = true := by
 decide +kernel
def pointBounds40803 : List (Nat × Nat × Nat) := [(5352073216,109115916927059,109116302580683)]
theorem point_links_checked40803 : (cuts40803.take 1).map (fun c => (5352062977-1+2*2^10*c.k,109115893523707+c.lower,109116279177319+c.upper)) = pointBounds40803 := by
 decide +kernel
def cuts40804 : List PrefixCut := [⟨23,113226979,113227046⟩,
⟨64,308019178,308019362⟩]
theorem checked40804 : checkPrefixCuts (2^48) 5352194049 10 Manual.Count131072.C040804.packed 64 cuts40804 = true := by
 decide +kernel
def pointBounds40804 : List (Nat × Nat × Nat) := [(5352241152,109116312042662,109116697696522)]
theorem point_links_checked40804 : (cuts40804.take 1).map (fun c => (5352194049-1+2*2^10*c.k,109116198815683+c.lower,109116584469476+c.upper)) = pointBounds40804 := by
 decide +kernel
def cuts40805 : List PrefixCut := [⟨41,196787527,196787647⟩,
⟨64,307117617,307117801⟩]
theorem checked40805 : checkPrefixCuts (2^48) 5352325121 10 Manual.Count131072.C040805.packed 64 cuts40805 = true := by
 decide +kernel
def pointBounds40805 : List (Nat × Nat × Nat) := [(5352409088,109116703622388,109117089276485)]
theorem point_links_checked40805 : (cuts40805.take 1).map (fun c => (5352325121-1+2*2^10*c.k,109116506834861+c.lower,109116892488838+c.upper)) = pointBounds40805 := by
 decide +kernel
def cuts40806 : List PrefixCut := [⟨59,281658098,281658264⟩,
⟨64,304585921,304586100⟩]
theorem checked40806 : checkPrefixCuts (2^48) 5352456193 10 Manual.Count131072.C040806.packed 64 cuts40806 = true := by
 decide +kernel
def pointBounds40806 : List (Nat × Nat × Nat) := [(5352577024,109117095610576,109117481264903)]
theorem point_links_checked40806 : (cuts40806.take 1).map (fun c => (5352456193-1+2*2^10*c.k,109116813952478+c.lower,109117199606639+c.upper)) = pointBounds40806 := by
 decide +kernel
def cuts40807 : List PrefixCut := [⟨64,311362055,311362235⟩]
theorem checked40807 : checkPrefixCuts (2^48) 5352587265 10 Manual.Count131072.C040807.packed 64 cuts40807 = true := by
 decide +kernel
def cuts40808 : List PrefixCut := [⟨13,62313556,62313594⟩,
⟨64,307883816,307884000⟩]
theorem checked40808 : checkPrefixCuts (2^48) 5352718337 10 Manual.Count131072.C040808.packed 64 cuts40808 = true := by
 decide +kernel
def pointBounds40808 : List (Nat × Nat × Nat) := [(5352744960,109117492214010,109117877868568)]
theorem point_links_checked40808 : (cuts40808.take 1).map (fun c => (5352718337-1+2*2^10*c.k,109117429900454+c.lower,109117815554974+c.upper)) = pointBounds40808 := by
 decide +kernel
def cuts40809 : List PrefixCut := [⟨31,149758698,149758786⟩,
⟨64,308612454,308612633⟩]
theorem checked40809 : checkPrefixCuts (2^48) 5352849409 10 Manual.Count131072.C040809.packed 64 cuts40809 = true := by
 decide +kernel
def pointBounds40809 : List (Nat × Nat × Nat) := [(5352912896,109117887542968,109118273197760)]
theorem point_links_checked40809 : (cuts40809.take 1).map (fun c => (5352849409-1+2*2^10*c.k,109117737784270+c.lower,109118123438974+c.upper)) = pointBounds40809 := by
 decide +kernel
def cuts40810 : List PrefixCut := [⟨49,234622428,234622563⟩,
⟨64,307185173,307185352⟩]
theorem checked40810 : checkPrefixCuts (2^48) 5352980481 10 Manual.Count131072.C040810.packed 64 cuts40810 = true := by
 decide +kernel
def pointBounds40810 : List (Nat × Nat × Nat) := [(5353080832,109118281019152,109118666674170)]
theorem point_links_checked40810 : (cuts40810.take 1).map (fun c => (5352980481-1+2*2^10*c.k,109118046396724+c.lower,109118432051607+c.upper)) = pointBounds40810 := by
 decide +kernel
def cuts40811 : List PrefixCut := [⟨64,311173790,311173972⟩]
theorem checked40811 : checkPrefixCuts (2^48) 5353111553 10 Manual.Count131072.C040811.packed 64 cuts40811 = true := by
 decide +kernel
def cuts40812 : List PrefixCut := [⟨3,13407959,13407967⟩,
⟨64,304646297,304646476⟩]
theorem checked40812 : checkPrefixCuts (2^48) 5353242625 10 Manual.Count131072.C040812.packed 64 cuts40812 = true := by
 decide +kernel
def pointBounds40812 : List (Nat × Nat × Nat) := [(5353248768,109118678163646,109119063818898)]
theorem point_links_checked40812 : (cuts40812.take 1).map (fun c => (5353242625-1+2*2^10*c.k,109118664755687+c.lower,109119050410931+c.upper)) = pointBounds40812 := by
 decide +kernel
def cuts40813 : List PrefixCut := [⟨21,99794489,99794549⟩,
⟨64,309844080,309844263⟩]
theorem checked40813 : checkPrefixCuts (2^48) 5353373697 10 Manual.Count131072.C040813.packed 64 cuts40813 = true := by
 decide +kernel
def pointBounds40813 : List (Nat × Nat × Nat) := [(5353416704,109119069196473,109119454851956)]
theorem point_links_checked40813 : (cuts40813.take 1).map (fun c => (5353373697-1+2*2^10*c.k,109118969401984+c.lower,109119355057407+c.upper)) = pointBounds40813 := by
 decide +kernel
def cuts40814 : List PrefixCut := [⟨39,191381361,191381474⟩,
⟨64,309153048,309153230⟩]
theorem checked40814 : checkPrefixCuts (2^48) 5353504769 10 Manual.Count131072.C040814.packed 64 cuts40814 = true := by
 decide +kernel
def pointBounds40814 : List (Nat × Nat × Nat) := [(5353584640,109119470627425,109119856283144)]
theorem point_links_checked40814 : (cuts40814.take 1).map (fun c => (5353504769-1+2*2^10*c.k,109119279246064+c.lower,109119664901670+c.upper)) = pointBounds40814 := by
 decide +kernel
def cuts40815 : List PrefixCut := [⟨57,277390036,277390201⟩,
⟨64,310722701,310722886⟩]
theorem checked40815 : checkPrefixCuts (2^48) 5353635841 10 Manual.Count131072.C040815.packed 64 cuts40815 = true := by
 decide +kernel
def pointBounds40815 : List (Nat × Nat × Nat) := [(5353752576,109119865789148,109120251445101)]
theorem point_links_checked40815 : (cuts40815.take 1).map (fun c => (5353635841-1+2*2^10*c.k,109119588399112+c.lower,109119974054900+c.upper)) = pointBounds40815 := by
 decide +kernel
def cuts40816 : List PrefixCut := [⟨64,310294533,310294716⟩]
theorem checked40816 : checkPrefixCuts (2^48) 5353766913 10 Manual.Count131072.C040816.packed 64 cuts40816 = true := by
 decide +kernel
def cuts40817 : List PrefixCut := [⟨11,52994307,52994340⟩,
⟨64,307237672,307237854⟩]
theorem checked40817 : checkPrefixCuts (2^48) 5353897985 10 Manual.Count131072.C040817.packed 64 cuts40817 = true := by
 decide +kernel
def pointBounds40817 : List (Nat × Nat × Nat) := [(5353920512,109120262410653,109120648066842)]
theorem point_links_checked40817 : (cuts40817.take 1).map (fun c => (5353897985-1+2*2^10*c.k,109120209416346+c.lower,109120595072502+c.upper)) = pointBounds40817 := by
 decide +kernel
def cuts40818 : List PrefixCut := [⟨29,138685582,138685667⟩,
⟨64,304654139,304654320⟩]
theorem checked40818 : checkPrefixCuts (2^48) 5354029057 10 Manual.Count131072.C040818.packed 64 cuts40818 = true := by
 decide +kernel
def pointBounds40818 : List (Nat × Nat × Nat) := [(5354088448,109120655339600,109121040996023)]
theorem point_links_checked40818 : (cuts40818.take 1).map (fun c => (5354029057-1+2*2^10*c.k,109120516654018+c.lower,109120902310356+c.upper)) = pointBounds40818 := by
 decide +kernel
def cuts40819 : List PrefixCut := [⟨47,227368592,227368730⟩,
⟨64,308642016,308642204⟩]
theorem checked40819 : checkPrefixCuts (2^48) 5354160129 10 Manual.Count131072.C040819.packed 64 cuts40819 = true := by
 decide +kernel
def pointBounds40819 : List (Nat × Nat × Nat) := [(5354256384,109121048676749,109121434333406)]
theorem point_links_checked40819 : (cuts40819.take 1).map (fun c => (5354160129-1+2*2^10*c.k,109120821308157+c.lower,109121206964676+c.upper)) = pointBounds40819 := by
 decide +kernel
def cuts40820 : List PrefixCut := [⟨64,309212766,309212951⟩]
theorem checked40820 : checkPrefixCuts (2^48) 5354291201 10 Manual.Count131072.C040820.packed 64 cuts40820 = true := by
 decide +kernel
def cuts40821 : List PrefixCut := [⟨1,4994023,4994026⟩,
⟨64,306839553,306839735⟩]
theorem checked40821 : checkPrefixCuts (2^48) 5354422273 10 Manual.Count131072.C040821.packed 64 cuts40821 = true := by
 decide +kernel
def pointBounds40821 : List (Nat × Nat × Nat) := [(5354424320,109121444156962,109121829813857)]
theorem point_links_checked40821 : (cuts40821.take 1).map (fun c => (5354422273-1+2*2^10*c.k,109121439162939+c.lower,109121824819831+c.upper)) = pointBounds40821 := by
 decide +kernel
def cuts40822 : List PrefixCut := [⟨19,90573284,90573335⟩,
⟨64,307568014,307568190⟩]
theorem checked40822 : checkPrefixCuts (2^48) 5354553345 10 Manual.Count131072.C040822.packed 64 cuts40822 = true := by
 decide +kernel
def pointBounds40822 : List (Nat × Nat × Nat) := [(5354592256,109121836575776,109122222232901)]
theorem point_links_checked40822 : (cuts40822.take 1).map (fun c => (5354553345-1+2*2^10*c.k,109121746002492+c.lower,109122131659566+c.upper)) = pointBounds40822 := by
 decide +kernel
def cuts40823 : List PrefixCut := [⟨37,177672178,177672280⟩,
⟨64,310504166,310504347⟩]
theorem checked40823 : checkPrefixCuts (2^48) 5354684417 10 Manual.Count131072.C040823.packed 64 cuts40823 = true := by
 decide +kernel
def pointBounds40823 : List (Nat × Nat × Nat) := [(5354760192,109122231242684,109122616900036)]
theorem point_links_checked40823 : (cuts40823.take 1).map (fun c => (5354684417-1+2*2^10*c.k,109122053570506+c.lower,109122439227756+c.upper)) = pointBounds40823 := by
 decide +kernel
def cuts40824 : List PrefixCut := [⟨55,262873893,262874044⟩,
⟨64,307395278,307395454⟩]
theorem checked40824 : checkPrefixCuts (2^48) 5354815489 10 Manual.Count131072.C040824.packed 64 cuts40824 = true := by
 decide +kernel
def pointBounds40824 : List (Nat × Nat × Nat) := [(5354928128,109122626948565,109123012606147)]
theorem point_links_checked40824 : (cuts40824.take 1).map (fun c => (5354815489-1+2*2^10*c.k,109122364074672+c.lower,109122749732103+c.upper)) = pointBounds40824 := by
 decide +kernel
def cuts40825 : List PrefixCut := [⟨64,306021128,306021306⟩]
theorem checked40825 : checkPrefixCuts (2^48) 5354946561 10 Manual.Count131072.C040825.packed 64 cuts40825 = true := by
 decide +kernel
def cuts40826 : List PrefixCut := [⟨9,41366415,41366440⟩,
⟨64,303911171,303911350⟩]
theorem checked40826 : checkPrefixCuts (2^48) 5355077633 10 Manual.Count131072.C040826.packed 64 cuts40826 = true := by
 decide +kernel
def pointBounds40826 : List (Nat × Nat × Nat) := [(5355096064,109123018857493,109123404515303)]
theorem point_links_checked40826 : (cuts40826.take 1).map (fun c => (5355077633-1+2*2^10*c.k,109122977491078+c.lower,109123363148863+c.upper)) = pointBounds40826 := by
 decide +kernel
def cuts40827 : List PrefixCut := [⟨27,132032442,132032521⟩,
⟨64,307372741,307372922⟩]
theorem checked40827 : checkPrefixCuts (2^48) 5355208705 10 Manual.Count131072.C040827.packed 64 cuts40827 = true := by
 decide +kernel
def pointBounds40827 : List (Nat × Nat × Nat) := [(5355264000,109123413434691,109123799092734)]
theorem point_links_checked40827 : (cuts40827.take 1).map (fun c => (5355208705-1+2*2^10*c.k,109123281402249+c.lower,109123667060213+c.upper)) = pointBounds40827 := by
 decide +kernel
def cuts40828 : List PrefixCut := [⟨45,218856589,218856714⟩,
⟨64,310255951,310256127⟩]
theorem checked40828 : checkPrefixCuts (2^48) 5355339777 10 Manual.Count131072.C040828.packed 64 cuts40828 = true := by
 decide +kernel
def pointBounds40828 : List (Nat × Nat × Nat) := [(5355431936,109123807631579,109124193289849)]
theorem point_links_checked40828 : (cuts40828.take 1).map (fun c => (5355339777-1+2*2^10*c.k,109123588774990+c.lower,109123974433135+c.upper)) = pointBounds40828 := by
 decide +kernel
def cuts40829 : List PrefixCut := [⟨63,301734040,301734216⟩,
⟨64,306148837,306149016⟩]
theorem checked40829 : checkPrefixCuts (2^48) 5355470849 10 Manual.Count131072.C040829.packed 64 cuts40829 = true := by
 decide +kernel
def pointBounds40829 : List (Nat × Nat × Nat) := [(5355599872,109124200764981,109124586423478)]
theorem point_links_checked40829 : (cuts40829.take 1).map (fun c => (5355470849-1+2*2^10*c.k,109123899030941+c.lower,109124284689262+c.upper)) = pointBounds40829 := by
 decide +kernel
def cuts40830 : List PrefixCut := [⟨64,306193896,306194080⟩]
theorem checked40830 : checkPrefixCuts (2^48) 5355601921 10 Manual.Count131072.C040830.packed 64 cuts40830 = true := by
 decide +kernel
def cuts40831 : List PrefixCut := [⟨17,81724018,81724067⟩,
⟨64,305608316,305608499⟩]
theorem checked40831 : checkPrefixCuts (2^48) 5355732993 10 Manual.Count131072.C040831.packed 64 cuts40831 = true := by
 decide +kernel
def pointBounds40831 : List (Nat × Nat × Nat) := [(5355767808,109124593097692,109124978756425)]
theorem point_links_checked40831 : (cuts40831.take 1).map (fun c => (5355732993-1+2*2^10*c.k,109124511373674+c.lower,109124897032358+c.upper)) = pointBounds40831 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000025
