import PlattAssemblyKernel
import PlattCertificates.Count131072.C050800
import PlattCertificates.Count131072.C050801
import PlattCertificates.Count131072.C050802
import PlattCertificates.Count131072.C050803
import PlattCertificates.Count131072.C050804
import PlattCertificates.Count131072.C050805
import PlattCertificates.Count131072.C050806
import PlattCertificates.Count131072.C050807
import PlattCertificates.Count131072.C050808
import PlattCertificates.Count131072.C050809
import PlattCertificates.Count131072.C050810
import PlattCertificates.Count131072.C050811
import PlattCertificates.Count131072.C050812
import PlattCertificates.Count131072.C050813
import PlattCertificates.Count131072.C050814
import PlattCertificates.Count131072.C050815
import PlattCertificates.Count131072.C050816
import PlattCertificates.Count131072.C050817
import PlattCertificates.Count131072.C050818
import PlattCertificates.Count131072.C050819
import PlattCertificates.Count131072.C050820
import PlattCertificates.Count131072.C050821
import PlattCertificates.Count131072.C050822
import PlattCertificates.Count131072.C050823
import PlattCertificates.Count131072.C050824
import PlattCertificates.Count131072.C050825
import PlattCertificates.Count131072.C050826
import PlattCertificates.Count131072.C050827
import PlattCertificates.Count131072.C050828
import PlattCertificates.Count131072.C050829
import PlattCertificates.Count131072.C050830
import PlattCertificates.Count131072.C050831
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50800 : List PrefixCut := [⟨24,92692512,92692565⟩,
⟨64,246981357,246981498⟩]
theorem checked50800 : checkPrefixCuts (2^48) 6662389761 10 Manual.Count131072.C050800.packed 64 cuts50800 = true := by
 decide +kernel
def pointBounds50800 : List (Nat × Nat × Nat) := [(6662438912,111854429565323,111854816799802)]
theorem point_links_checked50800 : (cuts50800.take 1).map (fun c => (6662389761-1+2*2^10*c.k,111854336872811+c.lower,111854724107237+c.upper)) = pointBounds50800 := by
 decide +kernel
def cuts50801 : List PrefixCut := [⟨62,237133013,237133147⟩,
⟨64,244145963,244146101⟩]
theorem checked50801 : checkPrefixCuts (2^48) 6662520833 10 Manual.Count131072.C050801.packed 64 cuts50801 = true := by
 decide +kernel
def pointBounds50801 : List (Nat × Nat × Nat) := [(6662647808,111854820987181,111855208221882)]
theorem point_links_checked50801 : (cuts50801.take 1).map (fun c => (6662520833-1+2*2^10*c.k,111854583854168+c.lower,111854971088735+c.upper)) = pointBounds50801 := by
 decide +kernel
def cuts50802 : List PrefixCut := [⟨64,245662011,245662148⟩]
theorem checked50802 : checkPrefixCuts (2^48) 6662651905 10 Manual.Count131072.C050802.packed 64 cuts50802 = true := by
 decide +kernel
def cuts50803 : List PrefixCut := [⟨36,138692339,138692420⟩,
⟨64,245107988,245108129⟩]
theorem checked50803 : checkPrefixCuts (2^48) 6662782977 10 Manual.Count131072.C050803.packed 64 cuts50803 = true := by
 decide +kernel
def pointBounds50803 : List (Nat × Nat × Nat) := [(6662856704,111855212354481,111855599589404)]
theorem point_links_checked50803 : (cuts50803.take 1).map (fun c => (6662782977-1+2*2^10*c.k,111855073662142+c.lower,111855460896984+c.upper)) = pointBounds50803 := by
 decide +kernel
def cuts50804 : List PrefixCut := [⟨64,244596221,244596362⟩]
theorem checked50804 : checkPrefixCuts (2^48) 6662914049 10 Manual.Count131072.C050804.packed 64 cuts50804 = true := by
 decide +kernel
def cuts50805 : List PrefixCut := [⟨10,39244785,39244809⟩,
⟨64,245647512,245647655⟩]
theorem checked50805 : checkPrefixCuts (2^48) 6663045121 10 Manual.Count131072.C050805.packed 64 cuts50805 = true := by
 decide +kernel
def pointBounds50805 : List (Nat × Nat × Nat) := [(6663065600,111855602611136,111855989846284)]
theorem point_links_checked50805 : (cuts50805.take 1).map (fun c => (6663045121-1+2*2^10*c.k,111855563366351+c.lower,111855950601475+c.upper)) = pointBounds50805 := by
 decide +kernel
def cuts50806 : List PrefixCut := [⟨48,181560592,181560697⟩,
⟨64,241502876,241503017⟩]
theorem checked50806 : checkPrefixCuts (2^48) 6663176193 10 Manual.Count131072.C050806.packed 64 cuts50806 = true := by
 decide +kernel
def pointBounds50806 : List (Nat × Nat × Nat) := [(6663274496,111855990574455,111856377809827)]
theorem point_links_checked50806 : (cuts50806.take 1).map (fun c => (6663176193-1+2*2^10*c.k,111855809013863+c.lower,111856196249130+c.upper)) = pointBounds50806 := by
 decide +kernel
def cuts50807 : List PrefixCut := [⟨64,246229229,246229370⟩]
theorem checked50807 : checkPrefixCuts (2^48) 6663307265 10 Manual.Count131072.C050807.packed 64 cuts50807 = true := by
 decide +kernel
def cuts50808 : List PrefixCut := [⟨22,84229638,84229687⟩,
⟨64,243520955,243521095⟩]
theorem checked50808 : checkPrefixCuts (2^48) 6663438337 10 Manual.Count131072.C050808.packed 64 cuts50808 = true := by
 decide +kernel
def pointBounds50808 : List (Nat × Nat × Nat) := [(6663483392,111856380975606,111856768211204)]
theorem point_links_checked50808 : (cuts50808.take 1).map (fun c => (6663438337-1+2*2^10*c.k,111856296745968+c.lower,111856683981517+c.upper)) = pointBounds50808 := by
 decide +kernel
def cuts50809 : List PrefixCut := [⟨60,228098537,228098664⟩,
⟨64,243980798,243980933⟩]
theorem checked50809 : checkPrefixCuts (2^48) 6663569409 10 Manual.Count131072.C050809.packed 64 cuts50809 = true := by
 decide +kernel
def pointBounds50809 : List (Nat × Nat × Nat) := [(6663692288,111856768365460,111857155601276)]
theorem point_links_checked50809 : (cuts50809.take 1).map (fun c => (6663569409-1+2*2^10*c.k,111856540266923+c.lower,111856927502612+c.upper)) = pointBounds50809 := by
 decide +kernel
def cuts50810 : List PrefixCut := [⟨64,250100744,250100885⟩]
theorem checked50810 : checkPrefixCuts (2^48) 6663700481 10 Manual.Count131072.C050810.packed 64 cuts50810 = true := by
 decide +kernel
def cuts50811 : List PrefixCut := [⟨34,128448739,128448811⟩,
⟨64,240803313,240803452⟩]
theorem checked50811 : checkPrefixCuts (2^48) 6663831553 10 Manual.Count131072.C050811.packed 64 cuts50811 = true := by
 decide +kernel
def pointBounds50811 : List (Nat × Nat × Nat) := [(6663901184,111857162797204,111857550033241)]
theorem point_links_checked50811 : (cuts50811.take 1).map (fun c => (6663831553-1+2*2^10*c.k,111857034348465+c.lower,111857421584430+c.upper)) = pointBounds50811 := by
 decide +kernel
def cuts50812 : List PrefixCut := [⟨64,244980110,244980251⟩]
theorem checked50812 : checkPrefixCuts (2^48) 6663962625 10 Manual.Count131072.C050812.packed 64 cuts50812 = true := by
 decide +kernel
def cuts50813 : List PrefixCut := [⟨8,30706649,30706667⟩,
⟨64,243961625,243961763⟩]
theorem checked50813 : checkPrefixCuts (2^48) 6664093697 10 Manual.Count131072.C050813.packed 64 cuts50813 = true := by
 decide +kernel
def pointBounds50813 : List (Nat × Nat × Nat) := [(6664110080,111857550838537,111857938074800)]
theorem point_links_checked50813 : (cuts50813.take 1).map (fun c => (6664093697-1+2*2^10*c.k,111857520131888+c.lower,111857907368133+c.upper)) = pointBounds50813 := by
 decide +kernel
def cuts50814 : List PrefixCut := [⟨46,177857513,177857620⟩,
⟨64,245519574,245519720⟩]
theorem checked50814 : checkPrefixCuts (2^48) 6664224769 10 Manual.Count131072.C050814.packed 64 cuts50814 = true := by
 decide +kernel
def pointBounds50814 : List (Nat × Nat × Nat) := [(6664318976,111857941951026,111858329187516)]
theorem point_links_checked50814 : (cuts50814.take 1).map (fun c => (6664224769-1+2*2^10*c.k,111857764093513+c.lower,111858151329896+c.upper)) = pointBounds50814 := by
 decide +kernel
def cuts50815 : List PrefixCut := [⟨64,241417876,241418012⟩]
theorem checked50815 : checkPrefixCuts (2^48) 6664355841 10 Manual.Count131072.C050815.packed 64 cuts50815 = true := by
 decide +kernel
def cuts50816 : List PrefixCut := [⟨20,74291214,74291256⟩,
⟨64,241370884,241371019⟩]
theorem checked50816 : checkPrefixCuts (2^48) 6664486913 10 Manual.Count131072.C050816.packed 64 cuts50816 = true := by
 decide +kernel
def pointBounds50816 : List (Nat × Nat × Nat) := [(6664527872,111858325322177,111858712558884)]
theorem point_links_checked50816 : (cuts50816.take 1).map (fun c => (6664486913-1+2*2^10*c.k,111858251030963+c.lower,111858638267628+c.upper)) = pointBounds50816 := by
 decide +kernel
def cuts50817 : List PrefixCut := [⟨58,220629572,220629699⟩,
⟨64,243984655,243984794⟩]
theorem checked50817 : checkPrefixCuts (2^48) 6664617985 10 Manual.Count131072.C050817.packed 64 cuts50817 = true := by
 decide +kernel
def pointBounds50817 : List (Nat × Nat × Nat) := [(6664736768,111858713031419,111859100268346)]
theorem point_links_checked50817 : (cuts50817.take 1).map (fun c => (6664617985-1+2*2^10*c.k,111858492401847+c.lower,111858879638647+c.upper)) = pointBounds50817 := by
 decide +kernel
def cuts50818 : List PrefixCut := [⟨64,243937642,243937782⟩]
theorem checked50818 : checkPrefixCuts (2^48) 6664749057 10 Manual.Count131072.C050818.packed 64 cuts50818 = true := by
 decide +kernel
def cuts50819 : List PrefixCut := [⟨32,122135946,122136016⟩,
⟨64,243214885,243215020⟩]
theorem checked50819 : checkPrefixCuts (2^48) 6664880129 10 Manual.Count131072.C050819.packed 64 cuts50819 = true := by
 decide +kernel
def pointBounds50819 : List (Nat × Nat × Nat) := [(6664945664,111859102460090,111859489697239)]
theorem point_links_checked50819 : (cuts50819.take 1).map (fun c => (6664880129-1+2*2^10*c.k,111858980324144+c.lower,111859367561223+c.upper)) = pointBounds50819 := by
 decide +kernel
def cuts50820 : List PrefixCut := [⟨64,242618853,242618992⟩]
theorem checked50820 : checkPrefixCuts (2^48) 6665011201 10 Manual.Count131072.C050820.packed 64 cuts50820 = true := by
 decide +kernel
def cuts50821 : List PrefixCut := [⟨6,23480353,23480367⟩,
⟨64,246161450,246161595⟩]
theorem checked50821 : checkPrefixCuts (2^48) 6665142273 10 Manual.Count131072.C050821.packed 64 cuts50821 = true := by
 decide +kernel
def pointBounds50821 : List (Nat × Nat × Nat) := [(6665154560,111859489638235,111859876875602)]
theorem point_links_checked50821 : (cuts50821.take 1).map (fun c => (6665142273-1+2*2^10*c.k,111859466157882+c.lower,111859853395235+c.upper)) = pointBounds50821 := by
 decide +kernel
def cuts50822 : List PrefixCut := [⟨44,169721485,169721578⟩,
⟨64,245649871,245650007⟩]
theorem checked50822 : checkPrefixCuts (2^48) 6665273345 10 Manual.Count131072.C050822.packed 64 cuts50822 = true := by
 decide +kernel
def pointBounds50822 : List (Nat × Nat × Nat) := [(6665363456,111859882040817,111860269278408)]
theorem point_links_checked50822 : (cuts50822.take 1).map (fun c => (6665273345-1+2*2^10*c.k,111859712319332+c.lower,111860099556830+c.upper)) = pointBounds50822 := by
 decide +kernel
def cuts50823 : List PrefixCut := [⟨64,248220972,248221111⟩]
theorem checked50823 : checkPrefixCuts (2^48) 6665404417 10 Manual.Count131072.C050823.packed 64 cuts50823 = true := by
 decide +kernel
def cuts50824 : List PrefixCut := [⟨18,67311886,67311924⟩,
⟨64,242726442,242726580⟩]
theorem checked50824 : checkPrefixCuts (2^48) 6665535489 10 Manual.Count131072.C050824.packed 64 cuts50824 = true := by
 decide +kernel
def pointBounds50824 : List (Nat × Nat × Nat) := [(6665572352,111860273502061,111860660739872)]
theorem point_links_checked50824 : (cuts50824.take 1).map (fun c => (6665535489-1+2*2^10*c.k,111860206190175+c.lower,111860593427948+c.upper)) = pointBounds50824 := by
 decide +kernel
def cuts50825 : List PrefixCut := [⟨56,212740664,212740789⟩,
⟨64,243946262,243946406⟩]
theorem checked50825 : checkPrefixCuts (2^48) 6665666561 10 Manual.Count131072.C050825.packed 64 cuts50825 = true := by
 decide +kernel
def pointBounds50825 : List (Nat × Nat × Nat) := [(6665781248,111860661657281,111861048895317)]
theorem point_links_checked50825 : (cuts50825.take 1).map (fun c => (6665666561-1+2*2^10*c.k,111860448916617+c.lower,111860836154528+c.upper)) = pointBounds50825 := by
 decide +kernel
def cuts50826 : List PrefixCut := [⟨64,241196777,241196913⟩]
theorem checked50826 : checkPrefixCuts (2^48) 6665797633 10 Manual.Count131072.C050826.packed 64 cuts50826 = true := by
 decide +kernel
def cuts50827 : List PrefixCut := [⟨30,115529559,115529623⟩,
⟨64,244950091,244950233⟩]
theorem checked50827 : checkPrefixCuts (2^48) 6665928705 10 Manual.Count131072.C050827.packed 64 cuts50827 = true := by
 decide +kernel
def pointBounds50827 : List (Nat × Nat × Nat) := [(6665990144,111861049589215,111861436827470)]
theorem point_links_checked50827 : (cuts50827.take 1).map (fun c => (6665928705-1+2*2^10*c.k,111860934059656+c.lower,111861321297847+c.upper)) = pointBounds50827 := by
 decide +kernel
def cuts50828 : List PrefixCut := [⟨64,243974102,243974239⟩]
theorem checked50828 : checkPrefixCuts (2^48) 6666059777 10 Manual.Count131072.C050828.packed 64 cuts50828 = true := by
 decide +kernel
def cuts50829 : List PrefixCut := [⟨4,14187339,14187347⟩,
⟨64,245784930,245785070⟩]
theorem checked50829 : checkPrefixCuts (2^48) 6666190849 10 Manual.Count131072.C050829.packed 64 cuts50829 = true := by
 decide +kernel
def pointBounds50829 : List (Nat × Nat × Nat) := [(6666199040,111861437171188,111861824409666)]
theorem point_links_checked50829 : (cuts50829.take 1).map (fun c => (6666190849-1+2*2^10*c.k,111861422983849+c.lower,111861810222319+c.upper)) = pointBounds50829 := by
 decide +kernel
def cuts50830 : List PrefixCut := [⟨42,160152393,160152483⟩,
⟨64,243964512,243964648⟩]
theorem checked50830 : checkPrefixCuts (2^48) 6666321921 10 Manual.Count131072.C050830.packed 64 cuts50830 = true := by
 decide +kernel
def pointBounds50830 : List (Nat × Nat × Nat) := [(6666407936,111861828921172,111862216159872)]
theorem point_links_checked50830 : (cuts50830.take 1).map (fun c => (6666321921-1+2*2^10*c.k,111861668768779+c.lower,111862056007389+c.upper)) = pointBounds50830 := by
 decide +kernel
def cuts50831 : List PrefixCut := [⟨64,246366401,246366539⟩]
theorem checked50831 : checkPrefixCuts (2^48) 6666452993 10 Manual.Count131072.C050831.packed 64 cuts50831 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000025
