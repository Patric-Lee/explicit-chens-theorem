import PlattAssemblyKernel
import PlattCertificates.Count131072.C068832
import PlattCertificates.Count131072.C068833
import PlattCertificates.Count131072.C068834
import PlattCertificates.Count131072.C068835
import PlattCertificates.Count131072.C068836
import PlattCertificates.Count131072.C068837
import PlattCertificates.Count131072.C068838
import PlattCertificates.Count131072.C068839
import PlattCertificates.Count131072.C068840
import PlattCertificates.Count131072.C068841
import PlattCertificates.Count131072.C068842
import PlattCertificates.Count131072.C068843
import PlattCertificates.Count131072.C068844
import PlattCertificates.Count131072.C068845
import PlattCertificates.Count131072.C068846
import PlattCertificates.Count131072.C068847
import PlattCertificates.Count131072.C068848
import PlattCertificates.Count131072.C068849
import PlattCertificates.Count131072.C068850
import PlattCertificates.Count131072.C068851
import PlattCertificates.Count131072.C068852
import PlattCertificates.Count131072.C068853
import PlattCertificates.Count131072.C068854
import PlattCertificates.Count131072.C068855
import PlattCertificates.Count131072.C068856
import PlattCertificates.Count131072.C068857
import PlattCertificates.Count131072.C068858
import PlattCertificates.Count131072.C068859
import PlattCertificates.Count131072.C068860
import PlattCertificates.Count131072.C068861
import PlattCertificates.Count131072.C068862
import PlattCertificates.Count131072.C068863
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000276
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68832 : List PrefixCut := [⟨29,82360139,82360187⟩,
⟨64,178784107,178784212⟩]
theorem checked68832 : checkPrefixCuts (2^48) 9025880065 10 Manual.Count131072.C068832.packed 64 cuts68832 = true := by
 decide +kernel
def pointBounds68832 : List (Nat × Nat × Nat) := [(9025939456,115607412092559,115607801476476)]
theorem point_links_checked68832 : (cuts68832.take 1).map (fun c => (9025880065-1+2*2^10*c.k,115607329732420+c.lower,115607719116289+c.upper)) = pointBounds68832 := by
 decide +kernel
def cuts68833 : List PrefixCut := [⟨64,177253474,177253576⟩]
theorem checked68833 : checkPrefixCuts (2^48) 9026011137 10 Manual.Count131072.C068833.packed 64 cuts68833 = true := by
 decide +kernel
def cuts68834 : List PrefixCut := [⟨39,110142844,110142905⟩,
⟨64,179714443,179714547⟩]
theorem checked68834 : checkPrefixCuts (2^48) 9026142209 10 Manual.Count131072.C068834.packed 64 cuts68834 = true := by
 decide +kernel
def pointBounds68834 : List (Nat × Nat × Nat) := [(9026222080,115607795912845,115608185296982)]
theorem point_links_checked68834 : (cuts68834.take 1).map (fun c => (9026142209-1+2*2^10*c.k,115607685770001+c.lower,115608075154077+c.upper)) = pointBounds68834 := by
 decide +kernel
def cuts68835 : List PrefixCut := [⟨64,179774190,179774288⟩]
theorem checked68835 : checkPrefixCuts (2^48) 9026273281 10 Manual.Count131072.C068835.packed 64 cuts68835 = true := by
 decide +kernel
def cuts68836 : List PrefixCut := [⟨49,134150671,134150749⟩,
⟨64,175374730,175374832⟩]
theorem checked68836 : checkPrefixCuts (2^48) 9026404353 10 Manual.Count131072.C068836.packed 64 cuts68836 = true := by
 decide +kernel
def pointBounds68836 : List (Nat × Nat × Nat) := [(9026504704,115608179409305,115608568793661)]
theorem point_links_checked68836 : (cuts68836.take 1).map (fun c => (9026404353-1+2*2^10*c.k,115608045258634+c.lower,115608434642912+c.upper)) = pointBounds68836 := by
 decide +kernel
def cuts68837 : List PrefixCut := [⟨64,176370046,176370143⟩]
theorem checked68837 : checkPrefixCuts (2^48) 9026535425 10 Manual.Count131072.C068837.packed 64 cuts68837 = true := by
 decide +kernel
def cuts68838 : List PrefixCut := [⟨59,164050545,164050644⟩,
⟨64,177708332,177708439⟩]
theorem checked68838 : checkPrefixCuts (2^48) 9026666497 10 Manual.Count131072.C068838.packed 64 cuts68838 = true := by
 decide +kernel
def pointBounds68838 : List (Nat × Nat × Nat) := [(9026787328,115608561053955,115608950438531)]
theorem point_links_checked68838 : (cuts68838.take 1).map (fun c => (9026666497-1+2*2^10*c.k,115608397003410+c.lower,115608786387887+c.upper)) = pointBounds68838 := by
 decide +kernel
def cuts68839 : List PrefixCut := [⟨64,178641207,178641312⟩]
theorem checked68839 : checkPrefixCuts (2^48) 9026797569 10 Manual.Count131072.C068839.packed 64 cuts68839 = true := by
 decide +kernel
def cuts68840 : List PrefixCut := [⟨64,177204248,177204361⟩]
theorem checked68840 : checkPrefixCuts (2^48) 9026928641 10 Manual.Count131072.C068840.packed 64 cuts68840 = true := by
 decide +kernel
def cuts68841 : List PrefixCut := [⟨5,13969187,13969195⟩,
⟨64,181847660,181847766⟩]
theorem checked68841 : checkPrefixCuts (2^48) 9027059713 10 Manual.Count131072.C068841.packed 64 cuts68841 = true := by
 decide +kernel
def pointBounds68841 : List (Nat × Nat × Nat) := [(9027069952,115608944526384,115609333911194)]
theorem point_links_checked68841 : (cuts68841.take 1).map (fun c => (9027059713-1+2*2^10*c.k,115608930557197+c.lower,115609319941999+c.upper)) = pointBounds68841 := by
 decide +kernel
def cuts68842 : List PrefixCut := [⟨64,179755930,179756036⟩]
theorem checked68842 : checkPrefixCuts (2^48) 9027190785 10 Manual.Count131072.C068842.packed 64 cuts68842 = true := by
 decide +kernel
def cuts68843 : List PrefixCut := [⟨15,42186917,42186942⟩,
⟨64,178537291,178537398⟩]
theorem checked68843 : checkPrefixCuts (2^48) 9027321857 10 Manual.Count131072.C068843.packed 64 cuts68843 = true := by
 decide +kernel
def pointBounds68843 : List (Nat × Nat × Nat) := [(9027352576,115609334347704,115609723732743)]
theorem point_links_checked68843 : (cuts68843.take 1).map (fun c => (9027321857-1+2*2^10*c.k,115609292160787+c.lower,115609681545801+c.upper)) = pointBounds68843 := by
 decide +kernel
def cuts68844 : List PrefixCut := [⟨64,175541446,175541554⟩]
theorem checked68844 : checkPrefixCuts (2^48) 9027452929 10 Manual.Count131072.C068844.packed 64 cuts68844 = true := by
 decide +kernel
def cuts68845 : List PrefixCut := [⟨25,70340586,70340625⟩,
⟨64,178157959,178158062⟩]
theorem checked68845 : checkPrefixCuts (2^48) 9027584001 10 Manual.Count131072.C068845.packed 64 cuts68845 = true := by
 decide +kernel
def pointBounds68845 : List (Nat × Nat × Nat) := [(9027635200,115609716580110,115610105965378)]
theorem point_links_checked68845 : (cuts68845.take 1).map (fun c => (9027584001-1+2*2^10*c.k,115609646239524+c.lower,115610035624753+c.upper)) = pointBounds68845 := by
 decide +kernel
def cuts68846 : List PrefixCut := [⟨64,179028370,179028475⟩]
theorem checked68846 : checkPrefixCuts (2^48) 9027715073 10 Manual.Count131072.C068846.packed 64 cuts68846 = true := by
 decide +kernel
def cuts68847 : List PrefixCut := [⟨35,99022586,99022646⟩,
⟨64,179867581,179867689⟩]
theorem checked68847 : checkPrefixCuts (2^48) 9027846145 10 Manual.Count131072.C068847.packed 64 cuts68847 = true := by
 decide +kernel
def pointBounds68847 : List (Nat × Nat × Nat) := [(9027917824,115610102448439,115610491833936)]
theorem point_links_checked68847 : (cuts68847.take 1).map (fun c => (9027846145-1+2*2^10*c.k,115610003425853+c.lower,115610392811290+c.upper)) = pointBounds68847 := by
 decide +kernel
def cuts68848 : List PrefixCut := [⟨64,176497767,176497866⟩]
theorem checked68848 : checkPrefixCuts (2^48) 9027977217 10 Manual.Count131072.C068848.packed 64 cuts68848 = true := by
 decide +kernel
def cuts68849 : List PrefixCut := [⟨45,123150956,123151027⟩,
⟨64,177617576,177617681⟩]
theorem checked68849 : checkPrefixCuts (2^48) 9028108289 10 Manual.Count131072.C068849.packed 64 cuts68849 = true := by
 decide +kernel
def pointBounds68849 : List (Nat × Nat × Nat) := [(9028200448,115610482942157,115610872327872)]
theorem point_links_checked68849 : (cuts68849.take 1).map (fun c => (9028108289-1+2*2^10*c.k,115610359791201+c.lower,115610749176845+c.upper)) = pointBounds68849 := by
 decide +kernel
def cuts68850 : List PrefixCut := [⟨64,179360925,179361029⟩]
theorem checked68850 : checkPrefixCuts (2^48) 9028239361 10 Manual.Count131072.C068850.packed 64 cuts68850 = true := by
 decide +kernel
def cuts68851 : List PrefixCut := [⟨55,153388459,153388556⟩,
⟨64,179420662,179420773⟩]
theorem checked68851 : checkPrefixCuts (2^48) 9028370433 10 Manual.Count131072.C068851.packed 64 cuts68851 = true := by
 decide +kernel
def pointBounds68851 : List (Nat × Nat × Nat) := [(9028483072,115610870158161,115611259544111)]
theorem point_links_checked68851 : (cuts68851.take 1).map (fun c => (9028370433-1+2*2^10*c.k,115610716769702+c.lower,115611106155555+c.upper)) = pointBounds68851 := by
 decide +kernel
def cuts68852 : List PrefixCut := [⟨64,176175770,176175879⟩]
theorem checked68852 : checkPrefixCuts (2^48) 9028501505 10 Manual.Count131072.C068852.packed 64 cuts68852 = true := by
 decide +kernel
def cuts68853 : List PrefixCut := [⟨64,175300290,175300398⟩]
theorem checked68853 : checkPrefixCuts (2^48) 9028632577 10 Manual.Count131072.C068853.packed 64 cuts68853 = true := by
 decide +kernel
def cuts68854 : List PrefixCut := [⟨1,2836957,2836958⟩,
⟨64,179880484,179880584⟩]
theorem checked68854 : checkPrefixCuts (2^48) 9028763649 10 Manual.Count131072.C068854.packed 64 cuts68854 = true := by
 decide +kernel
def pointBounds68854 : List (Nat × Nat × Nat) := [(9028765696,115611250503381,115611639889563)]
theorem point_links_checked68854 : (cuts68854.take 1).map (fun c => (9028763649-1+2*2^10*c.k,115611247666424+c.lower,115611637052605+c.upper)) = pointBounds68854 := by
 decide +kernel
def cuts68855 : List PrefixCut := [⟨64,180033739,180033841⟩]
theorem checked68855 : checkPrefixCuts (2^48) 9028894721 10 Manual.Count131072.C068855.packed 64 cuts68855 = true := by
 decide +kernel
def cuts68856 : List PrefixCut := [⟨11,29802735,29802754⟩,
⟨64,176789001,176789112⟩]
theorem checked68856 : checkPrefixCuts (2^48) 9029025793 10 Manual.Count131072.C068856.packed 64 cuts68856 = true := by
 decide +kernel
def pointBounds68856 : List (Nat × Nat × Nat) := [(9029048320,115611637383382,115612026769784)]
theorem point_links_checked68856 : (cuts68856.take 1).map (fun c => (9029025793-1+2*2^10*c.k,115611607580647+c.lower,115611996967030+c.upper)) = pointBounds68856 := by
 decide +kernel
def cuts68857 : List PrefixCut := [⟨64,177971059,177971162⟩]
theorem checked68857 : checkPrefixCuts (2^48) 9029156865 10 Manual.Count131072.C068857.packed 64 cuts68857 = true := by
 decide +kernel
def cuts68858 : List PrefixCut := [⟨21,58824337,58824367⟩,
⟨64,179901208,179901310⟩]
theorem checked68858 : checkPrefixCuts (2^48) 9029287937 10 Manual.Count131072.C068858.packed 64 cuts68858 = true := by
 decide +kernel
def pointBounds68858 : List (Nat × Nat × Nat) := [(9029330944,115612021165044,115612410551671)]
theorem point_links_checked68858 : (cuts68858.take 1).map (fun c => (9029287937-1+2*2^10*c.k,115611962340707+c.lower,115612351727304+c.upper)) = pointBounds68858 := by
 decide +kernel
def cuts68859 : List PrefixCut := [⟨64,175659078,175659183⟩]
theorem checked68859 : checkPrefixCuts (2^48) 9029419009 10 Manual.Count131072.C068859.packed 64 cuts68859 = true := by
 decide +kernel
def cuts68860 : List PrefixCut := [⟨31,86784321,86784373⟩,
⟨64,178524407,178524511⟩]
theorem checked68860 : checkPrefixCuts (2^48) 9029550081 10 Manual.Count131072.C068860.packed 64 cuts68860 = true := by
 decide +kernel
def pointBounds68860 : List (Nat × Nat × Nat) := [(9029613568,115612404685314,115612794072170)]
theorem point_links_checked68860 : (cuts68860.take 1).map (fun c => (9029550081-1+2*2^10*c.k,115612317900993+c.lower,115612707287797+c.upper)) = pointBounds68860 := by
 decide +kernel
def cuts68861 : List PrefixCut := [⟨64,177368443,177368548⟩]
theorem checked68861 : checkPrefixCuts (2^48) 9029681153 10 Manual.Count131072.C068861.packed 64 cuts68861 = true := by
 decide +kernel
def cuts68862 : List PrefixCut := [⟨41,115615419,115615486⟩,
⟨64,178768596,178768698⟩]
theorem checked68862 : checkPrefixCuts (2^48) 9029812225 10 Manual.Count131072.C068862.packed 64 cuts68862 = true := by
 decide +kernel
def pointBounds68862 : List (Nat × Nat × Nat) := [(9029896192,115612789409262,115613178796342)]
theorem point_links_checked68862 : (cuts68862.take 1).map (fun c => (9029812225-1+2*2^10*c.k,115612673793843+c.lower,115613063180856+c.upper)) = pointBounds68862 := by
 decide +kernel
def cuts68863 : List PrefixCut := [⟨64,178828335,178828438⟩]
theorem checked68863 : checkPrefixCuts (2^48) 9029943297 10 Manual.Count131072.C068863.packed 64 cuts68863 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000276
