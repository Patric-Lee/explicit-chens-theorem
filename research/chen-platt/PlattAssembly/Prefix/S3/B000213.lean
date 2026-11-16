import PlattAssemblyKernel
import PlattCertificates.Count131072.C026816
import PlattCertificates.Count131072.C026817
import PlattCertificates.Count131072.C026818
import PlattCertificates.Count131072.C026819
import PlattCertificates.Count131072.C026820
import PlattCertificates.Count131072.C026821
import PlattCertificates.Count131072.C026822
import PlattCertificates.Count131072.C026823
import PlattCertificates.Count131072.C026824
import PlattCertificates.Count131072.C026825
import PlattCertificates.Count131072.C026826
import PlattCertificates.Count131072.C026827
import PlattCertificates.Count131072.C026828
import PlattCertificates.Count131072.C026829
import PlattCertificates.Count131072.C026830
import PlattCertificates.Count131072.C026831
import PlattCertificates.Count131072.C026832
import PlattCertificates.Count131072.C026833
import PlattCertificates.Count131072.C026834
import PlattCertificates.Count131072.C026835
import PlattCertificates.Count131072.C026836
import PlattCertificates.Count131072.C026837
import PlattCertificates.Count131072.C026838
import PlattCertificates.Count131072.C026839
import PlattCertificates.Count131072.C026840
import PlattCertificates.Count131072.C026841
import PlattCertificates.Count131072.C026842
import PlattCertificates.Count131072.C026843
import PlattCertificates.Count131072.C026844
import PlattCertificates.Count131072.C026845
import PlattCertificates.Count131072.C026846
import PlattCertificates.Count131072.C026847
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000213
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26816 : List PrefixCut := [⟨16,61194248,61194281⟩,
⟨124,465628923,465629178⟩,
⟨128,481546879,481547143⟩]
theorem checked26816 : checkPrefixCuts (2^48) 3518758913 9 Manual.Count131072.C026816.packed 128 cuts26816 = true := by
 decide +kernel
def pointBounds26816 : List (Nat × Nat × Nat) := [(3518775296,103796454205889,103796836725401),(3518885888,103796858640564,103797241160298)]
theorem point_links_checked26816 : (cuts26816.take 2).map (fun c => (3518758913-1+2*2^9*c.k,103796393011641+c.lower,103796775531120+c.upper)) = pointBounds26816 := by
 decide +kernel
def cuts26817 : List PrefixCut := [⟨104,389943813,389944032⟩,
⟨128,481528912,481529183⟩]
theorem checked26817 : checkPrefixCuts (2^48) 3518889985 9 Manual.Count131072.C026817.packed 128 cuts26817 = true := by
 decide +kernel
def pointBounds26817 : List (Nat × Nat × Nat) := [(3518996480,103797264502333,103797647022295)]
theorem point_links_checked26817 : (cuts26817.take 1).map (fun c => (3518889985-1+2*2^9*c.k,103796874558520+c.lower,103797257078263+c.upper)) = pointBounds26817 := by
 decide +kernel
def cuts26818 : List PrefixCut := [⟨84,316103602,316103778⟩,
⟨128,477751760,477752028⟩]
theorem checked26818 : checkPrefixCuts (2^48) 3519021057 9 Manual.Count131072.C026818.packed 128 cuts26818 = true := by
 decide +kernel
def pointBounds26818 : List (Nat × Nat × Nat) := [(3519107072,103797672191034,103798054711224)]
theorem point_links_checked26818 : (cuts26818.take 1).map (fun c => (3519021057-1+2*2^9*c.k,103797356087432+c.lower,103797738607446+c.upper)) = pointBounds26818 := by
 decide +kernel
def cuts26819 : List PrefixCut := [⟨64,236029754,236029889⟩,
⟨128,471095372,471095642⟩]
theorem checked26819 : checkPrefixCuts (2^48) 3519152129 9 Manual.Count131072.C026819.packed 128 cuts26819 = true := by
 decide +kernel
def pointBounds26819 : List (Nat × Nat × Nat) := [(3519217664,103798069868946,103798452389363)]
theorem point_links_checked26819 : (cuts26819.take 1).map (fun c => (3519152129-1+2*2^9*c.k,103797833839192+c.lower,103798216359474+c.upper)) = pointBounds26819 := by
 decide +kernel
def cuts26820 : List PrefixCut := [⟨44,162199910,162200003⟩,
⟨128,472997316,472997586⟩]
theorem checked26820 : checkPrefixCuts (2^48) 3519283201 9 Manual.Count131072.C026820.packed 128 cuts26820 = true := by
 decide +kernel
def pointBounds26820 : List (Nat × Nat × Nat) := [(3519328256,103798467134474,103798849655119)]
theorem point_links_checked26820 : (cuts26820.take 1).map (fun c => (3519283201-1+2*2^9*c.k,103798304934564+c.lower,103798687455116+c.upper)) = pointBounds26820 := by
 decide +kernel
def cuts26821 : List PrefixCut := [⟨24,90774454,90774504⟩,
⟨128,478658023,478658292⟩]
theorem checked26821 : checkPrefixCuts (2^48) 3519414273 9 Manual.Count131072.C026821.packed 128 cuts26821 = true := by
 decide +kernel
def pointBounds26821 : List (Nat × Nat × Nat) := [(3519438848,103798868706334,103799251227206)]
theorem point_links_checked26821 : (cuts26821.take 1).map (fun c => (3519414273-1+2*2^9*c.k,103798777931880+c.lower,103799160452702+c.upper)) = pointBounds26821 := by
 decide +kernel
def cuts26822 : List PrefixCut := [⟨4,14315479,14315487⟩,
⟨112,413622836,413623066⟩,
⟨128,475681107,475681372⟩]
theorem checked26822 : checkPrefixCuts (2^48) 3519545345 9 Manual.Count131072.C026822.packed 128 cuts26822 = true := by
 decide +kernel
def pointBounds26822 : List (Nat × Nat × Nat) := [(3519549440,103799270905382,103799653426481),(3519660032,103799670212739,103800052734060)]
theorem point_links_checked26822 : (cuts26822.take 2).map (fun c => (3519545345-1+2*2^9*c.k,103799256589903+c.lower,103799639110994+c.upper)) = pointBounds26822 := by
 decide +kernel
def cuts26823 : List PrefixCut := [⟨92,344433964,344434156⟩,
⟨128,478462432,478462699⟩]
theorem checked26823 : checkPrefixCuts (2^48) 3519676417 9 Manual.Count131072.C026823.packed 128 cuts26823 = true := by
 decide +kernel
def pointBounds26823 : List (Nat × Nat × Nat) := [(3519770624,103800076704974,103800459226522)]
theorem point_links_checked26823 : (cuts26823.take 1).map (fun c => (3519676417-1+2*2^9*c.k,103799732271010+c.lower,103800114792366+c.upper)) = pointBounds26823 := by
 decide +kernel
def cuts26824 : List PrefixCut := [⟨72,269252232,269252385⟩,
⟨128,481083506,481083776⟩]
theorem checked26824 : checkPrefixCuts (2^48) 3519807489 9 Manual.Count131072.C026824.packed 128 cuts26824 = true := by
 decide +kernel
def pointBounds26824 : List (Nat × Nat × Nat) := [(3519881216,103800479985674,103800862507450)]
theorem point_links_checked26824 : (cuts26824.take 1).map (fun c => (3519807489-1+2*2^9*c.k,103800210733442+c.lower,103800593255065+c.upper)) = pointBounds26824 := by
 decide +kernel
def cuts26825 : List PrefixCut := [⟨52,189517646,189517753⟩,
⟨128,466911923,466912184⟩]
theorem checked26825 : checkPrefixCuts (2^48) 3519938561 9 Manual.Count131072.C026825.packed 128 cuts26825 = true := by
 decide +kernel
def pointBounds26825 : List (Nat × Nat × Nat) := [(3519991808,103800881334594,103801263856594)]
theorem point_links_checked26825 : (cuts26825.take 1).map (fun c => (3519938561-1+2*2^9*c.k,103800691816948+c.lower,103801074338841+c.upper)) = pointBounds26825 := by
 decide +kernel
def cuts26826 : List PrefixCut := [⟨32,116665289,116665351⟩,
⟨128,479528396,479528658⟩]
theorem checked26826 : checkPrefixCuts (2^48) 3520069633 9 Manual.Count131072.C026826.packed 128 cuts26826 = true := by
 decide +kernel
def pointBounds26826 : List (Nat × Nat × Nat) := [(3520102400,103801275394160,103801657916376)]
theorem point_links_checked26826 : (cuts26826.take 1).map (fun c => (3520069633-1+2*2^9*c.k,103801158728871+c.lower,103801541251025+c.upper)) = pointBounds26826 := by
 decide +kernel
def cuts26827 : List PrefixCut := [⟨12,47815935,47815962⟩,
⟨120,452805109,452805366⟩,
⟨128,482149334,482149607⟩]
theorem checked26827 : checkPrefixCuts (2^48) 3520200705 9 Manual.Count131072.C026827.packed 128 cuts26827 = true := by
 decide +kernel
def pointBounds26827 : List (Nat × Nat × Nat) := [(3520212992,103801686073202,103802068595645),(3520323584,103802091062376,103802473585049)]
theorem point_links_checked26827 : (cuts26827.take 2).map (fun c => (3520200705-1+2*2^9*c.k,103801638257267+c.lower,103802020779683+c.upper)) = pointBounds26827 := by
 decide +kernel
def cuts26828 : List PrefixCut := [⟨100,372593814,372594024⟩,
⟨128,476854184,476854452⟩]
theorem checked26828 : checkPrefixCuts (2^48) 3520331777 9 Manual.Count131072.C026828.packed 128 cuts26828 = true := by
 decide +kernel
def pointBounds26828 : List (Nat × Nat × Nat) := [(3520434176,103802493000415,103802875523314)]
theorem point_links_checked26828 : (cuts26828.take 1).map (fun c => (3520331777-1+2*2^9*c.k,103802120406601+c.lower,103802502929290+c.upper)) = pointBounds26828 := by
 decide +kernel
def cuts26829 : List PrefixCut := [⟨80,299903797,299903970⟩,
⟨128,480834098,480834373⟩]
theorem checked26829 : checkPrefixCuts (2^48) 3520462849 9 Manual.Count131072.C026829.packed 128 cuts26829 = true := by
 decide +kernel
def pointBounds26829 : List (Nat × Nat × Nat) := [(3520544768,103802897164582,103803279687712)]
theorem point_links_checked26829 : (cuts26829.take 1).map (fun c => (3520462849-1+2*2^9*c.k,103802597260785+c.lower,103802979783742+c.upper)) = pointBounds26829 := by
 decide +kernel
def cuts26830 : List PrefixCut := [⟨60,226339226,226339349⟩,
⟨128,479696899,479697169⟩]
theorem checked26830 : checkPrefixCuts (2^48) 3520593921 9 Manual.Count131072.C026830.packed 128 cuts26830 = true := by
 decide +kernel
def pointBounds26830 : List (Nat × Nat × Nat) := [(3520655360,103803304434109,103803686957464)]
theorem point_links_checked26830 : (cuts26830.take 1).map (fun c => (3520593921-1+2*2^9*c.k,103803078094883+c.lower,103803460618115+c.upper)) = pointBounds26830 := by
 decide +kernel
def cuts26831 : List PrefixCut := [⟨40,148382620,148382703⟩,
⟨128,474802339,474802607⟩]
theorem checked26831 : checkPrefixCuts (2^48) 3520724993 9 Manual.Count131072.C026831.packed 128 cuts26831 = true := by
 decide +kernel
def pointBounds26831 : List (Nat × Nat × Nat) := [(3520765952,103803706174402,103804088697987)]
theorem point_links_checked26831 : (cuts26831.take 1).map (fun c => (3520724993-1+2*2^9*c.k,103803557791782+c.lower,103803940315284+c.upper)) = pointBounds26831 := by
 decide +kernel
def cuts26832 : List PrefixCut := [⟨20,76107441,76107482⟩,
⟨128,473345709,473345973⟩]
theorem checked26832 : checkPrefixCuts (2^48) 3520856065 9 Manual.Count131072.C026832.packed 128 cuts26832 = true := by
 decide +kernel
def pointBounds26832 : List (Nat × Nat × Nat) := [(3520876544,103804108701562,103804491225373),(3520987136,103804505939830,103804888463864)]
theorem point_links_checked26832 : (cuts26832.take 2).map (fun c => (3520856065-1+2*2^9*c.k,103804032594121+c.lower,103804415117891+c.upper)) = pointBounds26832 := by
 decide +kernel
def cuts26833 : List PrefixCut := [⟨108,405699489,405699712⟩,
⟨128,482601093,482601360⟩]
theorem checked26833 : checkPrefixCuts (2^48) 3520987137 9 Manual.Count131072.C026833.packed 128 cuts26833 = true := by
 decide +kernel
def pointBounds26833 : List (Nat × Nat × Nat) := [(3521097728,103804911639319,103805294163576)]
theorem point_links_checked26833 : (cuts26833.take 1).map (fun c => (3520987137-1+2*2^9*c.k,103804505939830+c.lower,103804888463864+c.upper)) = pointBounds26833 := by
 decide +kernel
def cuts26834 : List PrefixCut := [⟨88,328145649,328145835⟩,
⟨128,480664594,480664864⟩]
theorem checked26834 : checkPrefixCuts (2^48) 3521118209 9 Manual.Count131072.C026834.packed 128 cuts26834 = true := by
 decide +kernel
def pointBounds26834 : List (Nat × Nat × Nat) := [(3521208320,103805316686572,103805699211059)]
theorem point_links_checked26834 : (cuts26834.take 1).map (fun c => (3521118209-1+2*2^9*c.k,103804988540923+c.lower,103805371065224+c.upper)) = pointBounds26834 := by
 decide +kernel
def cuts26835 : List PrefixCut := [⟨68,253155050,253155191⟩,
⟨128,474971383,474971649⟩]
theorem checked26835 : checkPrefixCuts (2^48) 3521249281 9 Manual.Count131072.C026835.packed 128 cuts26835 = true := by
 decide +kernel
def pointBounds26835 : List (Nat × Nat × Nat) := [(3521318912,103805722360567,103806104885279)]
theorem point_links_checked26835 : (cuts26835.take 1).map (fun c => (3521249281-1+2*2^9*c.k,103805469205517+c.lower,103805851730088+c.upper)) = pointBounds26835 := by
 decide +kernel
def cuts26836 : List PrefixCut := [⟨48,177770001,177770102⟩,
⟨128,475593157,475593423⟩]
theorem checked26836 : checkPrefixCuts (2^48) 3521380353 9 Manual.Count131072.C026836.packed 128 cuts26836 = true := by
 decide +kernel
def pointBounds26836 : List (Nat × Nat × Nat) := [(3521429504,103806121946901,103806504471839)]
theorem point_links_checked26836 : (cuts26836.take 1).map (fun c => (3521380353-1+2*2^9*c.k,103805944176900+c.lower,103806326701737+c.upper)) = pointBounds26836 := by
 decide +kernel
def cuts26837 : List PrefixCut := [⟨28,101750653,101750713⟩,
⟨128,475015976,475016241⟩]
theorem checked26837 : checkPrefixCuts (2^48) 3521511425 9 Manual.Count131072.C026837.packed 128 cuts26837 = true := by
 decide +kernel
def pointBounds26837 : List (Nat × Nat × Nat) := [(3521540096,103806521520710,103806904045873)]
theorem point_links_checked26837 : (cuts26837.take 1).map (fun c => (3521511425-1+2*2^9*c.k,103806419770057+c.lower,103806802295160+c.upper)) = pointBounds26837 := by
 decide +kernel
def cuts26838 : List PrefixCut := [⟨8,29253310,29253326⟩,
⟨116,431199726,431199969⟩,
⟨128,475797501,475797770⟩]
theorem checked26838 : checkPrefixCuts (2^48) 3521642497 9 Manual.Count131072.C026838.packed 128 cuts26838 = true := by
 decide +kernel
def pointBounds26838 : List (Nat × Nat × Nat) := [(3521650688,103806924039343,103807306564727),(3521761280,103807325985759,103807708511370)]
theorem point_links_checked26838 : (cuts26838.take 2).map (fun c => (3521642497-1+2*2^9*c.k,103806894786033+c.lower,103807277311401+c.upper)) = pointBounds26838 := by
 decide +kernel
def cuts26839 : List PrefixCut := [⟨96,355178130,355178324⟩,
⟨128,472982545,472982804⟩]
theorem checked26839 : checkPrefixCuts (2^48) 3521773569 9 Manual.Count131072.C026839.packed 128 cuts26839 = true := by
 decide +kernel
def pointBounds26839 : List (Nat × Nat × Nat) := [(3521871872,103807725761664,103808108287495)]
theorem point_links_checked26839 : (cuts26839.take 1).map (fun c => (3521773569-1+2*2^9*c.k,103807370583534+c.lower,103807753109171+c.upper)) = pointBounds26839 := by
 decide +kernel
def cuts26840 : List PrefixCut := [⟨76,277083838,277083990⟩,
⟨128,473124758,473125016⟩]
theorem checked26840 : checkPrefixCuts (2^48) 3521904641 9 Manual.Count131072.C026840.packed 128 cuts26840 = true := by
 decide +kernel
def pointBounds26840 : List (Nat × Nat × Nat) := [(3521982464,103808120649917,103808503175965)]
theorem point_links_checked26840 : (cuts26840.take 1).map (fun c => (3521904641-1+2*2^9*c.k,103807843566079+c.lower,103808226091975+c.upper)) = pointBounds26840 := by
 decide +kernel
def cuts26841 : List PrefixCut := [⟨56,204828773,204828888⟩,
⟨128,471189172,471189435⟩]
theorem checked26841 : checkPrefixCuts (2^48) 3522035713 9 Manual.Count131072.C026841.packed 128 cuts26841 = true := by
 decide +kernel
def pointBounds26841 : List (Nat × Nat × Nat) := [(3522093056,103808521519610,103808904045879)]
theorem point_links_checked26841 : (cuts26841.take 1).map (fun c => (3522035713-1+2*2^9*c.k,103808316690837+c.lower,103808699216991+c.upper)) = pointBounds26841 := by
 decide +kernel
def cuts26842 : List PrefixCut := [⟨36,136094992,136095066⟩,
⟨128,478923293,478923559⟩]
theorem checked26842 : checkPrefixCuts (2^48) 3522166785 9 Manual.Count131072.C026842.packed 128 cuts26842 = true := by
 decide +kernel
def pointBounds26842 : List (Nat × Nat × Nat) := [(3522203648,103808923975001,103809306501492)]
theorem point_links_checked26842 : (cuts26842.take 1).map (fun c => (3522166785-1+2*2^9*c.k,103808787880009+c.lower,103809170406426+c.upper)) = pointBounds26842 := by
 decide +kernel
def cuts26843 : List PrefixCut := [⟨16,59694344,59694377⟩,
⟨124,460606128,460606385⟩,
⟨128,475309450,475309716⟩]
theorem checked26843 : checkPrefixCuts (2^48) 3522297857 9 Manual.Count131072.C026843.packed 128 cuts26843 = true := by
 decide +kernel
def pointBounds26843 : List (Nat × Nat × Nat) := [(3522314240,103809326497646,103809709024362),(3522424832,103809727409430,103810109936370)]
theorem point_links_checked26843 : (cuts26843.take 2).map (fun c => (3522297857-1+2*2^9*c.k,103809266803302+c.lower,103809649329985+c.upper)) = pointBounds26843 := by
 decide +kernel
def cuts26844 : List PrefixCut := [⟨104,388513221,388513441⟩,
⟨128,478967522,478967792⟩]
theorem checked26844 : checkPrefixCuts (2^48) 3522428929 9 Manual.Count131072.C026844.packed 128 cuts26844 = true := by
 decide +kernel
def pointBounds26844 : List (Nat × Nat × Nat) := [(3522535424,103810130625973,103810513153142)]
theorem point_links_checked26844 : (cuts26844.take 1).map (fun c => (3522428929-1+2*2^9*c.k,103809742112752+c.lower,103810124639701+c.upper)) = pointBounds26844 := by
 decide +kernel
def cuts26845 : List PrefixCut := [⟨84,310991688,310991863⟩,
⟨128,475353994,475354259⟩]
theorem checked26845 : checkPrefixCuts (2^48) 3522560001 9 Manual.Count131072.C026845.packed 128 cuts26845 = true := by
 decide +kernel
def pointBounds26845 : List (Nat × Nat × Nat) := [(3522646016,103810532071962,103810914599356)]
theorem point_links_checked26845 : (cuts26845.take 1).map (fun c => (3522560001-1+2*2^9*c.k,103810221080274+c.lower,103810603607493+c.upper)) = pointBounds26845 := by
 decide +kernel
def cuts26846 : List PrefixCut := [⟨64,237470614,237470749⟩,
⟨128,472140273,472140537⟩]
theorem checked26846 : checkPrefixCuts (2^48) 3522691073 9 Manual.Count131072.C026846.packed 128 cuts26846 = true := by
 decide +kernel
def pointBounds26846 : List (Nat × Nat × Nat) := [(3522756608,103810933904882,103811316432501)]
theorem point_links_checked26846 : (cuts26846.take 1).map (fun c => (3522691073-1+2*2^9*c.k,103810696434268+c.lower,103811078961752+c.upper)) = pointBounds26846 := by
 decide +kernel
def cuts26847 : List PrefixCut := [⟨44,169068162,169068253⟩,
⟨128,482589508,482589775⟩]
theorem checked26847 : checkPrefixCuts (2^48) 3522822145 9 Manual.Count131072.C026847.packed 128 cuts26847 = true := by
 decide +kernel
def pointBounds26847 : List (Nat × Nat × Nat) := [(3522867200,103811337642703,103811720170542)]
theorem point_links_checked26847 : (cuts26847.take 1).map (fun c => (3522822145-1+2*2^9*c.k,103811168574541+c.lower,103811551102289+c.upper)) = pointBounds26847 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000213
