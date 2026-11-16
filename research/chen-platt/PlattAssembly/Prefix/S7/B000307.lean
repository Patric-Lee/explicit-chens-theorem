import PlattAssemblyKernel
import PlattCertificates.Count131072.C069824
import PlattCertificates.Count131072.C069825
import PlattCertificates.Count131072.C069826
import PlattCertificates.Count131072.C069827
import PlattCertificates.Count131072.C069828
import PlattCertificates.Count131072.C069829
import PlattCertificates.Count131072.C069830
import PlattCertificates.Count131072.C069831
import PlattCertificates.Count131072.C069832
import PlattCertificates.Count131072.C069833
import PlattCertificates.Count131072.C069834
import PlattCertificates.Count131072.C069835
import PlattCertificates.Count131072.C069836
import PlattCertificates.Count131072.C069837
import PlattCertificates.Count131072.C069838
import PlattCertificates.Count131072.C069839
import PlattCertificates.Count131072.C069840
import PlattCertificates.Count131072.C069841
import PlattCertificates.Count131072.C069842
import PlattCertificates.Count131072.C069843
import PlattCertificates.Count131072.C069844
import PlattCertificates.Count131072.C069845
import PlattCertificates.Count131072.C069846
import PlattCertificates.Count131072.C069847
import PlattCertificates.Count131072.C069848
import PlattCertificates.Count131072.C069849
import PlattCertificates.Count131072.C069850
import PlattCertificates.Count131072.C069851
import PlattCertificates.Count131072.C069852
import PlattCertificates.Count131072.C069853
import PlattCertificates.Count131072.C069854
import PlattCertificates.Count131072.C069855
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000307
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69824 : List PrefixCut := [⟨22,60162824,60162859⟩,
⟨64,174154733,174154835⟩]
theorem checked69824 : checkPrefixCuts (2^48) 9155903489 10 Manual.Count131072.C069824.packed 64 cuts69824 = true := by
 decide +kernel
def pointBounds69824 : List (Nat × Nat × Nat) := [(9155948544,115782917008430,115783306495512)]
theorem point_links_checked69824 : (cuts69824.take 1).map (fun c => (9155903489-1+2*2^10*c.k,115782856845606+c.lower,115783246332653+c.upper)) = pointBounds69824 := by
 decide +kernel
def cuts69825 : List PrefixCut := [⟨64,176242680,176242781⟩]
theorem checked69825 : checkPrefixCuts (2^48) 9156034561 10 Manual.Count131072.C069825.packed 64 cuts69825 = true := by
 decide +kernel
def cuts69826 : List PrefixCut := [⟨34,93669204,93669255⟩,
⟨64,176854975,176855078⟩]
theorem checked69826 : checkPrefixCuts (2^48) 9156165633 10 Manual.Count131072.C069826.packed 64 cuts69826 = true := by
 decide +kernel
def pointBounds69826 : List (Nat × Nat × Nat) := [(9156235264,115783300912223,115783690399524)]
theorem point_links_checked69826 : (cuts69826.take 1).map (fun c => (9156165633-1+2*2^10*c.k,115783207243019+c.lower,115783596730269+c.upper)) = pointBounds69826 := by
 decide +kernel
def cuts69827 : List PrefixCut := [⟨64,174762072,174762172⟩]
theorem checked69827 : checkPrefixCuts (2^48) 9156296705 10 Manual.Count131072.C069827.packed 64 cuts69827 = true := by
 decide +kernel
def cuts69828 : List PrefixCut := [⟨46,125943948,125944022⟩,
⟨64,176296577,176296682⟩]
theorem checked69828 : checkPrefixCuts (2^48) 9156427777 10 Manual.Count131072.C069828.packed 64 cuts69828 = true := by
 decide +kernel
def pointBounds69828 : List (Nat × Nat × Nat) := [(9156521984,115783684804014,115784074291541)]
theorem point_links_checked69828 : (cuts69828.take 1).map (fun c => (9156427777-1+2*2^10*c.k,115783558860066+c.lower,115783948347519+c.upper)) = pointBounds69828 := by
 decide +kernel
def cuts69829 : List PrefixCut := [⟨64,178507349,178507448⟩]
theorem checked69829 : checkPrefixCuts (2^48) 9156558849 10 Manual.Count131072.C069829.packed 64 cuts69829 = true := by
 decide +kernel
def cuts69830 : List PrefixCut := [⟨58,158186025,158186121⟩,
⟨64,175000471,175000576⟩]
theorem checked69830 : checkPrefixCuts (2^48) 9156689921 10 Manual.Count131072.C069830.packed 64 cuts69830 = true := by
 decide +kernel
def pointBounds69830 : List (Nat × Nat × Nat) := [(9156808704,115784071850017,115784461337770)]
theorem point_links_checked69830 : (cuts69830.take 1).map (fun c => (9156689921-1+2*2^10*c.k,115783913663992+c.lower,115784303151649+c.upper)) = pointBounds69830 := by
 decide +kernel
def cuts69831 : List PrefixCut := [⟨64,175797177,175797280⟩]
theorem checked69831 : checkPrefixCuts (2^48) 9156820993 10 Manual.Count131072.C069831.packed 64 cuts69831 = true := by
 decide +kernel
def cuts69832 : List PrefixCut := [⟨64,176809043,176809151⟩]
theorem checked69832 : checkPrefixCuts (2^48) 9156952065 10 Manual.Count131072.C069832.packed 64 cuts69832 = true := by
 decide +kernel
def cuts69833 : List PrefixCut := [⟨6,17029110,17029122⟩,
⟨64,177359802,177359906⟩]
theorem checked69833 : checkPrefixCuts (2^48) 9157083137 10 Manual.Count131072.C069833.packed 64 cuts69833 = true := by
 decide +kernel
def pointBounds69833 : List (Nat × Nat × Nat) := [(9157095424,115784458299793,115784847787778)]
theorem point_links_checked69833 : (cuts69833.take 1).map (fun c => (9157083137-1+2*2^10*c.k,115784441270683+c.lower,115784830758656+c.upper)) = pointBounds69833 := by
 decide +kernel
def cuts69834 : List PrefixCut := [⟨64,173976107,173976208⟩]
theorem checked69834 : checkPrefixCuts (2^48) 9157214209 10 Manual.Count131072.C069834.packed 64 cuts69834 = true := by
 decide +kernel
def cuts69835 : List PrefixCut := [⟨18,49487450,49487479⟩,
⟨64,175326066,175326165⟩]
theorem checked69835 : checkPrefixCuts (2^48) 9157345281 10 Manual.Count131072.C069835.packed 64 cuts69835 = true := by
 decide +kernel
def pointBounds69835 : List (Nat × Nat × Nat) := [(9157382144,115784842094042,115785231582249)]
theorem point_links_checked69835 : (cuts69835.take 1).map (fun c => (9157345281-1+2*2^10*c.k,115784792606592+c.lower,115785182094770+c.upper)) = pointBounds69835 := by
 decide +kernel
def cuts69836 : List PrefixCut := [⟨64,174555143,174555242⟩]
theorem checked69836 : checkPrefixCuts (2^48) 9157476353 10 Manual.Count131072.C069836.packed 64 cuts69836 = true := by
 decide +kernel
def cuts69837 : List PrefixCut := [⟨30,82773730,82773784⟩,
⟨64,175321042,175321155⟩]
theorem checked69837 : checkPrefixCuts (2^48) 9157607425 10 Manual.Count131072.C069837.packed 64 cuts69837 = true := by
 decide +kernel
def pointBounds69837 : List (Nat × Nat × Nat) := [(9157668864,115785225261531,115785614749961)]
theorem point_links_checked69837 : (cuts69837.take 1).map (fun c => (9157607425-1+2*2^10*c.k,115785142487801+c.lower,115785531976177+c.upper)) = pointBounds69837 := by
 decide +kernel
def cuts69838 : List PrefixCut := [⟨64,175902505,175902615⟩]
theorem checked69838 : checkPrefixCuts (2^48) 9157738497 10 Manual.Count131072.C069838.packed 64 cuts69838 = true := by
 decide +kernel
def cuts69839 : List PrefixCut := [⟨42,114490496,114490571⟩,
⟨64,176084406,176084520⟩]
theorem checked69839 : checkPrefixCuts (2^48) 9157869569 10 Manual.Count131072.C069839.packed 64 cuts69839 = true := by
 decide +kernel
def pointBounds69839 : List (Nat × Nat × Nat) := [(9157955584,115785608201844,115785997690518)]
theorem point_links_checked69839 : (cuts69839.take 1).map (fun c => (9157869569-1+2*2^10*c.k,115785493711348+c.lower,115785883199947+c.upper)) = pointBounds69839 := by
 decide +kernel
def cuts69840 : List PrefixCut := [⟨64,175159841,175159943⟩]
theorem checked69840 : checkPrefixCuts (2^48) 9158000641 10 Manual.Count131072.C069840.packed 64 cuts69840 = true := by
 decide +kernel
def cuts69841 : List PrefixCut := [⟨54,149278846,149278932⟩,
⟨64,177493176,177493278⟩]
theorem checked69841 : checkPrefixCuts (2^48) 9158131713 10 Manual.Count131072.C069841.packed 64 cuts69841 = true := by
 decide +kernel
def pointBounds69841 : List (Nat × Nat × Nat) := [(9158242304,115785994234441,115786383723342)]
theorem point_links_checked69841 : (cuts69841.take 1).map (fun c => (9158131713-1+2*2^10*c.k,115785844955595+c.lower,115786234444410+c.upper)) = pointBounds69841 := by
 decide +kernel
def cuts69842 : List PrefixCut := [⟨64,173556642,173556751⟩]
theorem checked69842 : checkPrefixCuts (2^48) 9158262785 10 Manual.Count131072.C069842.packed 64 cuts69842 = true := by
 decide +kernel
def cuts69843 : List PrefixCut := [⟨64,172755089,172755191⟩]
theorem checked69843 : checkPrefixCuts (2^48) 9158393857 10 Manual.Count131072.C069843.packed 64 cuts69843 = true := by
 decide +kernel
def cuts69844 : List PrefixCut := [⟨2,5593523,5593526⟩,
⟨64,175487902,175488007⟩]
theorem checked69844 : checkPrefixCuts (2^48) 9158524929 10 Manual.Count131072.C069844.packed 64 cuts69844 = true := by
 decide +kernel
def pointBounds69844 : List (Nat × Nat × Nat) := [(9158529024,115786374354025,115786763843156)]
theorem point_links_checked69844 : (cuts69844.take 1).map (fun c => (9158524929-1+2*2^10*c.k,115786368760502+c.lower,115786758249630+c.upper)) = pointBounds69844 := by
 decide +kernel
def cuts69845 : List PrefixCut := [⟨64,176038551,176038661⟩]
theorem checked69845 : checkPrefixCuts (2^48) 9158656001 10 Manual.Count131072.C069845.packed 64 cuts69845 = true := by
 decide +kernel
def cuts69846 : List PrefixCut := [⟨14,39245686,39245709⟩,
⟨64,176988758,176988862⟩]
theorem checked69846 : checkPrefixCuts (2^48) 9158787073 10 Manual.Count131072.C069846.packed 64 cuts69846 = true := by
 decide +kernel
def pointBounds69846 : List (Nat × Nat × Nat) := [(9158815744,115786759532641,115787149022007)]
theorem point_links_checked69846 : (cuts69846.take 1).map (fun c => (9158787073-1+2*2^10*c.k,115786720286955+c.lower,115787109776298+c.upper)) = pointBounds69846 := by
 decide +kernel
def cuts69847 : List PrefixCut := [⟨64,174773509,174773614⟩]
theorem checked69847 : checkPrefixCuts (2^48) 9158918145 10 Manual.Count131072.C069847.packed 64 cuts69847 = true := by
 decide +kernel
def cuts69848 : List PrefixCut := [⟨26,71328510,71328552⟩,
⟨64,176830029,176830131⟩]
theorem checked69848 : checkPrefixCuts (2^48) 9159049217 10 Manual.Count131072.C069848.packed 64 cuts69848 = true := by
 decide +kernel
def pointBounds69848 : List (Nat × Nat × Nat) := [(9159102464,115787143377732,115787532867326)]
theorem point_links_checked69848 : (cuts69848.take 1).map (fun c => (9159049217-1+2*2^10*c.k,115787072049222+c.lower,115787461538774+c.upper)) = pointBounds69848 := by
 decide +kernel
def cuts69849 : List PrefixCut := [⟨64,177472849,177472955⟩]
theorem checked69849 : checkPrefixCuts (2^48) 9159180289 10 Manual.Count131072.C069849.packed 64 cuts69849 = true := by
 decide +kernel
def cuts69850 : List PrefixCut := [⟨38,103808905,103808970⟩,
⟨64,178084909,178085017⟩]
theorem checked69850 : checkPrefixCuts (2^48) 9159311361 10 Manual.Count131072.C069850.packed 64 cuts69850 = true := by
 decide +kernel
def pointBounds69850 : List (Nat × Nat × Nat) := [(9159389184,115787530161005,115787919650830)]
theorem point_links_checked69850 : (cuts69850.take 1).map (fun c => (9159311361-1+2*2^10*c.k,115787426352100+c.lower,115787815841860+c.upper)) = pointBounds69850 := by
 decide +kernel
def cuts69851 : List PrefixCut := [⟨64,175777606,175777708⟩]
theorem checked69851 : checkPrefixCuts (2^48) 9159442433 10 Manual.Count131072.C069851.packed 64 cuts69851 = true := by
 decide +kernel
def cuts69852 : List PrefixCut := [⟨50,137393644,137393726⟩,
⟨64,176113116,176113220⟩]
theorem checked69852 : checkPrefixCuts (2^48) 9159573505 10 Manual.Count131072.C069852.packed 64 cuts69852 = true := by
 decide +kernel
def pointBounds69852 : List (Nat × Nat × Nat) := [(9159675904,115787917608259,115788307098311)]
theorem point_links_checked69852 : (cuts69852.take 1).map (fun c => (9159573505-1+2*2^10*c.k,115787780214615+c.lower,115788169704585+c.upper)) = pointBounds69852 := by
 decide +kernel
def cuts69853 : List PrefixCut := [⟨64,175588205,175588304⟩]
theorem checked69853 : checkPrefixCuts (2^48) 9159704577 10 Manual.Count131072.C069853.packed 64 cuts69853 = true := by
 decide +kernel
def cuts69854 : List PrefixCut := [⟨62,168610232,168610332⟩,
⟨64,174510165,174510269⟩]
theorem checked69854 : checkPrefixCuts (2^48) 9159835649 10 Manual.Count131072.C069854.packed 64 cuts69854 = true := by
 decide +kernel
def pointBounds69854 : List (Nat × Nat × Nat) := [(9159962624,115788300526168,115788690016441)]
theorem point_links_checked69854 : (cuts69854.take 1).map (fun c => (9159835649-1+2*2^10*c.k,115788131915936+c.lower,115788521406109+c.upper)) = pointBounds69854 := by
 decide +kernel
def cuts69855 : List PrefixCut := [⟨64,175060776,175060883⟩]
theorem checked69855 : checkPrefixCuts (2^48) 9159966721 10 Manual.Count131072.C069855.packed 64 cuts69855 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000307
