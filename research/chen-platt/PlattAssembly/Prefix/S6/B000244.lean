import PlattAssemblyKernel
import PlattCertificates.Count131072.C057808
import PlattCertificates.Count131072.C057809
import PlattCertificates.Count131072.C057810
import PlattCertificates.Count131072.C057811
import PlattCertificates.Count131072.C057812
import PlattCertificates.Count131072.C057813
import PlattCertificates.Count131072.C057814
import PlattCertificates.Count131072.C057815
import PlattCertificates.Count131072.C057816
import PlattCertificates.Count131072.C057817
import PlattCertificates.Count131072.C057818
import PlattCertificates.Count131072.C057819
import PlattCertificates.Count131072.C057820
import PlattCertificates.Count131072.C057821
import PlattCertificates.Count131072.C057822
import PlattCertificates.Count131072.C057823
import PlattCertificates.Count131072.C057824
import PlattCertificates.Count131072.C057825
import PlattCertificates.Count131072.C057826
import PlattCertificates.Count131072.C057827
import PlattCertificates.Count131072.C057828
import PlattCertificates.Count131072.C057829
import PlattCertificates.Count131072.C057830
import PlattCertificates.Count131072.C057831
import PlattCertificates.Count131072.C057832
import PlattCertificates.Count131072.C057833
import PlattCertificates.Count131072.C057834
import PlattCertificates.Count131072.C057835
import PlattCertificates.Count131072.C057836
import PlattCertificates.Count131072.C057837
import PlattCertificates.Count131072.C057838
import PlattCertificates.Count131072.C057839
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000244
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57808 : List PrefixCut := [⟨64,213380095,213380219⟩]
theorem checked57808 : checkPrefixCuts (2^48) 7580942337 10 Manual.Count131072.C057808.packed 64 cuts57808 = true := by
 decide +kernel
def cuts57809 : List PrefixCut := [⟨52,173315242,173315339⟩,
⟨64,213636307,213636426⟩]
theorem checked57809 : checkPrefixCuts (2^48) 7581073409 10 Manual.Count131072.C057809.packed 64 cuts57809 = true := by
 decide +kernel
def pointBounds57809 : List (Nat × Nat × Nat) := [(7581179904,113457323750315,113457711895404)]
theorem point_links_checked57809 : (cuts57809.take 1).map (fun c => (7581073409-1+2*2^10*c.k,113457150435073+c.lower,113457538580065+c.upper)) = pointBounds57809 := by
 decide +kernel
def cuts57810 : List PrefixCut := [⟨64,216120161,216120284⟩]
theorem checked57810 : checkPrefixCuts (2^48) 7581204481 10 Manual.Count131072.C057810.packed 64 cuts57810 = true := by
 decide +kernel
def cuts57811 : List PrefixCut := [⟨40,134994315,134994390⟩,
⟨64,213183416,213183536⟩]
theorem checked57811 : checkPrefixCuts (2^48) 7581335553 10 Manual.Count131072.C057811.packed 64 cuts57811 = true := by
 decide +kernel
def pointBounds57811 : List (Nat × Nat × Nat) := [(7581417472,113457715185856,113458103331165)]
theorem point_links_checked57811 : (cuts57811.take 1).map (fun c => (7581335553-1+2*2^10*c.k,113457580191541+c.lower,113457968336775+c.upper)) = pointBounds57811 := by
 decide +kernel
def cuts57812 : List PrefixCut := [⟨64,214924652,214924777⟩]
theorem checked57812 : checkPrefixCuts (2^48) 7581466625 10 Manual.Count131072.C057812.packed 64 cuts57812 = true := by
 decide +kernel
def cuts57813 : List PrefixCut := [⟨28,92517806,92517857⟩,
⟨64,213138906,213139026⟩]
theorem checked57813 : checkPrefixCuts (2^48) 7581597697 10 Manual.Count131072.C057813.packed 64 cuts57813 = true := by
 decide +kernel
def pointBounds57813 : List (Nat × Nat × Nat) := [(7581655040,113458100817415,113458488962945)]
theorem point_links_checked57813 : (cuts57813.take 1).map (fun c => (7581597697-1+2*2^10*c.k,113458008299609+c.lower,113458396445088+c.upper)) = pointBounds57813 := by
 decide +kernel
def cuts57814 : List PrefixCut := [⟨64,213654969,213655092⟩]
theorem checked57814 : checkPrefixCuts (2^48) 7581728769 10 Manual.Count131072.C057814.packed 64 cuts57814 = true := by
 decide +kernel
def cuts57815 : List PrefixCut := [⟨16,54350565,54350596⟩,
⟨64,213020167,213020287⟩]
theorem checked57815 : checkPrefixCuts (2^48) 7581859841 10 Manual.Count131072.C057815.packed 64 cuts57815 = true := by
 decide +kernel
def pointBounds57815 : List (Nat × Nat × Nat) := [(7581892608,113458489444049,113458877589802)]
theorem point_links_checked57815 : (cuts57815.take 1).map (fun c => (7581859841-1+2*2^10*c.k,113458435093484+c.lower,113458823239206+c.upper)) = pointBounds57815 := by
 decide +kernel
def cuts57816 : List PrefixCut := [⟨64,213758965,213759088⟩]
theorem checked57816 : checkPrefixCuts (2^48) 7581990913 10 Manual.Count131072.C057816.packed 64 cuts57816 = true := by
 decide +kernel
def cuts57817 : List PrefixCut := [⟨4,13735686,13735694⟩,
⟨64,213755269,213755394⟩]
theorem checked57817 : checkPrefixCuts (2^48) 7582121985 10 Manual.Count131072.C057817.packed 64 cuts57817 = true := by
 decide +kernel
def pointBounds57817 : List (Nat × Nat × Nat) := [(7582130176,113458875608302,113459263754275)]
theorem point_links_checked57817 : (cuts57817.take 1).map (fun c => (7582121985-1+2*2^10*c.k,113458861872616+c.lower,113459250018581+c.upper)) = pointBounds57817 := by
 decide +kernel
def cuts57818 : List PrefixCut := [⟨56,186986417,186986522⟩,
⟨64,213825807,213825928⟩]
theorem checked57818 : checkPrefixCuts (2^48) 7582253057 10 Manual.Count131072.C057818.packed 64 cuts57818 = true := by
 decide +kernel
def pointBounds57818 : List (Nat × Nat × Nat) := [(7582367744,113459262614302,113459650760497)]
theorem point_links_checked57818 : (cuts57818.take 1).map (fun c => (7582253057-1+2*2^10*c.k,113459075627885+c.lower,113459463773975+c.upper)) = pointBounds57818 := by
 decide +kernel
def cuts57819 : List PrefixCut := [⟨64,210555388,210555509⟩]
theorem checked57819 : checkPrefixCuts (2^48) 7582384129 10 Manual.Count131072.C057819.packed 64 cuts57819 = true := by
 decide +kernel
def cuts57820 : List PrefixCut := [⟨44,144067964,144068048⟩,
⟨64,209660828,209660950⟩]
theorem checked57820 : checkPrefixCuts (2^48) 7582515201 10 Manual.Count131072.C057820.packed 64 cuts57820 = true := by
 decide +kernel
def pointBounds57820 : List (Nat × Nat × Nat) := [(7582605312,113459644077044,113460032223460)]
theorem point_links_checked57820 : (cuts57820.take 1).map (fun c => (7582515201-1+2*2^10*c.k,113459500009080+c.lower,113459888155412+c.upper)) = pointBounds57820 := by
 decide +kernel
def cuts57821 : List PrefixCut := [⟨64,213963197,213963318⟩]
theorem checked57821 : checkPrefixCuts (2^48) 7582646273 10 Manual.Count131072.C057821.packed 64 cuts57821 = true := by
 decide +kernel
def cuts57822 : List PrefixCut := [⟨32,105421174,105421235⟩,
⟨64,212251988,212252113⟩]
theorem checked57822 : checkPrefixCuts (2^48) 7582777345 10 Manual.Count131072.C057822.packed 64 cuts57822 = true := by
 decide +kernel
def pointBounds57822 : List (Nat × Nat × Nat) := [(7582842880,113460029054279,113460417200915)]
theorem point_links_checked57822 : (cuts57822.take 1).map (fun c => (7582777345-1+2*2^10*c.k,113459923633105+c.lower,113460311779680+c.upper)) = pointBounds57822 := by
 decide +kernel
def cuts57823 : List PrefixCut := [⟨64,214401240,214401359⟩]
theorem checked57823 : checkPrefixCuts (2^48) 7582908417 10 Manual.Count131072.C057823.packed 64 cuts57823 = true := by
 decide +kernel
def cuts57824 : List PrefixCut := [⟨20,68076073,68076112⟩,
⟨64,213729406,213729525⟩]
theorem checked57824 : checkPrefixCuts (2^48) 7583039489 10 Manual.Count131072.C057824.packed 64 cuts57824 = true := by
 decide +kernel
def pointBounds57824 : List (Nat × Nat × Nat) := [(7583080448,113460418362406,113460806509264)]
theorem point_links_checked57824 : (cuts57824.take 1).map (fun c => (7583039489-1+2*2^10*c.k,113460350286333+c.lower,113460738433152+c.upper)) = pointBounds57824 := by
 decide +kernel
def cuts57825 : List PrefixCut := [⟨64,212278096,212278215⟩]
theorem checked57825 : checkPrefixCuts (2^48) 7583170561 10 Manual.Count131072.C057825.packed 64 cuts57825 = true := by
 decide +kernel
def cuts57826 : List PrefixCut := [⟨8,25536965,25536981⟩,
⟨64,213425046,213425168⟩]
theorem checked57826 : checkPrefixCuts (2^48) 7583301633 10 Manual.Count131072.C057826.packed 64 cuts57826 = true := by
 decide +kernel
def pointBounds57826 : List (Nat × Nat × Nat) := [(7583318016,113460801830800,113461189977873)]
theorem point_links_checked57826 : (cuts57826.take 1).map (fun c => (7583301633-1+2*2^10*c.k,113460776293835+c.lower,113461164440892+c.upper)) = pointBounds57826 := by
 decide +kernel
def cuts57827 : List PrefixCut := [⟨60,199057292,199057406⟩,
⟨64,212048054,212048174⟩]
theorem checked57827 : checkPrefixCuts (2^48) 7583432705 10 Manual.Count131072.C057827.packed 64 cuts57827 = true := by
 decide +kernel
def pointBounds57827 : List (Nat × Nat × Nat) := [(7583555584,113461188776173,113461576923466)]
theorem point_links_checked57827 : (cuts57827.take 1).map (fun c => (7583432705-1+2*2^10*c.k,113460989718881+c.lower,113461377866060+c.upper)) = pointBounds57827 := by
 decide +kernel
def cuts57828 : List PrefixCut := [⟨64,212415552,212415676⟩]
theorem checked57828 : checkPrefixCuts (2^48) 7583563777 10 Manual.Count131072.C057828.packed 64 cuts57828 = true := by
 decide +kernel
def cuts57829 : List PrefixCut := [⟨48,162751724,162751816⟩,
⟨64,216086323,216086446⟩]
theorem checked57829 : checkPrefixCuts (2^48) 7583694849 10 Manual.Count131072.C057829.packed 64 cuts57829 = true := by
 decide +kernel
def pointBounds57829 : List (Nat × Nat × Nat) := [(7583793152,113461576934211,113461965081726)]
theorem point_links_checked57829 : (cuts57829.take 1).map (fun c => (7583694849-1+2*2^10*c.k,113461414182487+c.lower,113461802329910+c.upper)) = pointBounds57829 := by
 decide +kernel
def cuts57830 : List PrefixCut := [⟨64,219274472,219274595⟩]
theorem checked57830 : checkPrefixCuts (2^48) 7583825921 10 Manual.Count131072.C057830.packed 64 cuts57830 = true := by
 decide +kernel
def cuts57831 : List PrefixCut := [⟨36,118209152,118209223⟩,
⟨64,213703512,213703637⟩]
theorem checked57831 : checkPrefixCuts (2^48) 7583956993 10 Manual.Count131072.C057831.packed 64 cuts57831 = true := by
 decide +kernel
def pointBounds57831 : List (Nat × Nat × Nat) := [(7584030720,113461967752434,113462355900174)]
theorem point_links_checked57831 : (cuts57831.take 1).map (fun c => (7583956993-1+2*2^10*c.k,113461849543282+c.lower,113462237690951+c.upper)) = pointBounds57831 := by
 decide +kernel
def cuts57832 : List PrefixCut := [⟨64,217040067,217040194⟩]
theorem checked57832 : checkPrefixCuts (2^48) 7584088065 10 Manual.Count131072.C057832.packed 64 cuts57832 = true := by
 decide +kernel
def cuts57833 : List PrefixCut := [⟨24,79125155,79125200⟩,
⟨64,217370309,217370432⟩]
theorem checked57833 : checkPrefixCuts (2^48) 7584219137 10 Manual.Count131072.C057833.packed 64 cuts57833 = true := by
 decide +kernel
def pointBounds57833 : List (Nat × Nat × Nat) := [(7584268288,113462359412016,113462747559982)]
theorem point_links_checked57833 : (cuts57833.take 1).map (fun c => (7584219137-1+2*2^10*c.k,113462280286861+c.lower,113462668434782+c.upper)) = pointBounds57833 := by
 decide +kernel
def cuts57834 : List PrefixCut := [⟨64,211688392,211688508⟩]
theorem checked57834 : checkPrefixCuts (2^48) 7584350209 10 Manual.Count131072.C057834.packed 64 cuts57834 = true := by
 decide +kernel
def cuts57835 : List PrefixCut := [⟨12,39672611,39672635⟩,
⟨64,216806130,216806258⟩]
theorem checked57835 : checkPrefixCuts (2^48) 7584481281 10 Manual.Count131072.C057835.packed 64 cuts57835 = true := by
 decide +kernel
def pointBounds57835 : List (Nat × Nat × Nat) := [(7584505856,113462749018173,113463137166357)]
theorem point_links_checked57835 : (cuts57835.take 1).map (fun c => (7584481281-1+2*2^10*c.k,113462709345562+c.lower,113463097493722+c.upper)) = pointBounds57835 := by
 decide +kernel
def cuts57836 : List PrefixCut := [⟨64,210567745,210567863⟩]
theorem checked57836 : checkPrefixCuts (2^48) 7584612353 10 Manual.Count131072.C057836.packed 64 cuts57836 = true := by
 decide +kernel
def pointBounds57836 : List (Nat × Nat × Nat) := [(7584743424,113463136719437,113463524867843)]
theorem point_links_checked57836 : (cuts57836.take 1).map (fun c => (7584612353-1+2*2^10*c.k,113462926151692+c.lower,113463314299980+c.upper)) = pointBounds57836 := by
 decide +kernel
def cuts57837 : List PrefixCut := [⟨64,210489892,210490014⟩]
theorem checked57837 : checkPrefixCuts (2^48) 7584743425 10 Manual.Count131072.C057837.packed 64 cuts57837 = true := by
 decide +kernel
def cuts57838 : List PrefixCut := [⟨52,173673710,173673808⟩,
⟨64,213492145,213492265⟩]
theorem checked57838 : checkPrefixCuts (2^48) 7584874497 10 Manual.Count131072.C057838.packed 64 cuts57838 = true := by
 decide +kernel
def pointBounds57838 : List (Nat × Nat × Nat) := [(7584980992,113463520883039,113463909031665)]
theorem point_links_checked57838 : (cuts57838.take 1).map (fun c => (7584874497-1+2*2^10*c.k,113463347209329+c.lower,113463735357857+c.upper)) = pointBounds57838 := by
 decide +kernel
def cuts57839 : List PrefixCut := [⟨64,211892773,211892890⟩]
theorem checked57839 : checkPrefixCuts (2^48) 7585005569 10 Manual.Count131072.C057839.packed 64 cuts57839 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000244
