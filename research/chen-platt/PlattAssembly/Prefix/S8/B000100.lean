import PlattAssemblyKernel
import PlattCertificates.Count131072.C073200
import PlattCertificates.Count131072.C073201
import PlattCertificates.Count131072.C073202
import PlattCertificates.Count131072.C073203
import PlattCertificates.Count131072.C073204
import PlattCertificates.Count131072.C073205
import PlattCertificates.Count131072.C073206
import PlattCertificates.Count131072.C073207
import PlattCertificates.Count131072.C073208
import PlattCertificates.Count131072.C073209
import PlattCertificates.Count131072.C073210
import PlattCertificates.Count131072.C073211
import PlattCertificates.Count131072.C073212
import PlattCertificates.Count131072.C073213
import PlattCertificates.Count131072.C073214
import PlattCertificates.Count131072.C073215
import PlattCertificates.Count131072.C073216
import PlattCertificates.Count131072.C073217
import PlattCertificates.Count131072.C073218
import PlattCertificates.Count131072.C073219
import PlattCertificates.Count131072.C073220
import PlattCertificates.Count131072.C073221
import PlattCertificates.Count131072.C073222
import PlattCertificates.Count131072.C073223
import PlattCertificates.Count131072.C073224
import PlattCertificates.Count131072.C073225
import PlattCertificates.Count131072.C073226
import PlattCertificates.Count131072.C073227
import PlattCertificates.Count131072.C073228
import PlattCertificates.Count131072.C073229
import PlattCertificates.Count131072.C073230
import PlattCertificates.Count131072.C073231
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000100
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73200 : List PrefixCut := [⟨12,31377905,31377924⟩,
⟨64,167357667,167357772⟩]
theorem checked73200 : checkPrefixCuts (2^48) 9598402561 10 Manual.Count131072.C073200.packed 64 cuts73200 = true := by
 decide +kernel
def pointBounds73200 : List (Nat × Nat × Nat) := [(9598427136,116361495743527,116361885573262)]
theorem point_links_checked73200 : (cuts73200.take 1).map (fun c => (9598402561-1+2*2^10*c.k,116361464365622+c.lower,116361854195338+c.upper)) = pointBounds73200 := by
 decide +kernel
def cuts73201 : List PrefixCut := [⟨64,167795242,167795347⟩]
theorem checked73201 : checkPrefixCuts (2^48) 9598533633 10 Manual.Count131072.C073201.packed 64 cuts73201 = true := by
 decide +kernel
def cuts73202 : List PrefixCut := [⟨31,81902725,81902775⟩,
⟨64,167001217,167001317⟩]
theorem checked73202 : checkPrefixCuts (2^48) 9598664705 10 Manual.Count131072.C073202.packed 64 cuts73202 = true := by
 decide +kernel
def pointBounds73202 : List (Nat × Nat × Nat) := [(9598728192,116361881421256,116362271251232)]
theorem point_links_checked73202 : (cuts73202.take 1).map (fun c => (9598664705-1+2*2^10*c.k,116361799518531+c.lower,116362189348457+c.upper)) = pointBounds73202 := by
 decide +kernel
def cuts73203 : List PrefixCut := [⟨64,167380137,167380235⟩]
theorem checked73203 : checkPrefixCuts (2^48) 9598795777 10 Manual.Count131072.C073203.packed 64 cuts73203 = true := by
 decide +kernel
def cuts73204 : List PrefixCut := [⟨50,131368936,131369013⟩,
⟨64,168668076,168668175⟩]
theorem checked73204 : checkPrefixCuts (2^48) 9598926849 10 Manual.Count131072.C073204.packed 64 cuts73204 = true := by
 decide +kernel
def pointBounds73204 : List (Nat × Nat × Nat) := [(9599029248,116362265268821,116362655099022)]
theorem point_links_checked73204 : (cuts73204.take 1).map (fun c => (9598926849-1+2*2^10*c.k,116362133899885+c.lower,116362523730009+c.upper)) = pointBounds73204 := by
 decide +kernel
def cuts73205 : List PrefixCut := [⟨64,164707177,164707271⟩]
theorem checked73205 : checkPrefixCuts (2^48) 9599057921 10 Manual.Count131072.C073205.packed 64 cuts73205 = true := by
 decide +kernel
def cuts73206 : List PrefixCut := [⟨64,168047696,168047789⟩]
theorem checked73206 : checkPrefixCuts (2^48) 9599188993 10 Manual.Count131072.C073206.packed 64 cuts73206 = true := by
 decide +kernel
def cuts73207 : List PrefixCut := [⟨5,12813872,12813881⟩,
⟨64,165875561,165875665⟩]
theorem checked73207 : checkPrefixCuts (2^48) 9599320065 10 Manual.Count131072.C073207.packed 64 cuts73207 = true := by
 decide +kernel
def pointBounds73207 : List (Nat × Nat × Nat) := [(9599330304,116362648136706,116363037967125)]
theorem point_links_checked73207 : (cuts73207.take 1).map (fun c => (9599320065-1+2*2^10*c.k,116362635322834+c.lower,116363025153244+c.upper)) = pointBounds73207 := by
 decide +kernel
def cuts73208 : List PrefixCut := [⟨64,166049237,166049330⟩]
theorem checked73208 : checkPrefixCuts (2^48) 9599451137 10 Manual.Count131072.C073208.packed 64 cuts73208 = true := by
 decide +kernel
def cuts73209 : List PrefixCut := [⟨24,61311257,61311296⟩,
⟨64,165489845,165489950⟩]
theorem checked73209 : checkPrefixCuts (2^48) 9599582209 10 Manual.Count131072.C073209.packed 64 cuts73209 = true := by
 decide +kernel
def pointBounds73209 : List (Nat × Nat × Nat) := [(9599631360,116363028558889,116363418389535)]
theorem point_links_checked73209 : (cuts73209.take 1).map (fun c => (9599582209-1+2*2^10*c.k,116362967247632+c.lower,116363357078239+c.upper)) = pointBounds73209 := by
 decide +kernel
def cuts73210 : List PrefixCut := [⟨64,167921235,167921337⟩]
theorem checked73210 : checkPrefixCuts (2^48) 9599713281 10 Manual.Count131072.C073210.packed 64 cuts73210 = true := by
 decide +kernel
def cuts73211 : List PrefixCut := [⟨43,112004848,112004917⟩,
⟨64,165631934,165632035⟩]
theorem checked73211 : checkPrefixCuts (2^48) 9599844353 10 Manual.Count131072.C073211.packed 64 cuts73211 = true := by
 decide +kernel
def pointBounds73211 : List (Nat × Nat × Nat) := [(9599932416,116363412663560,116363802494443)]
theorem point_links_checked73211 : (cuts73211.take 1).map (fun c => (9599844353-1+2*2^10*c.k,116363300658712+c.lower,116363690489526+c.upper)) = pointBounds73211 := by
 decide +kernel
def cuts73212 : List PrefixCut := [⟨64,167007725,167007827⟩]
theorem checked73212 : checkPrefixCuts (2^48) 9599975425 10 Manual.Count131072.C073212.packed 64 cuts73212 = true := by
 decide +kernel
def cuts73213 : List PrefixCut := [⟨62,163311187,163311280⟩,
⟨64,168852588,168852684⟩]
theorem checked73213 : checkPrefixCuts (2^48) 9600106497 10 Manual.Count131072.C073213.packed 64 cuts73213 = true := by
 decide +kernel
def pointBounds73213 : List (Nat × Nat × Nat) := [(9600233472,116363796609558,116364186440668)]
theorem point_links_checked73213 : (cuts73213.take 1).map (fun c => (9600106497-1+2*2^10*c.k,116363633298371+c.lower,116364023129388+c.upper)) = pointBounds73213 := by
 decide +kernel
def cuts73214 : List PrefixCut := [⟨64,166944531,166944629⟩]
theorem checked73214 : checkPrefixCuts (2^48) 9600237569 10 Manual.Count131072.C073214.packed 64 cuts73214 = true := by
 decide +kernel
def cuts73215 : List PrefixCut := [⟨64,169023891,169023995⟩]
theorem checked73215 : checkPrefixCuts (2^48) 9600368641 10 Manual.Count131072.C073215.packed 64 cuts73215 = true := by
 decide +kernel
def cuts73216 : List PrefixCut := [⟨17,42512146,42512174⟩,
⟨64,165855165,165855263⟩]
theorem checked73216 : checkPrefixCuts (2^48) 9600499713 10 Manual.Count131072.C073216.packed 64 cuts73216 = true := by
 decide +kernel
def pointBounds73216 : List (Nat × Nat × Nat) := [(9600534528,116364180631527,116364570462870)]
theorem point_links_checked73216 : (cuts73216.take 1).map (fun c => (9600499713-1+2*2^10*c.k,116364138119381+c.lower,116364527950696+c.upper)) = pointBounds73216 := by
 decide +kernel
def cuts73217 : List PrefixCut := [⟨64,166791097,166791199⟩]
theorem checked73217 : checkPrefixCuts (2^48) 9600630785 10 Manual.Count131072.C073217.packed 64 cuts73217 = true := by
 decide +kernel
def cuts73218 : List PrefixCut := [⟨36,94813965,94814020⟩,
⟨64,167287219,167287321⟩]
theorem checked73218 : checkPrefixCuts (2^48) 9600761857 10 Manual.Count131072.C073218.packed 64 cuts73218 = true := by
 decide +kernel
def pointBounds73218 : List (Nat × Nat × Nat) := [(9600835584,116364565579608,116364955411178)]
theorem point_links_checked73218 : (cuts73218.take 1).map (fun c => (9600761857-1+2*2^10*c.k,116364470765643+c.lower,116364860597158+c.upper)) = pointBounds73218 := by
 decide +kernel
def cuts73219 : List PrefixCut := [⟨64,166464060,166464155⟩]
theorem checked73219 : checkPrefixCuts (2^48) 9600892929 10 Manual.Count131072.C073219.packed 64 cuts73219 = true := by
 decide +kernel
def cuts73220 : List PrefixCut := [⟨55,145060520,145060604⟩,
⟨64,168250111,168250208⟩]
theorem checked73220 : checkPrefixCuts (2^48) 9601024001 10 Manual.Count131072.C073220.packed 64 cuts73220 = true := by
 decide +kernel
def pointBounds73220 : List (Nat × Nat × Nat) := [(9601136640,116364949577442,116365339409238)]
theorem point_links_checked73220 : (cuts73220.take 1).map (fun c => (9601024001-1+2*2^10*c.k,116364804516922+c.lower,116365194348634+c.upper)) = pointBounds73220 := by
 decide +kernel
def cuts73221 : List PrefixCut := [⟨64,167778749,167778854⟩]
theorem checked73221 : checkPrefixCuts (2^48) 9601155073 10 Manual.Count131072.C073221.packed 64 cuts73221 = true := by
 decide +kernel
def cuts73222 : List PrefixCut := [⟨64,166369277,166369378⟩]
theorem checked73222 : checkPrefixCuts (2^48) 9601286145 10 Manual.Count131072.C073222.packed 64 cuts73222 = true := by
 decide +kernel
def cuts73223 : List PrefixCut := [⟨10,26824089,26824104⟩,
⟨64,167656915,167657015⟩]
theorem checked73223 : checkPrefixCuts (2^48) 9601417217 10 Manual.Count131072.C073223.packed 64 cuts73223 = true := by
 decide +kernel
def pointBounds73223 : List (Nat × Nat × Nat) := [(9601437696,116365333739148,116365723571178)]
theorem point_links_checked73223 : (cuts73223.take 1).map (fun c => (9601417217-1+2*2^10*c.k,116365306915059+c.lower,116365696747074+c.upper)) = pointBounds73223 := by
 decide +kernel
def cuts73224 : List PrefixCut := [⟨64,168240929,168241031⟩]
theorem checked73224 : checkPrefixCuts (2^48) 9601548289 10 Manual.Count131072.C073224.packed 64 cuts73224 = true := by
 decide +kernel
def cuts73225 : List PrefixCut := [⟨29,76483046,76483091⟩,
⟨64,169206026,169206126⟩]
theorem checked73225 : checkPrefixCuts (2^48) 9601679361 10 Manual.Count131072.C073225.packed 64 cuts73225 = true := by
 decide +kernel
def pointBounds73225 : List (Nat × Nat × Nat) := [(9601738752,116365719295949,116366109128211)]
theorem point_links_checked73225 : (cuts73225.take 1).map (fun c => (9601679361-1+2*2^10*c.k,116365642812903+c.lower,116366032645120+c.upper)) = pointBounds73225 := by
 decide +kernel
def cuts73226 : List PrefixCut := [⟨64,166565397,166565492⟩]
theorem checked73226 : checkPrefixCuts (2^48) 9601810433 10 Manual.Count131072.C073226.packed 64 cuts73226 = true := by
 decide +kernel
def cuts73227 : List PrefixCut := [⟨48,123823274,123823351⟩,
⟨64,165097417,165097519⟩]
theorem checked73227 : checkPrefixCuts (2^48) 9601941505 10 Manual.Count131072.C073227.packed 64 cuts73227 = true := by
 decide +kernel
def pointBounds73227 : List (Nat × Nat × Nat) := [(9602039808,116366102407600,116366492240089)]
theorem point_links_checked73227 : (cuts73227.take 1).map (fun c => (9601941505-1+2*2^10*c.k,116365978584326+c.lower,116366368416738+c.upper)) = pointBounds73227 := by
 decide +kernel
def cuts73228 : List PrefixCut := [⟨64,166355657,166355763⟩]
theorem checked73228 : checkPrefixCuts (2^48) 9602072577 10 Manual.Count131072.C073228.packed 64 cuts73228 = true := by
 decide +kernel
def cuts73229 : List PrefixCut := [⟨64,166998288,166998386⟩]
theorem checked73229 : checkPrefixCuts (2^48) 9602203649 10 Manual.Count131072.C073229.packed 64 cuts73229 = true := by
 decide +kernel
def cuts73230 : List PrefixCut := [⟨3,8236999,8237003⟩,
⟨64,165970048,165970146⟩]
theorem checked73230 : checkPrefixCuts (2^48) 9602334721 10 Manual.Count131072.C073230.packed 64 cuts73230 = true := by
 decide +kernel
def pointBounds73230 : List (Nat × Nat × Nat) := [(9602340864,116366485272687,116366875105409)]
theorem point_links_checked73230 : (cuts73230.take 1).map (fun c => (9602334721-1+2*2^10*c.k,116366477035688+c.lower,116366866868406+c.upper)) = pointBounds73230 := by
 decide +kernel
def cuts73231 : List PrefixCut := [⟨64,167023025,167023127⟩]
theorem checked73231 : checkPrefixCuts (2^48) 9602465793 10 Manual.Count131072.C073231.packed 64 cuts73231 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000100
