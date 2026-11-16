import PlattAssemblyKernel
import PlattCertificates.Count131072.C050192
import PlattCertificates.Count131072.C050193
import PlattCertificates.Count131072.C050194
import PlattCertificates.Count131072.C050195
import PlattCertificates.Count131072.C050196
import PlattCertificates.Count131072.C050197
import PlattCertificates.Count131072.C050198
import PlattCertificates.Count131072.C050199
import PlattCertificates.Count131072.C050200
import PlattCertificates.Count131072.C050201
import PlattCertificates.Count131072.C050202
import PlattCertificates.Count131072.C050203
import PlattCertificates.Count131072.C050204
import PlattCertificates.Count131072.C050205
import PlattCertificates.Count131072.C050206
import PlattCertificates.Count131072.C050207
import PlattCertificates.Count131072.C050208
import PlattCertificates.Count131072.C050209
import PlattCertificates.Count131072.C050210
import PlattCertificates.Count131072.C050211
import PlattCertificates.Count131072.C050212
import PlattCertificates.Count131072.C050213
import PlattCertificates.Count131072.C050214
import PlattCertificates.Count131072.C050215
import PlattCertificates.Count131072.C050216
import PlattCertificates.Count131072.C050217
import PlattCertificates.Count131072.C050218
import PlattCertificates.Count131072.C050219
import PlattCertificates.Count131072.C050220
import PlattCertificates.Count131072.C050221
import PlattCertificates.Count131072.C050222
import PlattCertificates.Count131072.C050223
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50192 : List PrefixCut := [⟨46,176425712,176425813⟩,
⟨64,248431994,248432135⟩]
theorem checked50192 : checkPrefixCuts (2^48) 6582697985 10 Manual.Count131072.C050192.packed 64 cuts50192 = true := by
 decide +kernel
def pointBounds50192 : List (Nat × Nat × Nat) := [(6582792192,111704724564783,111705111714094)]
theorem point_links_checked50192 : (cuts50192.take 1).map (fun c => (6582697985-1+2*2^10*c.k,111704548139071+c.lower,111704935288281+c.upper)) = pointBounds50192 := by
 decide +kernel
def cuts50193 : List PrefixCut := [⟨64,248213277,248213416⟩]
theorem checked50193 : checkPrefixCuts (2^48) 6582829057 10 Manual.Count131072.C050193.packed 64 cuts50193 = true := by
 decide +kernel
def cuts50194 : List PrefixCut := [⟨19,71448583,71448626⟩,
⟨64,245600093,245600238⟩]
theorem checked50194 : checkPrefixCuts (2^48) 6582960129 10 Manual.Count131072.C050194.packed 64 cuts50194 = true := by
 decide +kernel
def pointBounds50194 : List (Nat × Nat × Nat) := [(6582999040,111705116232925,111705503382458)]
theorem point_links_checked50194 : (cuts50194.take 1).map (fun c => (6582960129-1+2*2^10*c.k,111705044784342+c.lower,111705431933832+c.upper)) = pointBounds50194 := by
 decide +kernel
def cuts50195 : List PrefixCut := [⟨56,218786981,218787107⟩,
⟨64,248844768,248844911⟩]
theorem checked50195 : checkPrefixCuts (2^48) 6583091201 10 Manual.Count131072.C050195.packed 64 cuts50195 = true := by
 decide +kernel
def pointBounds50195 : List (Nat × Nat × Nat) := [(6583205888,111705509171416,111705896321177)]
theorem point_links_checked50195 : (cuts50195.take 1).map (fun c => (6583091201-1+2*2^10*c.k,111705290384435+c.lower,111705677534070+c.upper)) = pointBounds50195 := by
 decide +kernel
def cuts50196 : List PrefixCut := [⟨64,247300577,247300712⟩]
theorem checked50196 : checkPrefixCuts (2^48) 6583222273 10 Manual.Count131072.C050196.packed 64 cuts50196 = true := by
 decide +kernel
def cuts50197 : List PrefixCut := [⟨29,114199556,114199623⟩,
⟨64,249732670,249732820⟩]
theorem checked50197 : checkPrefixCuts (2^48) 6583353345 10 Manual.Count131072.C050197.packed 64 cuts50197 = true := by
 decide +kernel
def pointBounds50197 : List (Nat × Nat × Nat) := [(6583412736,111705900729336,111706287879316)]
theorem point_links_checked50197 : (cuts50197.take 1).map (fun c => (6583353345-1+2*2^10*c.k,111705786529780+c.lower,111706173679693+c.upper)) = pointBounds50197 := by
 decide +kernel
def cuts50198 : List PrefixCut := [⟨64,248958138,248958276⟩]
theorem checked50198 : checkPrefixCuts (2^48) 6583484417 10 Manual.Count131072.C050198.packed 64 cuts50198 = true := by
 decide +kernel
def cuts50199 : List PrefixCut := [⟨2,7952213,7952217⟩,
⟨64,245789417,245789555⟩]
theorem checked50199 : checkPrefixCuts (2^48) 6583615489 10 Manual.Count131072.C050199.packed 64 cuts50199 = true := by
 decide +kernel
def pointBounds50199 : List (Nat × Nat × Nat) := [(6583619584,111706293172801,111706680323006)]
theorem point_links_checked50199 : (cuts50199.take 1).map (fun c => (6583615489-1+2*2^10*c.k,111706285220588+c.lower,111706672370789+c.upper)) = pointBounds50199 := by
 decide +kernel
def cuts50200 : List PrefixCut := [⟨39,152456276,152456361⟩,
⟨64,248648976,248649117⟩]
theorem checked50200 : checkPrefixCuts (2^48) 6583746561 10 Manual.Count131072.C050200.packed 64 cuts50200 = true := by
 decide +kernel
def pointBounds50200 : List (Nat × Nat × Nat) := [(6583826432,111706683466281,111707070616705)]
theorem point_links_checked50200 : (cuts50200.take 1).map (fun c => (6583746561-1+2*2^10*c.k,111706531010005+c.lower,111706918160344+c.upper)) = pointBounds50200 := by
 decide +kernel
def cuts50201 : List PrefixCut := [⟨64,251636628,251636770⟩]
theorem checked50201 : checkPrefixCuts (2^48) 6583877633 10 Manual.Count131072.C050201.packed 64 cuts50201 = true := by
 decide +kernel
def cuts50202 : List PrefixCut := [⟨12,43648987,43649014⟩,
⟨64,246415987,246416129⟩]
theorem checked50202 : checkPrefixCuts (2^48) 6584008705 10 Manual.Count131072.C050202.packed 64 cuts50202 = true := by
 decide +kernel
def pointBounds50202 : List (Nat × Nat × Nat) := [(6584033280,111707074944596,111707462095245)]
theorem point_links_checked50202 : (cuts50202.take 1).map (fun c => (6584008705-1+2*2^10*c.k,111707031295609+c.lower,111707418446231+c.upper)) = pointBounds50202 := by
 decide +kernel
def cuts50203 : List PrefixCut := [⟨49,188057785,188057888⟩,
⟨64,246753114,246753251⟩]
theorem checked50203 : checkPrefixCuts (2^48) 6584139777 10 Manual.Count131072.C050203.packed 64 cuts50203 = true := by
 decide +kernel
def pointBounds50203 : List (Nat × Nat × Nat) := [(6584240128,111707465769381,111707852920248)]
theorem point_links_checked50203 : (cuts50203.take 1).map (fun c => (6584139777-1+2*2^10*c.k,111707277711596+c.lower,111707664862360+c.upper)) = pointBounds50203 := by
 decide +kernel
def cuts50204 : List PrefixCut := [⟨64,248543641,248543783⟩]
theorem checked50204 : checkPrefixCuts (2^48) 6584270849 10 Manual.Count131072.C050204.packed 64 cuts50204 = true := by
 decide +kernel
def cuts50205 : List PrefixCut := [⟨22,86608655,86608700⟩,
⟨64,248709707,248709842⟩]
theorem checked50205 : checkPrefixCuts (2^48) 6584401921 10 Manual.Count131072.C050205.packed 64 cuts50205 = true := by
 decide +kernel
def pointBounds50205 : List (Nat × Nat × Nat) := [(6584446976,111707859617006,111708246768094)]
theorem point_links_checked50205 : (cuts50205.take 1).map (fun c => (6584401921-1+2*2^10*c.k,111707773008351+c.lower,111708160159394+c.upper)) = pointBounds50205 := by
 decide +kernel
def cuts50206 : List PrefixCut := [⟨59,230366273,230366407⟩,
⟨64,249687949,249688095⟩]
theorem checked50206 : checkPrefixCuts (2^48) 6584532993 10 Manual.Count131072.C050206.packed 64 cuts50206 = true := by
 decide +kernel
def pointBounds50206 : List (Nat × Nat × Nat) := [(6584653824,111708252084331,111708639235643)]
theorem point_links_checked50206 : (cuts50206.take 1).map (fun c => (6584532993-1+2*2^10*c.k,111708021718058+c.lower,111708408869236+c.upper)) = pointBounds50206 := by
 decide +kernel
def cuts50207 : List PrefixCut := [⟨64,246776189,246776331⟩]
theorem checked50207 : checkPrefixCuts (2^48) 6584664065 10 Manual.Count131072.C050207.packed 64 cuts50207 = true := by
 decide +kernel
def cuts50208 : List PrefixCut := [⟨32,124433530,124433603⟩,
⟨64,248096411,248096555⟩]
theorem checked50208 : checkPrefixCuts (2^48) 6584795137 10 Manual.Count131072.C050208.packed 64 cuts50208 = true := by
 decide +kernel
def pointBounds50208 : List (Nat × Nat × Nat) := [(6584860672,111708642615726,111709029767265)]
theorem point_links_checked50208 : (cuts50208.take 1).map (fun c => (6584795137-1+2*2^10*c.k,111708518182196+c.lower,111708905333662+c.upper)) = pointBounds50208 := by
 decide +kernel
def cuts50209 : List PrefixCut := [⟨64,244415410,244415548⟩]
theorem checked50209 : checkPrefixCuts (2^48) 6584926209 10 Manual.Count131072.C050209.packed 64 cuts50209 = true := by
 decide +kernel
def cuts50210 : List PrefixCut := [⟨5,18935794,18935804⟩,
⟨64,249026897,249027037⟩]
theorem checked50210 : checkPrefixCuts (2^48) 6585057281 10 Manual.Count131072.C050210.packed 64 cuts50210 = true := by
 decide +kernel
def pointBounds50210 : List (Nat × Nat × Nat) := [(6585067520,111709029629811,111709416781569)]
theorem point_links_checked50210 : (cuts50210.take 1).map (fun c => (6585057281-1+2*2^10*c.k,111709010694017+c.lower,111709397845765+c.upper)) = pointBounds50210 := by
 decide +kernel
def cuts50211 : List PrefixCut := [⟨42,162253783,162253878⟩,
⟨64,245944448,245944591⟩]
theorem checked50211 : checkPrefixCuts (2^48) 6585188353 10 Manual.Count131072.C050211.packed 64 cuts50211 = true := by
 decide +kernel
def pointBounds50211 : List (Nat × Nat × Nat) := [(6585274368,111709421974697,111709809126680)]
theorem point_links_checked50211 : (cuts50211.take 1).map (fun c => (6585188353-1+2*2^10*c.k,111709259720914+c.lower,111709646872802+c.upper)) = pointBounds50211 := by
 decide +kernel
def cuts50212 : List PrefixCut := [⟨64,250812188,250812331⟩]
theorem checked50212 : checkPrefixCuts (2^48) 6585319425 10 Manual.Count131072.C050212.packed 64 cuts50212 = true := by
 decide +kernel
def cuts50213 : List PrefixCut := [⟨15,57573251,57573286⟩,
⟨64,245934635,245934777⟩]
theorem checked50213 : checkPrefixCuts (2^48) 6585450497 10 Manual.Count131072.C050213.packed 64 cuts50213 = true := by
 decide +kernel
def pointBounds50213 : List (Nat × Nat × Nat) := [(6585481216,111709814050801,111710201203010)]
theorem point_links_checked50213 : (cuts50213.take 1).map (fun c => (6585450497-1+2*2^10*c.k,111709756477550+c.lower,111710143629724+c.upper)) = pointBounds50213 := by
 decide +kernel
def cuts50214 : List PrefixCut := [⟨52,200625031,200625145⟩,
⟨64,247126493,247126632⟩]
theorem checked50214 : checkPrefixCuts (2^48) 6585581569 10 Manual.Count131072.C050214.packed 64 cuts50214 = true := by
 decide +kernel
def pointBounds50214 : List (Nat × Nat × Nat) := [(6585688064,111710203037216,111710590189646)]
theorem point_links_checked50214 : (cuts50214.take 1).map (fun c => (6585581569-1+2*2^10*c.k,111710002412185+c.lower,111710389564501+c.upper)) = pointBounds50214 := by
 decide +kernel
def cuts50215 : List PrefixCut := [⟨64,249942405,249942546⟩]
theorem checked50215 : checkPrefixCuts (2^48) 6585712641 10 Manual.Count131072.C050215.packed 64 cuts50215 = true := by
 decide +kernel
def cuts50216 : List PrefixCut := [⟨25,95009284,95009335⟩,
⟨64,243996703,243996842⟩]
theorem checked50216 : checkPrefixCuts (2^48) 6585843713 10 Manual.Count131072.C050216.packed 64 cuts50216 = true := by
 decide +kernel
def pointBounds50216 : List (Nat × Nat × Nat) := [(6585894912,111710594490367,111710981643014)]
theorem point_links_checked50216 : (cuts50216.take 1).map (fun c => (6585843713-1+2*2^10*c.k,111710499481083+c.lower,111710886633679+c.upper)) = pointBounds50216 := by
 decide +kernel
def cuts50217 : List PrefixCut := [⟨62,242325147,242325283⟩,
⟨64,249590555,249590696⟩]
theorem checked50217 : checkPrefixCuts (2^48) 6585974785 10 Manual.Count131072.C050217.packed 64 cuts50217 = true := by
 decide +kernel
def pointBounds50217 : List (Nat × Nat × Nat) := [(6586101760,111710985802933,111711372955804)]
theorem point_links_checked50217 : (cuts50217.take 1).map (fun c => (6585974785-1+2*2^10*c.k,111710743477786+c.lower,111711130630521+c.upper)) = pointBounds50217 := by
 decide +kernel
def cuts50218 : List PrefixCut := [⟨64,247534205,247534342⟩]
theorem checked50218 : checkPrefixCuts (2^48) 6586105857 10 Manual.Count131072.C050218.packed 64 cuts50218 = true := by
 decide +kernel
def cuts50219 : List PrefixCut := [⟨35,133808290,133808366⟩,
⟨64,244836874,244837014⟩]
theorem checked50219 : checkPrefixCuts (2^48) 6586236929 10 Manual.Count131072.C050219.packed 64 cuts50219 = true := by
 decide +kernel
def pointBounds50219 : List (Nat × Nat × Nat) := [(6586308608,111711374410836,111711761563925)]
theorem point_links_checked50219 : (cuts50219.take 1).map (fun c => (6586236929-1+2*2^10*c.k,111711240602546+c.lower,111711627755559+c.upper)) = pointBounds50219 := by
 decide +kernel
def cuts50220 : List PrefixCut := [⟨64,246883338,246883481⟩]
theorem checked50220 : checkPrefixCuts (2^48) 6586368001 10 Manual.Count131072.C050220.packed 64 cuts50220 = true := by
 decide +kernel
def cuts50221 : List PrefixCut := [⟨8,30769257,30769273⟩,
⟨64,250724518,250724655⟩]
theorem checked50221 : checkPrefixCuts (2^48) 6586499073 10 Manual.Count131072.C050221.packed 64 cuts50221 = true := by
 decide +kernel
def pointBounds50221 : List (Nat × Nat × Nat) := [(6586515456,111711763092015,111712150245327)]
theorem point_links_checked50221 : (cuts50221.take 1).map (fun c => (6586499073-1+2*2^10*c.k,111711732322758+c.lower,111712119476054+c.upper)) = pointBounds50221 := by
 decide +kernel
def cuts50222 : List PrefixCut := [⟨45,173329017,173329113⟩,
⟨64,246873466,246873602⟩]
theorem checked50222 : checkPrefixCuts (2^48) 6586630145 10 Manual.Count131072.C050222.packed 64 cuts50222 = true := by
 decide +kernel
def pointBounds50222 : List (Nat × Nat × Nat) := [(6586722304,111712156376293,111712543529822)]
theorem point_links_checked50222 : (cuts50222.take 1).map (fun c => (6586630145-1+2*2^10*c.k,111711983047276+c.lower,111712370200709+c.upper)) = pointBounds50222 := by
 decide +kernel
def cuts50223 : List PrefixCut := [⟨64,248065087,248065229⟩]
theorem checked50223 : checkPrefixCuts (2^48) 6586761217 10 Manual.Count131072.C050223.packed 64 cuts50223 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000006
