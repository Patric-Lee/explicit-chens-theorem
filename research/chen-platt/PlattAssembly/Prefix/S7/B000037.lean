import PlattAssemblyKernel
import PlattCertificates.Count131072.C061184
import PlattCertificates.Count131072.C061185
import PlattCertificates.Count131072.C061186
import PlattCertificates.Count131072.C061187
import PlattCertificates.Count131072.C061188
import PlattCertificates.Count131072.C061189
import PlattCertificates.Count131072.C061190
import PlattCertificates.Count131072.C061191
import PlattCertificates.Count131072.C061192
import PlattCertificates.Count131072.C061193
import PlattCertificates.Count131072.C061194
import PlattCertificates.Count131072.C061195
import PlattCertificates.Count131072.C061196
import PlattCertificates.Count131072.C061197
import PlattCertificates.Count131072.C061198
import PlattCertificates.Count131072.C061199
import PlattCertificates.Count131072.C061200
import PlattCertificates.Count131072.C061201
import PlattCertificates.Count131072.C061202
import PlattCertificates.Count131072.C061203
import PlattCertificates.Count131072.C061204
import PlattCertificates.Count131072.C061205
import PlattCertificates.Count131072.C061206
import PlattCertificates.Count131072.C061207
import PlattCertificates.Count131072.C061208
import PlattCertificates.Count131072.C061209
import PlattCertificates.Count131072.C061210
import PlattCertificates.Count131072.C061211
import PlattCertificates.Count131072.C061212
import PlattCertificates.Count131072.C061213
import PlattCertificates.Count131072.C061214
import PlattCertificates.Count131072.C061215
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000037
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61184 : List PrefixCut := [⟨25,79178851,79178897⟩,
⟨64,199577420,199577534⟩]
theorem checked61184 : checkPrefixCuts (2^48) 8023441409 10 Manual.Count131072.C061184.packed 64 cuts61184 = true := by
 decide +kernel
def pointBounds61184 : List (Nat × Nat × Nat) := [(8023492608,114158083178821,114158471724005)]
theorem point_links_checked61184 : (cuts61184.take 1).map (fun c => (8023441409-1+2*2^10*c.k,114158003999970+c.lower,114158392545108+c.upper)) = pointBounds61184 := by
 decide +kernel
def cuts61185 : List PrefixCut := [⟨64,203783833,203783948⟩]
theorem checked61185 : checkPrefixCuts (2^48) 8023572481 10 Manual.Count131072.C061185.packed 64 cuts61185 = true := by
 decide +kernel
def cuts61186 : List PrefixCut := [⟨20,63600644,63600677⟩,
⟨64,201886190,201886299⟩]
theorem checked61186 : checkPrefixCuts (2^48) 8023703553 10 Manual.Count131072.C061186.packed 64 cuts61186 = true := by
 decide +kernel
def pointBounds61186 : List (Nat × Nat × Nat) := [(8023744512,114158470961867,114158859507267)]
theorem point_links_checked61186 : (cuts61186.take 1).map (fun c => (8023703553-1+2*2^10*c.k,114158407361223+c.lower,114158795906590+c.upper)) = pointBounds61186 := by
 decide +kernel
def cuts61187 : List PrefixCut := [⟨64,202444127,202444238⟩]
theorem checked61187 : checkPrefixCuts (2^48) 8023834625 10 Manual.Count131072.C061187.packed 64 cuts61187 = true := by
 decide +kernel
def cuts61188 : List PrefixCut := [⟨15,45497734,45497759⟩,
⟨64,201177982,201178097⟩]
theorem checked61188 : checkPrefixCuts (2^48) 8023965697 10 Manual.Count131072.C061188.packed 64 cuts61188 = true := by
 decide +kernel
def pointBounds61188 : List (Nat × Nat × Nat) := [(8023996416,114158857189274,114159245734886)]
theorem point_links_checked61188 : (cuts61188.take 1).map (fun c => (8023965697-1+2*2^10*c.k,114158811691540+c.lower,114159200237127+c.upper)) = pointBounds61188 := by
 decide +kernel
def cuts61189 : List PrefixCut := [⟨64,202507689,202507806⟩]
theorem checked61189 : checkPrefixCuts (2^48) 8024096769 10 Manual.Count131072.C061189.packed 64 cuts61189 = true := by
 decide +kernel
def cuts61190 : List PrefixCut := [⟨10,33254025,33254043⟩,
⟨64,203942574,203942694⟩]
theorem checked61190 : checkPrefixCuts (2^48) 8024227841 10 Manual.Count131072.C061190.packed 64 cuts61190 = true := by
 decide +kernel
def pointBounds61190 : List (Nat × Nat × Nat) := [(8024248320,114159248631236,114159637177073)]
theorem point_links_checked61190 : (cuts61190.take 1).map (fun c => (8024227841-1+2*2^10*c.k,114159215377211+c.lower,114159603923030+c.upper)) = pointBounds61190 := by
 decide +kernel
def cuts61191 : List PrefixCut := [⟨64,201518916,201519034⟩]
theorem checked61191 : checkPrefixCuts (2^48) 8024358913 10 Manual.Count131072.C061191.packed 64 cuts61191 = true := by
 decide +kernel
def cuts61192 : List PrefixCut := [⟨5,15784632,15784641⟩,
⟨64,203550069,203550182⟩]
theorem checked61192 : checkPrefixCuts (2^48) 8024489985 10 Manual.Count131072.C061192.packed 64 cuts61192 = true := by
 decide +kernel
def pointBounds61192 : List (Nat × Nat × Nat) := [(8024500224,114159636623333,114160025169399)]
theorem point_links_checked61192 : (cuts61192.take 1).map (fun c => (8024489985-1+2*2^10*c.k,114159620838701+c.lower,114160009384758+c.upper)) = pointBounds61192 := by
 decide +kernel
def cuts61193 : List PrefixCut := [⟨64,198215188,198215298⟩]
theorem checked61193 : checkPrefixCuts (2^48) 8024621057 10 Manual.Count131072.C061193.packed 64 cuts61193 = true := by
 decide +kernel
def pointBounds61193 : List (Nat × Nat × Nat) := [(8024752128,114160022603958,114160411150238)]
theorem point_links_checked61193 : (cuts61193.take 1).map (fun c => (8024621057-1+2*2^10*c.k,114159824388770+c.lower,114160212934940+c.upper)) = pointBounds61193 := by
 decide +kernel
def cuts61194 : List PrefixCut := [⟨64,197510413,197510531⟩]
theorem checked61194 : checkPrefixCuts (2^48) 8024752129 10 Manual.Count131072.C061194.packed 64 cuts61194 = true := by
 decide +kernel
def cuts61195 : List PrefixCut := [⟨59,188352759,188352864⟩,
⟨64,203961007,203961121⟩]
theorem checked61195 : checkPrefixCuts (2^48) 8024883201 10 Manual.Count131072.C061195.packed 64 cuts61195 = true := by
 decide +kernel
def pointBounds61195 : List (Nat × Nat × Nat) := [(8025004032,114160408467130,114160797013633)]
theorem point_links_checked61195 : (cuts61195.take 1).map (fun c => (8024883201-1+2*2^10*c.k,114160220114371+c.lower,114160608660769+c.upper)) = pointBounds61195 := by
 decide +kernel
def cuts61196 : List PrefixCut := [⟨64,201642762,201642882⟩]
theorem checked61196 : checkPrefixCuts (2^48) 8025014273 10 Manual.Count131072.C061196.packed 64 cuts61196 = true := by
 decide +kernel
def cuts61197 : List PrefixCut := [⟨54,169161307,169161404⟩,
⟨64,200937980,200938093⟩]
theorem checked61197 : checkPrefixCuts (2^48) 8025145345 10 Manual.Count131072.C061197.packed 64 cuts61197 = true := by
 decide +kernel
def pointBounds61197 : List (Nat × Nat × Nat) := [(8025255936,114160794879447,114161183426176)]
theorem point_links_checked61197 : (cuts61197.take 1).map (fun c => (8025145345-1+2*2^10*c.k,114160625718140+c.lower,114161014264772+c.upper)) = pointBounds61197 := by
 decide +kernel
def cuts61198 : List PrefixCut := [⟨64,202162261,202162373⟩]
theorem checked61198 : checkPrefixCuts (2^48) 8025276417 10 Manual.Count131072.C061198.packed 64 cuts61198 = true := by
 decide +kernel
def cuts61199 : List PrefixCut := [⟨49,152426192,152426280⟩,
⟨64,199212867,199212980⟩]
theorem checked61199 : checkPrefixCuts (2^48) 8025407489 10 Manual.Count131072.C061199.packed 64 cuts61199 = true := by
 decide +kernel
def pointBounds61199 : List (Nat × Nat × Nat) := [(8025507840,114161181244573,114161569791518)]
theorem point_links_checked61199 : (cuts61199.take 1).map (fun c => (8025407489-1+2*2^10*c.k,114161028818381+c.lower,114161417365238+c.upper)) = pointBounds61199 := by
 decide +kernel
def cuts61200 : List PrefixCut := [⟨64,201840006,201840124⟩]
theorem checked61200 : checkPrefixCuts (2^48) 8025538561 10 Manual.Count131072.C061200.packed 64 cuts61200 = true := by
 decide +kernel
def cuts61201 : List PrefixCut := [⟨44,137866573,137866652⟩,
⟨64,201100208,201100323⟩]
theorem checked61201 : checkPrefixCuts (2^48) 8025669633 10 Manual.Count131072.C061201.packed 64 cuts61201 = true := by
 decide +kernel
def pointBounds61201 : List (Nat × Nat × Nat) := [(8025759744,114161567737827,114161956284994)]
theorem point_links_checked61201 : (cuts61201.take 1).map (fun c => (8025669633-1+2*2^10*c.k,114161429871254+c.lower,114161818418342+c.upper)) = pointBounds61201 := by
 decide +kernel
def cuts61202 : List PrefixCut := [⟨64,204253328,204253444⟩]
theorem checked61202 : checkPrefixCuts (2^48) 8025800705 10 Manual.Count131072.C061202.packed 64 cuts61202 = true := by
 decide +kernel
def cuts61203 : List PrefixCut := [⟨39,120993247,120993311⟩,
⟨64,200848136,200848244⟩]
theorem checked61203 : checkPrefixCuts (2^48) 8025931777 10 Manual.Count131072.C061203.packed 64 cuts61203 = true := by
 decide +kernel
def pointBounds61203 : List (Nat × Nat × Nat) := [(8026011648,114161956218037,114162344765420)]
theorem point_links_checked61203 : (cuts61203.take 1).map (fun c => (8025931777-1+2*2^10*c.k,114161835224790+c.lower,114162223772109+c.upper)) = pointBounds61203 := by
 decide +kernel
def cuts61204 : List PrefixCut := [⟨64,201826826,201826935⟩]
theorem checked61204 : checkPrefixCuts (2^48) 8026062849 10 Manual.Count131072.C061204.packed 64 cuts61204 = true := by
 decide +kernel
def cuts61205 : List PrefixCut := [⟨34,107592872,107592932⟩,
⟨64,201367639,201367754⟩]
theorem checked61205 : checkPrefixCuts (2^48) 8026193921 10 Manual.Count131072.C061205.packed 64 cuts61205 = true := by
 decide +kernel
def pointBounds61205 : List (Nat × Nat × Nat) := [(8026263552,114162345492624,114162734040220)]
theorem point_links_checked61205 : (cuts61205.take 1).map (fun c => (8026193921-1+2*2^10*c.k,114162237899752+c.lower,114162626447288+c.upper)) = pointBounds61205 := by
 decide +kernel
def cuts61206 : List PrefixCut := [⟨64,203012576,203012691⟩]
theorem checked61206 : checkPrefixCuts (2^48) 8026324993 10 Manual.Count131072.C061206.packed 64 cuts61206 = true := by
 decide +kernel
def cuts61207 : List PrefixCut := [⟨29,91142408,91142459⟩,
⟨64,201501322,201501437⟩]
theorem checked61207 : checkPrefixCuts (2^48) 8026456065 10 Manual.Count131072.C061207.packed 64 cuts61207 = true := by
 decide +kernel
def pointBounds61207 : List (Nat × Nat × Nat) := [(8026515456,114162733422375,114163121970192)]
theorem point_links_checked61207 : (cuts61207.take 1).map (fun c => (8026456065-1+2*2^10*c.k,114162642279967+c.lower,114163030827733+c.upper)) = pointBounds61207 := by
 decide +kernel
def cuts61208 : List PrefixCut := [⟨64,202585131,202585245⟩]
theorem checked61208 : checkPrefixCuts (2^48) 8026587137 10 Manual.Count131072.C061208.packed 64 cuts61208 = true := by
 decide +kernel
def cuts61209 : List PrefixCut := [⟨24,74903407,74903450⟩,
⟨64,201038873,201038989⟩]
theorem checked61209 : checkPrefixCuts (2^48) 8026718209 10 Manual.Count131072.C061209.packed 64 cuts61209 = true := by
 decide +kernel
def pointBounds61209 : List (Nat × Nat × Nat) := [(8026767360,114163121269827,114163509817865)]
theorem point_links_checked61209 : (cuts61209.take 1).map (fun c => (8026718209-1+2*2^10*c.k,114163046366420+c.lower,114163434914415+c.upper)) = pointBounds61209 := by
 decide +kernel
def cuts61210 : List PrefixCut := [⟨64,202753839,202753959⟩]
theorem checked61210 : checkPrefixCuts (2^48) 8026849281 10 Manual.Count131072.C061210.packed 64 cuts61210 = true := by
 decide +kernel
def cuts61211 : List PrefixCut := [⟨19,57823860,57823895⟩,
⟨64,200962167,200962281⟩]
theorem checked61211 : checkPrefixCuts (2^48) 8026980353 10 Manual.Count131072.C061211.packed 64 cuts61211 = true := by
 decide +kernel
def pointBounds61211 : List (Nat × Nat × Nat) := [(8027019264,114163507982992,114163896531258)]
theorem point_links_checked61211 : (cuts61211.take 1).map (fun c => (8026980353-1+2*2^10*c.k,114163450159132+c.lower,114163838707363+c.upper)) = pointBounds61211 := by
 decide +kernel
def cuts61212 : List PrefixCut := [⟨64,200257594,200257709⟩]
theorem checked61212 : checkPrefixCuts (2^48) 8027111425 10 Manual.Count131072.C061212.packed 64 cuts61212 = true := by
 decide +kernel
def cuts61213 : List PrefixCut := [⟨14,45444101,45444125⟩,
⟨64,201621869,201621978⟩]
theorem checked61213 : checkPrefixCuts (2^48) 8027242497 10 Manual.Count131072.C061213.packed 64 cuts61213 = true := by
 decide +kernel
def pointBounds61213 : List (Nat × Nat × Nat) := [(8027271168,114163896822994,114164285371478)]
theorem point_links_checked61213 : (cuts61213.take 1).map (fun c => (8027242497-1+2*2^10*c.k,114163851378893+c.lower,114164239927353+c.upper)) = pointBounds61213 := by
 decide +kernel
def cuts61214 : List PrefixCut := [⟨64,200882215,200882329⟩]
theorem checked61214 : checkPrefixCuts (2^48) 8027373569 10 Manual.Count131072.C061214.packed 64 cuts61214 = true := by
 decide +kernel
def cuts61215 : List PrefixCut := [⟨9,28051015,28051031⟩,
⟨64,203158045,203158160⟩]
theorem checked61215 : checkPrefixCuts (2^48) 8027504641 10 Manual.Count131072.C061215.packed 64 cuts61215 = true := by
 decide +kernel
def pointBounds61215 : List (Nat × Nat × Nat) := [(8027523072,114164281933992,114164670482691)]
theorem point_links_checked61215 : (cuts61215.take 1).map (fun c => (8027504641-1+2*2^10*c.k,114164253882977+c.lower,114164642431660+c.upper)) = pointBounds61215 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000037
