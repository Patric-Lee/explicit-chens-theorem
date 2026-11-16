import PlattAssemblyKernel
import PlattCertificates.Count131072.C056176
import PlattCertificates.Count131072.C056177
import PlattCertificates.Count131072.C056178
import PlattCertificates.Count131072.C056179
import PlattCertificates.Count131072.C056180
import PlattCertificates.Count131072.C056181
import PlattCertificates.Count131072.C056182
import PlattCertificates.Count131072.C056183
import PlattCertificates.Count131072.C056184
import PlattCertificates.Count131072.C056185
import PlattCertificates.Count131072.C056186
import PlattCertificates.Count131072.C056187
import PlattCertificates.Count131072.C056188
import PlattCertificates.Count131072.C056189
import PlattCertificates.Count131072.C056190
import PlattCertificates.Count131072.C056191
import PlattCertificates.Count131072.C056192
import PlattCertificates.Count131072.C056193
import PlattCertificates.Count131072.C056194
import PlattCertificates.Count131072.C056195
import PlattCertificates.Count131072.C056196
import PlattCertificates.Count131072.C056197
import PlattCertificates.Count131072.C056198
import PlattCertificates.Count131072.C056199
import PlattCertificates.Count131072.C056200
import PlattCertificates.Count131072.C056201
import PlattCertificates.Count131072.C056202
import PlattCertificates.Count131072.C056203
import PlattCertificates.Count131072.C056204
import PlattCertificates.Count131072.C056205
import PlattCertificates.Count131072.C056206
import PlattCertificates.Count131072.C056207
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000193
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts56176 : List PrefixCut := [⟨64,219575754,219575880⟩]
theorem checked56176 : checkPrefixCuts (2^48) 7367032833 10 Manual.Count131072.C056176.packed 64 cuts56176 = true := by
 decide +kernel
def cuts56177 : List PrefixCut := [⟨46,160276026,160276116⟩,
⟨64,222360940,222361064⟩]
theorem checked56177 : checkPrefixCuts (2^48) 7367163905 10 Manual.Count131072.C056177.packed 64 cuts56177 = true := by
 decide +kernel
def pointBounds56177 : List (Nat × Nat × Nat) := [(7367258112,113102954186086,113103342129734)]
theorem point_links_checked56177 : (cuts56177.take 1).map (fun c => (7367163905-1+2*2^10*c.k,113102793910060+c.lower,113103181853618+c.upper)) = pointBounds56177 := by
 decide +kernel
def cuts56178 : List PrefixCut := [⟨64,222471575,222471701⟩]
theorem checked56178 : checkPrefixCuts (2^48) 7367294977 10 Manual.Count131072.C056178.packed 64 cuts56178 = true := by
 decide +kernel
def cuts56179 : List PrefixCut := [⟨31,105790082,105790145⟩,
⟨64,219220190,219220320⟩]
theorem checked56179 : checkPrefixCuts (2^48) 7367426049 10 Manual.Count131072.C056179.packed 64 cuts56179 = true := by
 decide +kernel
def pointBounds56179 : List (Nat × Nat × Nat) := [(7367489536,113103344532657,113103732476528)]
theorem point_links_checked56179 : (cuts56179.take 1).map (fun c => (7367426049-1+2*2^10*c.k,113103238742575+c.lower,113103626686383+c.upper)) = pointBounds56179 := by
 decide +kernel
def cuts56180 : List PrefixCut := [⟨64,221317525,221317651⟩]
theorem checked56180 : checkPrefixCuts (2^48) 7367557121 10 Manual.Count131072.C056180.packed 64 cuts56180 = true := by
 decide +kernel
def cuts56181 : List PrefixCut := [⟨16,54287713,54287745⟩,
⟨64,221772031,221772159⟩]
theorem checked56181 : checkPrefixCuts (2^48) 7367688193 10 Manual.Count131072.C056181.packed 64 cuts56181 = true := by
 decide +kernel
def pointBounds56181 : List (Nat × Nat × Nat) := [(7367720960,113103733568003,113104121512099)]
theorem point_links_checked56181 : (cuts56181.take 1).map (fun c => (7367688193-1+2*2^10*c.k,113103679280290+c.lower,113104067224354+c.upper)) = pointBounds56181 := by
 decide +kernel
def cuts56182 : List PrefixCut := [⟨64,217756790,217756914⟩]
theorem checked56182 : checkPrefixCuts (2^48) 7367819265 10 Manual.Count131072.C056182.packed 64 cuts56182 = true := by
 decide +kernel
def cuts56183 : List PrefixCut := [⟨1,3285424,3285425⟩,
⟨64,223636065,223636192⟩]
theorem checked56183 : checkPrefixCuts (2^48) 7367950337 10 Manual.Count131072.C056183.packed 64 cuts56183 = true := by
 decide +kernel
def pointBounds56183 : List (Nat × Nat × Nat) := [(7367952384,113104122094535,113104510038852)]
theorem point_links_checked56183 : (cuts56183.take 1).map (fun c => (7367950337-1+2*2^10*c.k,113104118809111+c.lower,113104506753427+c.upper)) = pointBounds56183 := by
 decide +kernel
def cuts56184 : List PrefixCut := [⟨50,172404083,172404183⟩,
⟨64,219697317,219697446⟩]
theorem checked56184 : checkPrefixCuts (2^48) 7368081409 10 Manual.Count131072.C056184.packed 64 cuts56184 = true := by
 decide +kernel
def pointBounds56184 : List (Nat × Nat × Nat) := [(7368183808,113104514849259,113104902793802)]
theorem point_links_checked56184 : (cuts56184.take 1).map (fun c => (7368081409-1+2*2^10*c.k,113104342445176+c.lower,113104730389619+c.upper)) = pointBounds56184 := by
 decide +kernel
def cuts56185 : List PrefixCut := [⟨64,223131509,223131636⟩]
theorem checked56185 : checkPrefixCuts (2^48) 7368212481 10 Manual.Count131072.C056185.packed 64 cuts56185 = true := by
 decide +kernel
def cuts56186 : List PrefixCut := [⟨35,121744613,121744682⟩,
⟨64,221523123,221523249⟩]
theorem checked56186 : checkPrefixCuts (2^48) 7368343553 10 Manual.Count131072.C056186.packed 64 cuts56186 = true := by
 decide +kernel
def pointBounds56186 : List (Nat × Nat × Nat) := [(7368415232,113104907018615,113105294963383)]
theorem point_links_checked56186 : (cuts56186.take 1).map (fun c => (7368343553-1+2*2^10*c.k,113104785274002+c.lower,113105173218701+c.upper)) = pointBounds56186 := by
 decide +kernel
def cuts56187 : List PrefixCut := [⟨64,222283159,222283286⟩]
theorem checked56187 : checkPrefixCuts (2^48) 7368474625 10 Manual.Count131072.C056187.packed 64 cuts56187 = true := by
 decide +kernel
def cuts56188 : List PrefixCut := [⟨20,68872976,68873016⟩,
⟨64,221209643,221209769⟩]
theorem checked56188 : checkPrefixCuts (2^48) 7368605697 10 Manual.Count131072.C056188.packed 64 cuts56188 = true := by
 decide +kernel
def pointBounds56188 : List (Nat × Nat × Nat) := [(7368646656,113105297953260,113105685898252)]
theorem point_links_checked56188 : (cuts56188.take 1).map (fun c => (7368605697-1+2*2^10*c.k,113105229080284+c.lower,113105617025236+c.upper)) = pointBounds56188 := by
 decide +kernel
def cuts56189 : List PrefixCut := [⟨64,217767867,217767994⟩]
theorem checked56189 : checkPrefixCuts (2^48) 7368736769 10 Manual.Count131072.C056189.packed 64 cuts56189 = true := by
 decide +kernel
def cuts56190 : List PrefixCut := [⟨5,17838383,17838392⟩,
⟨64,219444687,219444813⟩]
theorem checked56190 : checkPrefixCuts (2^48) 7368867841 10 Manual.Count131072.C056190.packed 64 cuts56190 = true := by
 decide +kernel
def pointBounds56190 : List (Nat × Nat × Nat) := [(7368878080,113105685896177,113106073841391)]
theorem point_links_checked56190 : (cuts56190.take 1).map (fun c => (7368867841-1+2*2^10*c.k,113105668057794+c.lower,113106056002999+c.upper)) = pointBounds56190 := by
 decide +kernel
def cuts56191 : List PrefixCut := [⟨54,183039467,183039571⟩,
⟨64,216155871,216155993⟩]
theorem checked56191 : checkPrefixCuts (2^48) 7368998913 10 Manual.Count131072.C056191.packed 64 cuts56191 = true := by
 decide +kernel
def pointBounds56191 : List (Nat × Nat × Nat) := [(7369109504,113106070541948,113106458487383)]
theorem point_links_checked56191 : (cuts56191.take 1).map (fun c => (7368998913-1+2*2^10*c.k,113105887502481+c.lower,113106275447812+c.upper)) = pointBounds56191 := by
 decide +kernel
def cuts56192 : List PrefixCut := [⟨64,222645356,222645478⟩]
theorem checked56192 : checkPrefixCuts (2^48) 7369129985 10 Manual.Count131072.C056192.packed 64 cuts56192 = true := by
 decide +kernel
def cuts56193 : List PrefixCut := [⟨39,133302665,133302738⟩,
⟨64,220005914,220006036⟩]
theorem checked56193 : checkPrefixCuts (2^48) 7369261057 10 Manual.Count131072.C056193.packed 64 cuts56193 = true := by
 decide +kernel
def pointBounds56193 : List (Nat × Nat × Nat) := [(7369340928,113106459606373,113106847552021)]
theorem point_links_checked56193 : (cuts56193.take 1).map (fun c => (7369261057-1+2*2^10*c.k,113106326303708+c.lower,113106714249283+c.upper)) = pointBounds56193 := by
 decide +kernel
def cuts56194 : List PrefixCut := [⟨64,222102706,222102832⟩]
theorem checked56194 : checkPrefixCuts (2^48) 7369392129 10 Manual.Count131072.C056194.packed 64 cuts56194 = true := by
 decide +kernel
def cuts56195 : List PrefixCut := [⟨24,83072654,83072701⟩,
⟨64,222289732,222289859⟩]
theorem checked56195 : checkPrefixCuts (2^48) 7369523201 10 Manual.Count131072.C056195.packed 64 cuts56195 = true := by
 decide +kernel
def pointBounds56195 : List (Nat × Nat × Nat) := [(7369572352,113106851484982,113107239430852)]
theorem point_links_checked56195 : (cuts56195.take 1).map (fun c => (7369523201-1+2*2^10*c.k,113106768412328+c.lower,113107156358151+c.upper)) = pointBounds56195 := by
 decide +kernel
def cuts56196 : List PrefixCut := [⟨64,221674674,221674798⟩]
theorem checked56196 : checkPrefixCuts (2^48) 7369654273 10 Manual.Count131072.C056196.packed 64 cuts56196 = true := by
 decide +kernel
def cuts56197 : List PrefixCut := [⟨9,31471068,31471087⟩,
⟨64,219150038,219150164⟩]
theorem checked56197 : checkPrefixCuts (2^48) 7369785345 10 Manual.Count131072.C056197.packed 64 cuts56197 = true := by
 decide +kernel
def pointBounds56197 : List (Nat × Nat × Nat) := [(7369803776,113107243847802,113107631793895)]
theorem point_links_checked56197 : (cuts56197.take 1).map (fun c => (7369785345-1+2*2^10*c.k,113107212376734+c.lower,113107600322808+c.upper)) = pointBounds56197 := by
 decide +kernel
def cuts56198 : List PrefixCut := [⟨58,204060428,204060543⟩,
⟨64,224263871,224263998⟩]
theorem checked56198 : checkPrefixCuts (2^48) 7369916417 10 Manual.Count131072.C056198.packed 64 cuts56198 = true := by
 decide +kernel
def pointBounds56198 : List (Nat × Nat × Nat) := [(7370035200,113107635587200,113108023533515)]
theorem point_links_checked56198 : (cuts56198.take 1).map (fun c => (7369916417-1+2*2^10*c.k,113107431526772+c.lower,113107819472972+c.upper)) = pointBounds56198 := by
 decide +kernel
def cuts56199 : List PrefixCut := [⟨64,222197551,222197673⟩]
theorem checked56199 : checkPrefixCuts (2^48) 7370047489 10 Manual.Count131072.C056199.packed 64 cuts56199 = true := by
 decide +kernel
def cuts56200 : List PrefixCut := [⟨43,147378401,147378489⟩,
⟨64,219940327,219940457⟩]
theorem checked56200 : checkPrefixCuts (2^48) 7370178561 10 Manual.Count131072.C056200.packed 64 cuts56200 = true := by
 decide +kernel
def pointBounds56200 : List (Nat × Nat × Nat) := [(7370266624,113108025366595,113108413313132)]
theorem point_links_checked56200 : (cuts56200.take 1).map (fun c => (7370178561-1+2*2^10*c.k,113107877988194+c.lower,113108265934643+c.upper)) = pointBounds56200 := by
 decide +kernel
def cuts56201 : List PrefixCut := [⟨64,215964656,215964781⟩]
theorem checked56201 : checkPrefixCuts (2^48) 7370309633 10 Manual.Count131072.C056201.packed 64 cuts56201 = true := by
 decide +kernel
def cuts56202 : List PrefixCut := [⟨28,95817575,95817630⟩,
⟨64,217221070,217221193⟩]
theorem checked56202 : checkPrefixCuts (2^48) 7370440705 10 Manual.Count131072.C056202.packed 64 cuts56202 = true := by
 decide +kernel
def pointBounds56202 : List (Nat × Nat × Nat) := [(7370498048,113108409710752,113108797657511)]
theorem point_links_checked56202 : (cuts56202.take 1).map (fun c => (7370440705-1+2*2^10*c.k,113108313893177+c.lower,113108701839881+c.upper)) = pointBounds56202 := by
 decide +kernel
def cuts56203 : List PrefixCut := [⟨64,222983701,222983826⟩]
theorem checked56203 : checkPrefixCuts (2^48) 7370571777 10 Manual.Count131072.C056203.packed 64 cuts56203 = true := by
 decide +kernel
def cuts56204 : List PrefixCut := [⟨13,45214913,45214938⟩,
⟨64,220459319,220459444⟩]
theorem checked56204 : checkPrefixCuts (2^48) 7370702849 10 Manual.Count131072.C056204.packed 64 cuts56204 = true := by
 decide +kernel
def pointBounds56204 : List (Nat × Nat × Nat) := [(7370729472,113108799312861,113109187259838)]
theorem point_links_checked56204 : (cuts56204.take 1).map (fun c => (7370702849-1+2*2^10*c.k,113108754097948+c.lower,113109142044900+c.upper)) = pointBounds56204 := by
 decide +kernel
def cuts56205 : List PrefixCut := [⟨62,211252308,211252430⟩,
⟨64,217438601,217438726⟩]
theorem checked56205 : checkPrefixCuts (2^48) 7370833921 10 Manual.Count131072.C056205.packed 64 cuts56205 = true := by
 decide +kernel
def pointBounds56205 : List (Nat × Nat × Nat) := [(7370960896,113109185809575,113109573756774)]
theorem point_links_checked56205 : (cuts56205.take 1).map (fun c => (7370833921-1+2*2^10*c.k,113108974557267+c.lower,113109362504344+c.upper)) = pointBounds56205 := by
 decide +kernel
def cuts56206 : List PrefixCut := [⟨64,220833339,220833465⟩]
theorem checked56206 : checkPrefixCuts (2^48) 7370964993 10 Manual.Count131072.C056206.packed 64 cuts56206 = true := by
 decide +kernel
def cuts56207 : List PrefixCut := [⟨47,160572348,160572437⟩,
⟨64,218385514,218385637⟩]
theorem checked56207 : checkPrefixCuts (2^48) 7371096065 10 Manual.Count131072.C056207.packed 64 cuts56207 = true := by
 decide +kernel
def pointBounds56207 : List (Nat × Nat × Nat) := [(7371192320,113109573401555,113109961348972)]
theorem point_links_checked56207 : (cuts56207.take 1).map (fun c => (7371096065-1+2*2^10*c.k,113109412829207+c.lower,113109800776535+c.upper)) = pointBounds56207 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000193
