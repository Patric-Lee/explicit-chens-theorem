import PlattAssemblyKernel
import PlattCertificates.Count131072.C056208
import PlattCertificates.Count131072.C056209
import PlattCertificates.Count131072.C056210
import PlattCertificates.Count131072.C056211
import PlattCertificates.Count131072.C056212
import PlattCertificates.Count131072.C056213
import PlattCertificates.Count131072.C056214
import PlattCertificates.Count131072.C056215
import PlattCertificates.Count131072.C056216
import PlattCertificates.Count131072.C056217
import PlattCertificates.Count131072.C056218
import PlattCertificates.Count131072.C056219
import PlattCertificates.Count131072.C056220
import PlattCertificates.Count131072.C056221
import PlattCertificates.Count131072.C056222
import PlattCertificates.Count131072.C056223
import PlattCertificates.Count131072.C056224
import PlattCertificates.Count131072.C056225
import PlattCertificates.Count131072.C056226
import PlattCertificates.Count131072.C056227
import PlattCertificates.Count131072.C056228
import PlattCertificates.Count131072.C056229
import PlattCertificates.Count131072.C056230
import PlattCertificates.Count131072.C056231
import PlattCertificates.Count131072.C056232
import PlattCertificates.Count131072.C056233
import PlattCertificates.Count131072.C056234
import PlattCertificates.Count131072.C056235
import PlattCertificates.Count131072.C056236
import PlattCertificates.Count131072.C056237
import PlattCertificates.Count131072.C056238
import PlattCertificates.Count131072.C056239
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000194
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts56208 : List PrefixCut := [⟨64,217312455,217312578⟩]
theorem checked56208 : checkPrefixCuts (2^48) 7371227137 10 Manual.Count131072.C056208.packed 64 cuts56208 = true := by
 decide +kernel
def cuts56209 : List PrefixCut := [⟨32,109284829,109284891⟩,
⟨64,219943320,219943442⟩]
theorem checked56209 : checkPrefixCuts (2^48) 7371358209 10 Manual.Count131072.C056209.packed 64 cuts56209 = true := by
 decide +kernel
def pointBounds56209 : List (Nat × Nat × Nat) := [(7371423744,113109957812005,113110345759641)]
theorem point_links_checked56209 : (cuts56209.take 1).map (fun c => (7371358209-1+2*2^10*c.k,113109848527176+c.lower,113110236474750+c.upper)) = pointBounds56209 := by
 decide +kernel
def cuts56210 : List PrefixCut := [⟨64,222115914,222116040⟩]
theorem checked56210 : checkPrefixCuts (2^48) 7371489281 10 Manual.Count131072.C056210.packed 64 cuts56210 = true := by
 decide +kernel
def cuts56211 : List PrefixCut := [⟨17,58878950,58878984⟩,
⟨64,217415427,217415552⟩]
theorem checked56211 : checkPrefixCuts (2^48) 7371620353 10 Manual.Count131072.C056211.packed 64 cuts56211 = true := by
 decide +kernel
def pointBounds56211 : List (Nat × Nat × Nat) := [(7371655168,113110349465360,113110737413216)]
theorem point_links_checked56211 : (cuts56211.take 1).map (fun c => (7371620353-1+2*2^10*c.k,113110290586410+c.lower,113110678534232+c.upper)) = pointBounds56211 := by
 decide +kernel
def cuts56212 : List PrefixCut := [⟨64,219740655,219740783⟩]
theorem checked56212 : checkPrefixCuts (2^48) 7371751425 10 Manual.Count131072.C056212.packed 64 cuts56212 = true := by
 decide +kernel
def cuts56213 : List PrefixCut := [⟨2,7025528,7025532⟩,
⟨64,218094963,218095086⟩]
theorem checked56213 : checkPrefixCuts (2^48) 7371882497 10 Manual.Count131072.C056213.packed 64 cuts56213 = true := by
 decide +kernel
def pointBounds56213 : List (Nat × Nat × Nat) := [(7371886592,113110734768020,113111122716099)]
theorem point_links_checked56213 : (cuts56213.take 1).map (fun c => (7371882497-1+2*2^10*c.k,113110727742492+c.lower,113111115690567+c.upper)) = pointBounds56213 := by
 decide +kernel
def cuts56214 : List PrefixCut := [⟨51,176473874,176473975⟩,
⟨64,221374656,221374783⟩]
theorem checked56214 : checkPrefixCuts (2^48) 7372013569 10 Manual.Count131072.C056214.packed 64 cuts56214 = true := by
 decide +kernel
def pointBounds56214 : List (Nat × Nat × Nat) := [(7372118016,113111122311329,113111510259628)]
theorem point_links_checked56214 : (cuts56214.take 1).map (fun c => (7372013569-1+2*2^10*c.k,113110945837455+c.lower,113111333785653+c.upper)) = pointBounds56214 := by
 decide +kernel
def cuts56215 : List PrefixCut := [⟨64,218583534,218583656⟩]
theorem checked56215 : checkPrefixCuts (2^48) 7372144641 10 Manual.Count131072.C056215.packed 64 cuts56215 = true := by
 decide +kernel
def cuts56216 : List PrefixCut := [⟨36,124008637,124008707⟩,
⟨64,217243360,217243485⟩]
theorem checked56216 : checkPrefixCuts (2^48) 7372275713 10 Manual.Count131072.C056216.packed 64 cuts56216 = true := by
 decide +kernel
def pointBounds56216 : List (Nat × Nat × Nat) := [(7372349440,113111509804282,113111897752799)]
theorem point_links_checked56216 : (cuts56216.take 1).map (fun c => (7372275713-1+2*2^10*c.k,113111385795645+c.lower,113111773744092+c.upper)) = pointBounds56216 := by
 decide +kernel
def cuts56217 : List PrefixCut := [⟨64,218003071,218003196⟩]
theorem checked56217 : checkPrefixCuts (2^48) 7372406785 10 Manual.Count131072.C056217.packed 64 cuts56217 = true := by
 decide +kernel
def cuts56218 : List PrefixCut := [⟨21,74066725,74066766⟩,
⟨64,221855240,221855364⟩]
theorem checked56218 : checkPrefixCuts (2^48) 7372537857 10 Manual.Count131072.C056218.packed 64 cuts56218 = true := by
 decide +kernel
def pointBounds56218 : List (Nat × Nat × Nat) := [(7372580864,113111895108801,113112283057539)]
theorem point_links_checked56218 : (cuts56218.take 1).map (fun c => (7372537857-1+2*2^10*c.k,113111821042076+c.lower,113112208990773+c.upper)) = pointBounds56218 := by
 decide +kernel
def cuts56219 : List PrefixCut := [⟨64,218224364,218224489⟩]
theorem checked56219 : checkPrefixCuts (2^48) 7372668929 10 Manual.Count131072.C056219.packed 64 cuts56219 = true := by
 decide +kernel
def cuts56220 : List PrefixCut := [⟨6,20386757,20386767⟩,
⟨64,218335056,218335179⟩]
theorem checked56220 : checkPrefixCuts (2^48) 7372800001 10 Manual.Count131072.C056220.packed 64 cuts56220 = true := by
 decide +kernel
def pointBounds56220 : List (Nat × Nat × Nat) := [(7372812288,113112281508437,113112669457393)]
theorem point_links_checked56220 : (cuts56220.take 1).map (fun c => (7372800001-1+2*2^10*c.k,113112261121680+c.lower,113112649070626+c.upper)) = pointBounds56220 := by
 decide +kernel
def cuts56221 : List PrefixCut := [⟨55,187637520,187637629⟩,
⟨64,219361912,219362040⟩]
theorem checked56221 : checkPrefixCuts (2^48) 7372931073 10 Manual.Count131072.C056221.packed 64 cuts56221 = true := by
 decide +kernel
def pointBounds56221 : List (Nat × Nat × Nat) := [(7373043712,113112667094256,113113055043434)]
theorem point_links_checked56221 : (cuts56221.take 1).map (fun c => (7372931073-1+2*2^10*c.k,113112479456736+c.lower,113112867405805+c.upper)) = pointBounds56221 := by
 decide +kernel
def cuts56222 : List PrefixCut := [⟨64,220236072,220236195⟩]
theorem checked56222 : checkPrefixCuts (2^48) 7373062145 10 Manual.Count131072.C056222.packed 64 cuts56222 = true := by
 decide +kernel
def cuts56223 : List PrefixCut := [⟨40,138957837,138957916⟩,
⟨64,221110195,221110322⟩]
theorem checked56223 : checkPrefixCuts (2^48) 7373193217 10 Manual.Count131072.C056223.packed 64 cuts56223 = true := by
 decide +kernel
def pointBounds56223 : List (Nat × Nat × Nat) := [(7373275136,113113058012557,113113445961956)]
theorem point_links_checked56223 : (cuts56223.take 1).map (fun c => (7373193217-1+2*2^10*c.k,113112919054720+c.lower,113113307004040+c.upper)) = pointBounds56223 := by
 decide +kernel
def cuts56224 : List PrefixCut := [⟨64,221907913,221908038⟩]
theorem checked56224 : checkPrefixCuts (2^48) 7373324289 10 Manual.Count131072.C056224.packed 64 cuts56224 = true := by
 decide +kernel
def cuts56225 : List PrefixCut := [⟨25,86807559,86807609⟩,
⟨64,217781213,217781339⟩]
theorem checked56225 : checkPrefixCuts (2^48) 7373455361 10 Manual.Count131072.C056225.packed 64 cuts56225 = true := by
 decide +kernel
def pointBounds56225 : List (Nat × Nat × Nat) := [(7373506560,113113448880387,113113836830009)]
theorem point_links_checked56225 : (cuts56225.take 1).map (fun c => (7373455361-1+2*2^10*c.k,113113362072828+c.lower,113113750022400+c.upper)) = pointBounds56225 := by
 decide +kernel
def cuts56226 : List PrefixCut := [⟨64,221785510,221785637⟩]
theorem checked56226 : checkPrefixCuts (2^48) 7373586433 10 Manual.Count131072.C056226.packed 64 cuts56226 = true := by
 decide +kernel
def cuts56227 : List PrefixCut := [⟨10,35691448,35691467⟩,
⟨64,223881035,223881161⟩]
theorem checked56227 : checkPrefixCuts (2^48) 7373717505 10 Manual.Count131072.C056227.packed 64 cuts56227 = true := by
 decide +kernel
def pointBounds56227 : List (Nat × Nat × Nat) := [(7373737984,113113837330999,113114225280843)]
theorem point_links_checked56227 : (cuts56227.take 1).map (fun c => (7373717505-1+2*2^10*c.k,113113801639551+c.lower,113114189589376+c.upper)) = pointBounds56227 := by
 decide +kernel
def cuts56228 : List PrefixCut := [⟨59,202768260,202768374⟩,
⟨64,219792702,219792825⟩]
theorem checked56228 : checkPrefixCuts (2^48) 7373848577 10 Manual.Count131072.C056228.packed 64 cuts56228 = true := by
 decide +kernel
def pointBounds56228 : List (Nat × Nat × Nat) := [(7373969408,113114228288846,113114616238911)]
theorem point_links_checked56228 : (cuts56228.take 1).map (fun c => (7373848577-1+2*2^10*c.k,113114025520586+c.lower,113114413470537+c.upper)) = pointBounds56228 := by
 decide +kernel
def cuts56229 : List PrefixCut := [⟨64,219445248,219445373⟩]
theorem checked56229 : checkPrefixCuts (2^48) 7373979649 10 Manual.Count131072.C056229.packed 64 cuts56229 = true := by
 decide +kernel
def cuts56230 : List PrefixCut := [⟨44,150887812,150887898⟩,
⟨64,218487092,218487216⟩]
theorem checked56230 : checkPrefixCuts (2^48) 7374110721 10 Manual.Count131072.C056230.packed 64 cuts56230 = true := by
 decide +kernel
def pointBounds56230 : List (Nat × Nat × Nat) := [(7374200832,113114615646348,113115003596633)]
theorem point_links_checked56230 : (cuts56230.take 1).map (fun c => (7374110721-1+2*2^10*c.k,113114464758536+c.lower,113114852708735+c.upper)) = pointBounds56230 := by
 decide +kernel
def cuts56231 : List PrefixCut := [⟨64,217872490,217872614⟩]
theorem checked56231 : checkPrefixCuts (2^48) 7374241793 10 Manual.Count131072.C056231.packed 64 cuts56231 = true := by
 decide +kernel
def cuts56232 : List PrefixCut := [⟨29,98132962,98133018⟩,
⟨64,214586095,214586218⟩]
theorem checked56232 : checkPrefixCuts (2^48) 7374372865 10 Manual.Count131072.C056232.packed 64 cuts56232 = true := by
 decide +kernel
def pointBounds56232 : List (Nat × Nat × Nat) := [(7374432256,113114999251080,113115387201583)]
theorem point_links_checked56232 : (cuts56232.take 1).map (fun c => (7374372865-1+2*2^10*c.k,113114901118118+c.lower,113115289068565+c.upper)) = pointBounds56232 := by
 decide +kernel
def cuts56233 : List PrefixCut := [⟨64,221986939,221987064⟩]
theorem checked56233 : checkPrefixCuts (2^48) 7374503937 10 Manual.Count131072.C056233.packed 64 cuts56233 = true := by
 decide +kernel
def cuts56234 : List PrefixCut := [⟨14,48282397,48282425⟩,
⟨64,221868471,221868596⟩]
theorem checked56234 : checkPrefixCuts (2^48) 7374635009 10 Manual.Count131072.C056234.packed 64 cuts56234 = true := by
 decide +kernel
def pointBounds56234 : List (Nat × Nat × Nat) := [(7374663680,113115385973549,113115773924272)]
theorem point_links_checked56234 : (cuts56234.take 1).map (fun c => (7374635009-1+2*2^10*c.k,113115337691152+c.lower,113115725641847+c.upper)) = pointBounds56234 := by
 decide +kernel
def cuts56235 : List PrefixCut := [⟨63,216139513,216139638⟩,
⟨64,219345509,219345636⟩]
theorem checked56235 : checkPrefixCuts (2^48) 7374766081 10 Manual.Count131072.C056235.packed 64 cuts56235 = true := by
 decide +kernel
def pointBounds56235 : List (Nat × Nat × Nat) := [(7374895104,113115775699136,113116163650081)]
theorem point_links_checked56235 : (cuts56235.take 1).map (fun c => (7374766081-1+2*2^10*c.k,113115559559623+c.lower,113115947510443+c.upper)) = pointBounds56235 := by
 decide +kernel
def cuts56236 : List PrefixCut := [⟨64,218158443,218158565⟩]
theorem checked56236 : checkPrefixCuts (2^48) 7374897153 10 Manual.Count131072.C056236.packed 64 cuts56236 = true := by
 decide +kernel
def cuts56237 : List PrefixCut := [⟨48,167089381,167089476⟩,
⟨64,221246009,221246136⟩]
theorem checked56237 : checkPrefixCuts (2^48) 7375028225 10 Manual.Count131072.C056237.packed 64 cuts56237 = true := by
 decide +kernel
def pointBounds56237 : List (Nat × Nat × Nat) := [(7375126528,113116164152956,113116552104120)]
theorem point_links_checked56237 : (cuts56237.take 1).map (fun c => (7375028225-1+2*2^10*c.k,113115997063575+c.lower,113116385014644+c.upper)) = pointBounds56237 := by
 decide +kernel
def cuts56238 : List PrefixCut := [⟨64,221432881,221433005⟩]
theorem checked56238 : checkPrefixCuts (2^48) 7375159297 10 Manual.Count131072.C056238.packed 64 cuts56238 = true := by
 decide +kernel
def cuts56239 : List PrefixCut := [⟨33,113271965,113272029⟩,
⟨64,219329922,219330047⟩]
theorem checked56239 : checkPrefixCuts (2^48) 7375290369 10 Manual.Count131072.C056239.packed 64 cuts56239 = true := by
 decide +kernel
def pointBounds56239 : List (Nat × Nat × Nat) := [(7375357952,113116553014430,113116940965814)]
theorem point_links_checked56239 : (cuts56239.take 1).map (fun c => (7375290369-1+2*2^10*c.k,113116439742465+c.lower,113116827693785+c.upper)) = pointBounds56239 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000194
