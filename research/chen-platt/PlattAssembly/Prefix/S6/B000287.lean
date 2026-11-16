import PlattAssemblyKernel
import PlattCertificates.Count131072.C059184
import PlattCertificates.Count131072.C059185
import PlattCertificates.Count131072.C059186
import PlattCertificates.Count131072.C059187
import PlattCertificates.Count131072.C059188
import PlattCertificates.Count131072.C059189
import PlattCertificates.Count131072.C059190
import PlattCertificates.Count131072.C059191
import PlattCertificates.Count131072.C059192
import PlattCertificates.Count131072.C059193
import PlattCertificates.Count131072.C059194
import PlattCertificates.Count131072.C059195
import PlattCertificates.Count131072.C059196
import PlattCertificates.Count131072.C059197
import PlattCertificates.Count131072.C059198
import PlattCertificates.Count131072.C059199
import PlattCertificates.Count131072.C059200
import PlattCertificates.Count131072.C059201
import PlattCertificates.Count131072.C059202
import PlattCertificates.Count131072.C059203
import PlattCertificates.Count131072.C059204
import PlattCertificates.Count131072.C059205
import PlattCertificates.Count131072.C059206
import PlattCertificates.Count131072.C059207
import PlattCertificates.Count131072.C059208
import PlattCertificates.Count131072.C059209
import PlattCertificates.Count131072.C059210
import PlattCertificates.Count131072.C059211
import PlattCertificates.Count131072.C059212
import PlattCertificates.Count131072.C059213
import PlattCertificates.Count131072.C059214
import PlattCertificates.Count131072.C059215
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000287
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts59184 : List PrefixCut := [⟨64,207224872,207224991⟩]
theorem checked59184 : checkPrefixCuts (2^48) 7761297409 10 Manual.Count131072.C059184.packed 64 cuts59184 = true := by
 decide +kernel
def cuts59185 : List PrefixCut := [⟨33,106222249,106222306⟩,
⟨64,207982957,207983070⟩]
theorem checked59185 : checkPrefixCuts (2^48) 7761428481 10 Manual.Count131072.C059185.packed 64 cuts59185 = true := by
 decide +kernel
def pointBounds59185 : List (Nat × Nat × Nat) := [(7761496064,113747959635869,113748347946766)]
theorem point_links_checked59185 : (cuts59185.take 1).map (fun c => (7761428481-1+2*2^10*c.k,113747853413620+c.lower,113748241724460+c.upper)) = pointBounds59185 := by
 decide +kernel
def cuts59186 : List PrefixCut := [⟨64,209937753,209937875⟩]
theorem checked59186 : checkPrefixCuts (2^48) 7761559553 10 Manual.Count131072.C059186.packed 64 cuts59186 = true := by
 decide +kernel
def cuts59187 : List PrefixCut := [⟨24,78875338,78875382⟩,
⟨64,210514441,210514558⟩]
theorem checked59187 : checkPrefixCuts (2^48) 7761690625 10 Manual.Count131072.C059187.packed 64 cuts59187 = true := by
 decide +kernel
def pointBounds59187 : List (Nat × Nat × Nat) := [(7761739776,113748350209668,113748738520787)]
theorem point_links_checked59187 : (cuts59187.take 1).map (fun c => (7761690625-1+2*2^10*c.k,113748271334330+c.lower,113748659645405+c.upper)) = pointBounds59187 := by
 decide +kernel
def cuts59188 : List PrefixCut := [⟨64,209894407,209894525⟩]
theorem checked59188 : checkPrefixCuts (2^48) 7761821697 10 Manual.Count131072.C059188.packed 64 cuts59188 = true := by
 decide +kernel
def cuts59189 : List PrefixCut := [⟨15,47722554,47722583⟩,
⟨64,208621638,208621759⟩]
theorem checked59189 : checkPrefixCuts (2^48) 7761952769 10 Manual.Count131072.C059189.packed 64 cuts59189 = true := by
 decide +kernel
def pointBounds59189 : List (Nat × Nat × Nat) := [(7761983488,113748739465732,113749127777071)]
theorem point_links_checked59189 : (cuts59189.take 1).map (fun c => (7761952769-1+2*2^10*c.k,113748691743178+c.lower,113749080054488+c.upper)) = pointBounds59189 := by
 decide +kernel
def cuts59190 : List PrefixCut := [⟨64,210612566,210612685⟩]
theorem checked59190 : checkPrefixCuts (2^48) 7762083841 10 Manual.Count131072.C059190.packed 64 cuts59190 = true := by
 decide +kernel
def cuts59191 : List PrefixCut := [⟨6,19255208,19255218⟩,
⟨64,211080397,211080520⟩]
theorem checked59191 : checkPrefixCuts (2^48) 7762214913 10 Manual.Count131072.C059191.packed 64 cuts59191 = true := by
 decide +kernel
def pointBounds59191 : List (Nat × Nat × Nat) := [(7762227200,113749130232590,113749518544150)]
theorem point_links_checked59191 : (cuts59191.take 1).map (fun c => (7762214913-1+2*2^10*c.k,113749110977382+c.lower,113749499288932+c.upper)) = pointBounds59191 := by
 decide +kernel
def cuts59192 : List PrefixCut := [⟨61,198566798,198566915⟩,
⟨64,208103435,208103558⟩]
theorem checked59192 : checkPrefixCuts (2^48) 7762345985 10 Manual.Count131072.C059192.packed 64 cuts59192 = true := by
 decide +kernel
def pointBounds59192 : List (Nat × Nat × Nat) := [(7762470912,113749520624577,113749908936367)]
theorem point_links_checked59192 : (cuts59192.take 1).map (fun c => (7762345985-1+2*2^10*c.k,113749322057779+c.lower,113749710369452+c.upper)) = pointBounds59192 := by
 decide +kernel
def cuts59193 : List PrefixCut := [⟨64,207302200,207302320⟩]
theorem checked59193 : checkPrefixCuts (2^48) 7762477057 10 Manual.Count131072.C059193.packed 64 cuts59193 = true := by
 decide +kernel
def cuts59194 : List PrefixCut := [⟨52,169334676,169334771⟩,
⟨64,208386476,208386595⟩]
theorem checked59194 : checkPrefixCuts (2^48) 7762608129 10 Manual.Count131072.C059194.packed 64 cuts59194 = true := by
 decide +kernel
def pointBounds59194 : List (Nat × Nat × Nat) := [(7762714624,113749906798090,113750295110101)]
theorem point_links_checked59194 : (cuts59194.take 1).map (fun c => (7762608129-1+2*2^10*c.k,113749737463414+c.lower,113750125775330+c.upper)) = pointBounds59194 := by
 decide +kernel
def cuts59195 : List PrefixCut := [⟨64,210957376,210957494⟩]
theorem checked59195 : checkPrefixCuts (2^48) 7762739201 10 Manual.Count131072.C059195.packed 64 cuts59195 = true := by
 decide +kernel
def cuts59196 : List PrefixCut := [⟨43,139705618,139705696⟩,
⟨64,208633248,208633365⟩]
theorem checked59196 : checkPrefixCuts (2^48) 7762870273 10 Manual.Count131072.C059196.packed 64 cuts59196 = true := by
 decide +kernel
def pointBounds59196 : List (Nat × Nat × Nat) := [(7762958336,113750296512884,113750684825115)]
theorem point_links_checked59196 : (cuts59196.take 1).map (fun c => (7762870273-1+2*2^10*c.k,113750156807266+c.lower,113750545119419+c.upper)) = pointBounds59196 := by
 decide +kernel
def cuts59197 : List PrefixCut := [⟨64,209318639,209318762⟩]
theorem checked59197 : checkPrefixCuts (2^48) 7763001345 10 Manual.Count131072.C059197.packed 64 cuts59197 = true := by
 decide +kernel
def cuts59198 : List PrefixCut := [⟨34,111166236,111166298⟩,
⟨64,207756039,207756155⟩]
theorem checked59198 : checkPrefixCuts (2^48) 7763132417 10 Manual.Count131072.C059198.packed 64 cuts59198 = true := by
 decide +kernel
def pointBounds59198 : List (Nat × Nat × Nat) := [(7763202048,113750685925389,113751074237844)]
theorem point_links_checked59198 : (cuts59198.take 1).map (fun c => (7763132417-1+2*2^10*c.k,113750574759153+c.lower,113750963071546+c.upper)) = pointBounds59198 := by
 decide +kernel
def cuts59199 : List PrefixCut := [⟨64,209275319,209275440⟩]
theorem checked59199 : checkPrefixCuts (2^48) 7763263489 10 Manual.Count131072.C059199.packed 64 cuts59199 = true := by
 decide +kernel
def cuts59200 : List PrefixCut := [⟨25,83643878,83643925⟩,
⟨64,210794558,210794676⟩]
theorem checked59200 : checkPrefixCuts (2^48) 7763394561 10 Manual.Count131072.C059200.packed 64 cuts59200 = true := by
 decide +kernel
def pointBounds59200 : List (Nat × Nat × Nat) := [(7763445760,113751075434389,113751463747066)]
theorem point_links_checked59200 : (cuts59200.take 1).map (fun c => (7763394561-1+2*2^10*c.k,113750991790511+c.lower,113751380103141+c.upper)) = pointBounds59200 := by
 decide +kernel
def cuts59201 : List PrefixCut := [⟨64,211153537,211153660⟩]
theorem checked59201 : checkPrefixCuts (2^48) 7763525633 10 Manual.Count131072.C059201.packed 64 cuts59201 = true := by
 decide +kernel
def cuts59202 : List PrefixCut := [⟨16,52098977,52099008⟩,
⟨64,210171073,210171197⟩]
theorem checked59202 : checkPrefixCuts (2^48) 7763656705 10 Manual.Count131072.C059202.packed 64 cuts59202 = true := by
 decide +kernel
def pointBounds59202 : List (Nat × Nat × Nat) := [(7763689472,113751465837583,113751854150485)]
theorem point_links_checked59202 : (cuts59202.take 1).map (fun c => (7763656705-1+2*2^10*c.k,113751413738606+c.lower,113751802051477+c.upper)) = pointBounds59202 := by
 decide +kernel
def cuts59203 : List PrefixCut := [⟨64,209333685,209333803⟩]
theorem checked59203 : checkPrefixCuts (2^48) 7763787777 10 Manual.Count131072.C059203.packed 64 cuts59203 = true := by
 decide +kernel
def cuts59204 : List PrefixCut := [⟨7,22550109,22550123⟩,
⟨64,208351297,208351415⟩]
theorem checked59204 : checkPrefixCuts (2^48) 7763918849 10 Manual.Count131072.C059204.packed 64 cuts59204 = true := by
 decide +kernel
def pointBounds59204 : List (Nat × Nat × Nat) := [(7763933184,113751855793473,113752244106600)]
theorem point_links_checked59204 : (cuts59204.take 1).map (fun c => (7763918849-1+2*2^10*c.k,113751833243364+c.lower,113752221556477+c.upper)) = pointBounds59204 := by
 decide +kernel
def cuts59205 : List PrefixCut := [⟨62,198196895,198197008⟩,
⟨64,204867450,204867567⟩]
theorem checked59205 : checkPrefixCuts (2^48) 7764049921 10 Manual.Count131072.C059205.packed 64 cuts59205 = true := by
 decide +kernel
def pointBounds59205 : List (Nat × Nat × Nat) := [(7764176896,113752239791556,113752628104900)]
theorem point_links_checked59205 : (cuts59205.take 1).map (fun c => (7764049921-1+2*2^10*c.k,113752041594661+c.lower,113752429907892+c.upper)) = pointBounds59205 := by
 decide +kernel
def cuts59206 : List PrefixCut := [⟨64,206604145,206604265⟩]
theorem checked59206 : checkPrefixCuts (2^48) 7764180993 10 Manual.Count131072.C059206.packed 64 cuts59206 = true := by
 decide +kernel
def cuts59207 : List PrefixCut := [⟨53,172777707,172777804⟩,
⟨64,208884535,208884652⟩]
theorem checked59207 : checkPrefixCuts (2^48) 7764312065 10 Manual.Count131072.C059207.packed 64 cuts59207 = true := by
 decide +kernel
def pointBounds59207 : List (Nat × Nat × Nat) := [(7764420608,113752625843963,113753014157528)]
theorem point_links_checked59207 : (cuts59207.take 1).map (fun c => (7764312065-1+2*2^10*c.k,113752453066256+c.lower,113752841379724+c.upper)) = pointBounds59207 := by
 decide +kernel
def cuts59208 : List PrefixCut := [⟨64,204820835,204820954⟩]
theorem checked59208 : checkPrefixCuts (2^48) 7764443137 10 Manual.Count131072.C059208.packed 64 cuts59208 = true := by
 decide +kernel
def cuts59209 : List PrefixCut := [⟨44,146490135,146490221⟩,
⟨64,209892525,209892649⟩]
theorem checked59209 : checkPrefixCuts (2^48) 7764574209 10 Manual.Count131072.C059209.packed 64 cuts59209 = true := by
 decide +kernel
def pointBounds59209 : List (Nat × Nat × Nat) := [(7764664320,113753013261761,113753401575551)]
theorem point_links_checked59209 : (cuts59209.take 1).map (fun c => (7764574209-1+2*2^10*c.k,113752866771626+c.lower,113753255085330+c.upper)) = pointBounds59209 := by
 decide +kernel
def cuts59210 : List PrefixCut := [⟨64,207387697,207387813⟩]
theorem checked59210 : checkPrefixCuts (2^48) 7764705281 10 Manual.Count131072.C059210.packed 64 cuts59210 = true := by
 decide +kernel
def cuts59211 : List PrefixCut := [⟨35,112591807,112591874⟩,
⟨64,208471658,208471782⟩]
theorem checked59211 : checkPrefixCuts (2^48) 7764836353 10 Manual.Count131072.C059211.packed 64 cuts59211 = true := by
 decide +kernel
def pointBounds59211 : List (Nat × Nat × Nat) := [(7764908032,113753396643655,113753784957666)]
theorem point_links_checked59211 : (cuts59211.take 1).map (fun c => (7764836353-1+2*2^10*c.k,113753284051848+c.lower,113753672365792+c.upper)) = pointBounds59211 := by
 decide +kernel
def cuts59212 : List PrefixCut := [⟨64,210280619,210280734⟩]
theorem checked59212 : checkPrefixCuts (2^48) 7764967425 10 Manual.Count131072.C059212.packed 64 cuts59212 = true := by
 decide +kernel
def cuts59213 : List PrefixCut := [⟨26,84132997,84133045⟩,
⟨64,206217241,206217361⟩]
theorem checked59213 : checkPrefixCuts (2^48) 7765098497 10 Manual.Count131072.C059213.packed 64 cuts59213 = true := by
 decide +kernel
def pointBounds59213 : List (Nat × Nat × Nat) := [(7765151744,113753786937122,113754175251353)]
theorem point_links_checked59213 : (cuts59213.take 1).map (fun c => (7765098497-1+2*2^10*c.k,113753702804125+c.lower,113754091118308+c.upper)) = pointBounds59213 := by
 decide +kernel
def cuts59214 : List PrefixCut := [⟨64,207337452,207337570⟩]
theorem checked59214 : checkPrefixCuts (2^48) 7765229569 10 Manual.Count131072.C059214.packed 64 cuts59214 = true := by
 decide +kernel
def cuts59215 : List PrefixCut := [⟨17,54806097,54806129⟩,
⟨64,206246523,206246643⟩]
theorem checked59215 : checkPrefixCuts (2^48) 7765360641 10 Manual.Count131072.C059215.packed 64 cuts59215 = true := by
 decide +kernel
def pointBounds59215 : List (Nat × Nat × Nat) := [(7765395456,113754171164915,113754559479368)]
theorem point_links_checked59215 : (cuts59215.take 1).map (fun c => (7765360641-1+2*2^10*c.k,113754116358818+c.lower,113754504673239+c.upper)) = pointBounds59215 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000287
