import PlattAssemblyKernel
import PlattCertificates.Count131072.C069216
import PlattCertificates.Count131072.C069217
import PlattCertificates.Count131072.C069218
import PlattCertificates.Count131072.C069219
import PlattCertificates.Count131072.C069220
import PlattCertificates.Count131072.C069221
import PlattCertificates.Count131072.C069222
import PlattCertificates.Count131072.C069223
import PlattCertificates.Count131072.C069224
import PlattCertificates.Count131072.C069225
import PlattCertificates.Count131072.C069226
import PlattCertificates.Count131072.C069227
import PlattCertificates.Count131072.C069228
import PlattCertificates.Count131072.C069229
import PlattCertificates.Count131072.C069230
import PlattCertificates.Count131072.C069231
import PlattCertificates.Count131072.C069232
import PlattCertificates.Count131072.C069233
import PlattCertificates.Count131072.C069234
import PlattCertificates.Count131072.C069235
import PlattCertificates.Count131072.C069236
import PlattCertificates.Count131072.C069237
import PlattCertificates.Count131072.C069238
import PlattCertificates.Count131072.C069239
import PlattCertificates.Count131072.C069240
import PlattCertificates.Count131072.C069241
import PlattCertificates.Count131072.C069242
import PlattCertificates.Count131072.C069243
import PlattCertificates.Count131072.C069244
import PlattCertificates.Count131072.C069245
import PlattCertificates.Count131072.C069246
import PlattCertificates.Count131072.C069247
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000288
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69216 : List PrefixCut := [⟨64,177141413,177141515⟩]
theorem checked69216 : checkPrefixCuts (2^48) 9076211713 10 Manual.Count131072.C069216.packed 64 cuts69216 = true := by
 decide +kernel
def cuts69217 : List PrefixCut := [⟨64,176363562,176363671⟩]
theorem checked69217 : checkPrefixCuts (2^48) 9076342785 10 Manual.Count131072.C069217.packed 64 cuts69217 = true := by
 decide +kernel
def cuts69218 : List PrefixCut := [⟨3,8031970,8031976⟩,
⟨64,177880562,177880668⟩]
theorem checked69218 : checkPrefixCuts (2^48) 9076473857 10 Manual.Count131072.C069218.packed 64 cuts69218 = true := by
 decide +kernel
def pointBounds69218 : List (Nat × Nat × Nat) := [(9076480000,115675941972497,115676331396656)]
theorem point_links_checked69218 : (cuts69218.take 1).map (fun c => (9076473857-1+2*2^10*c.k,115675933940527+c.lower,115676323364680+c.upper)) = pointBounds69218 := by
 decide +kernel
def cuts69219 : List PrefixCut := [⟨64,176606548,176606651⟩]
theorem checked69219 : checkPrefixCuts (2^48) 9076604929 10 Manual.Count131072.C069219.packed 64 cuts69219 = true := by
 decide +kernel
def cuts69220 : List PrefixCut := [⟨14,38235990,38236012⟩,
⟨64,178805732,178805838⟩]
theorem checked69220 : checkPrefixCuts (2^48) 9076736001 10 Manual.Count131072.C069220.packed 64 cuts69220 = true := by
 decide +kernel
def pointBounds69220 : List (Nat × Nat × Nat) := [(9076764672,115676326663627,115676716088011)]
theorem point_links_checked69220 : (cuts69220.take 1).map (fun c => (9076736001-1+2*2^10*c.k,115676288427637+c.lower,115676677851999+c.upper)) = pointBounds69220 := by
 decide +kernel
def cuts69221 : List PrefixCut := [⟨64,177562756,177562860⟩]
theorem checked69221 : checkPrefixCuts (2^48) 9076867073 10 Manual.Count131072.C069221.packed 64 cuts69221 = true := by
 decide +kernel
def cuts69222 : List PrefixCut := [⟨25,70422805,70422845⟩,
⟨64,178273425,178273523⟩]
theorem checked69222 : checkPrefixCuts (2^48) 9076998145 10 Manual.Count131072.C069222.packed 64 cuts69222 = true := by
 decide +kernel
def pointBounds69222 : List (Nat × Nat × Nat) := [(9077049344,115676715218930,115677104643542)]
theorem point_links_checked69222 : (cuts69222.take 1).map (fun c => (9076998145-1+2*2^10*c.k,115676644796125+c.lower,115677034220697+c.upper)) = pointBounds69222 := by
 decide +kernel
def cuts69223 : List PrefixCut := [⟨64,177154514,177154618⟩]
theorem checked69223 : checkPrefixCuts (2^48) 9077129217 10 Manual.Count131072.C069223.packed 64 cuts69223 = true := by
 decide +kernel
def cuts69224 : List PrefixCut := [⟨36,100530099,100530155⟩,
⟨64,176810873,176810972⟩]
theorem checked69224 : checkPrefixCuts (2^48) 9077260289 10 Manual.Count131072.C069224.packed 64 cuts69224 = true := by
 decide +kernel
def pointBounds69224 : List (Nat × Nat × Nat) := [(9077334016,115677100754163,115677490178993)]
theorem point_links_checked69224 : (cuts69224.take 1).map (fun c => (9077260289-1+2*2^10*c.k,115677000224064+c.lower,115677389648838+c.upper)) = pointBounds69224 := by
 decide +kernel
def cuts69225 : List PrefixCut := [⟨64,181304494,181304606⟩]
theorem checked69225 : checkPrefixCuts (2^48) 9077391361 10 Manual.Count131072.C069225.packed 64 cuts69225 = true := by
 decide +kernel
def cuts69226 : List PrefixCut := [⟨47,130077441,130077515⟩,
⟨64,177363894,177363998⟩]
theorem checked69226 : checkPrefixCuts (2^48) 9077522433 10 Manual.Count131072.C069226.packed 64 cuts69226 = true := by
 decide +kernel
def pointBounds69226 : List (Nat × Nat × Nat) := [(9077618688,115677488416872,115677877841931)]
theorem point_links_checked69226 : (cuts69226.take 1).map (fun c => (9077522433-1+2*2^10*c.k,115677358339431+c.lower,115677747764416+c.upper)) = pointBounds69226 := by
 decide +kernel
def cuts69227 : List PrefixCut := [⟨64,175810979,175811087⟩]
theorem checked69227 : checkPrefixCuts (2^48) 9077653505 10 Manual.Count131072.C069227.packed 64 cuts69227 = true := by
 decide +kernel
def cuts69228 : List PrefixCut := [⟨58,159778045,159778141⟩,
⟨64,175219319,175219425⟩]
theorem checked69228 : checkPrefixCuts (2^48) 9077784577 10 Manual.Count131072.C069228.packed 64 cuts69228 = true := by
 decide +kernel
def pointBounds69228 : List (Nat × Nat × Nat) := [(9077903360,115677871292349,115678260717642)]
theorem point_links_checked69228 : (cuts69228.take 1).map (fun c => (9077784577-1+2*2^10*c.k,115677711514304+c.lower,115678100939501+c.upper)) = pointBounds69228 := by
 decide +kernel
def cuts69229 : List PrefixCut := [⟨64,178069372,178069473⟩]
theorem checked69229 : checkPrefixCuts (2^48) 9077915649 10 Manual.Count131072.C069229.packed 64 cuts69229 = true := by
 decide +kernel
def cuts69230 : List PrefixCut := [⟨64,174625122,174625232⟩]
theorem checked69230 : checkPrefixCuts (2^48) 9078046721 10 Manual.Count131072.C069230.packed 64 cuts69230 = true := by
 decide +kernel
def cuts69231 : List PrefixCut := [⟨5,14355612,14355621⟩,
⟨64,177196078,177196175⟩]
theorem checked69231 : checkPrefixCuts (2^48) 9078177793 10 Manual.Count131072.C069231.packed 64 cuts69231 = true := by
 decide +kernel
def pointBounds69231 : List (Nat × Nat × Nat) := [(9078188032,115678253783729,115678643209252)]
theorem point_links_checked69231 : (cuts69231.take 1).map (fun c => (9078177793-1+2*2^10*c.k,115678239428117+c.lower,115678628853631+c.upper)) = pointBounds69231 := by
 decide +kernel
def cuts69232 : List PrefixCut := [⟨64,178650752,178650859⟩]
theorem checked69232 : checkPrefixCuts (2^48) 9078308865 10 Manual.Count131072.C069232.packed 64 cuts69232 = true := by
 decide +kernel
def cuts69233 : List PrefixCut := [⟨16,44119700,44119727⟩,
⟨64,176880900,176881004⟩]
theorem checked69233 : checkPrefixCuts (2^48) 9078439937 10 Manual.Count131072.C069233.packed 64 cuts69233 = true := by
 decide +kernel
def pointBounds69233 : List (Nat × Nat × Nat) := [(9078472704,115678639394647,115679028820392)]
theorem point_links_checked69233 : (cuts69233.take 1).map (fun c => (9078439937-1+2*2^10*c.k,115678595274947+c.lower,115678984700665+c.upper)) = pointBounds69233 := by
 decide +kernel
def cuts69234 : List PrefixCut := [⟨64,176599320,176599423⟩]
theorem checked69234 : checkPrefixCuts (2^48) 9078571009 10 Manual.Count131072.C069234.packed 64 cuts69234 = true := by
 decide +kernel
def cuts69235 : List PrefixCut := [⟨27,74440065,74440105⟩,
⟨64,177216836,177216940⟩]
theorem checked69235 : checkPrefixCuts (2^48) 9078702081 10 Manual.Count131072.C069235.packed 64 cuts69235 = true := by
 decide +kernel
def pointBounds69235 : List (Nat × Nat × Nat) := [(9078757376,115679023195232,115679412621197)]
theorem point_links_checked69235 : (cuts69235.take 1).map (fun c => (9078702081-1+2*2^10*c.k,115678948755167+c.lower,115679338181092+c.upper)) = pointBounds69235 := by
 decide +kernel
def cuts69236 : List PrefixCut := [⟨64,178206387,178206485⟩]
theorem checked69236 : checkPrefixCuts (2^48) 9078833153 10 Manual.Count131072.C069236.packed 64 cuts69236 = true := by
 decide +kernel
def cuts69237 : List PrefixCut := [⟨38,104789605,104789662⟩,
⟨64,177025705,177025801⟩]
theorem checked69237 : checkPrefixCuts (2^48) 9078964225 10 Manual.Count131072.C069237.packed 64 cuts69237 = true := by
 decide +kernel
def pointBounds69237 : List (Nat × Nat × Nat) := [(9079042048,115679408967995,115679798394179)]
theorem point_links_checked69237 : (cuts69237.take 1).map (fun c => (9078964225-1+2*2^10*c.k,115679304178390+c.lower,115679693604517+c.upper)) = pointBounds69237 := by
 decide +kernel
def cuts69238 : List PrefixCut := [⟨64,174573963,174574065⟩]
theorem checked69238 : checkPrefixCuts (2^48) 9079095297 10 Manual.Count131072.C069238.packed 64 cuts69238 = true := by
 decide +kernel
def cuts69239 : List PrefixCut := [⟨49,135540341,135540424⟩,
⟨64,177609623,177609733⟩]
theorem checked69239 : checkPrefixCuts (2^48) 9079226369 10 Manual.Count131072.C069239.packed 64 cuts69239 = true := by
 decide +kernel
def pointBounds69239 : List (Nat × Nat × Nat) := [(9079326720,115679791318399,115680180744807)]
theorem point_links_checked69239 : (cuts69239.take 1).map (fun c => (9079226369-1+2*2^10*c.k,115679655778058+c.lower,115680045204383+c.upper)) = pointBounds69239 := by
 decide +kernel
def cuts69240 : List PrefixCut := [⟨64,176243002,176243110⟩]
theorem checked69240 : checkPrefixCuts (2^48) 9079357441 10 Manual.Count131072.C069240.packed 64 cuts69240 = true := by
 decide +kernel
def cuts69241 : List PrefixCut := [⟨60,165359187,165359284⟩,
⟨64,176674460,176674564⟩]
theorem checked69241 : checkPrefixCuts (2^48) 9079488513 10 Manual.Count131072.C069241.packed 64 cuts69241 = true := by
 decide +kernel
def pointBounds69241 : List (Nat × Nat × Nat) := [(9079611392,115680174989870,115680564416510)]
theorem point_links_checked69241 : (cuts69241.take 1).map (fun c => (9079488513-1+2*2^10*c.k,115680009630683+c.lower,115680399057226+c.upper)) = pointBounds69241 := by
 decide +kernel
def cuts69242 : List PrefixCut := [⟨64,176795922,176796027⟩]
theorem checked69242 : checkPrefixCuts (2^48) 9079619585 10 Manual.Count131072.C069242.packed 64 cuts69242 = true := by
 decide +kernel
def cuts69243 : List PrefixCut := [⟨64,178343380,178343486⟩]
theorem checked69243 : checkPrefixCuts (2^48) 9079750657 10 Manual.Count131072.C069243.packed 64 cuts69243 = true := by
 decide +kernel
def cuts69244 : List PrefixCut := [⟨7,20428880,20428892⟩,
⟨64,179673787,179673892⟩]
theorem checked69244 : checkPrefixCuts (2^48) 9079881729 10 Manual.Count131072.C069244.packed 64 cuts69244 = true := by
 decide +kernel
def pointBounds69244 : List (Nat × Nat × Nat) := [(9079896064,115680561873325,115680951300195)]
theorem point_links_checked69244 : (cuts69244.take 1).map (fun c => (9079881729-1+2*2^10*c.k,115680541444445+c.lower,115680930871303+c.upper)) = pointBounds69244 := by
 decide +kernel
def cuts69245 : List PrefixCut := [⟨64,179547182,179547293⟩]
theorem checked69245 : checkPrefixCuts (2^48) 9080012801 10 Manual.Count131072.C069245.packed 64 cuts69245 = true := by
 decide +kernel
def cuts69246 : List PrefixCut := [⟨18,49939201,49939232⟩,
⟨64,177250693,177250800⟩]
theorem checked69246 : checkPrefixCuts (2^48) 9080143873 10 Manual.Count131072.C069246.packed 64 cuts69246 = true := by
 decide +kernel
def pointBounds69246 : List (Nat × Nat × Nat) := [(9080180736,115680950604615,115681340031720)]
theorem point_links_checked69246 : (cuts69246.take 1).map (fun c => (9080143873-1+2*2^10*c.k,115680900665414+c.lower,115681290092488+c.upper)) = pointBounds69246 := by
 decide +kernel
def cuts69247 : List PrefixCut := [⟨64,179727987,179728091⟩]
theorem checked69247 : checkPrefixCuts (2^48) 9080274945 10 Manual.Count131072.C069247.packed 64 cuts69247 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000288
