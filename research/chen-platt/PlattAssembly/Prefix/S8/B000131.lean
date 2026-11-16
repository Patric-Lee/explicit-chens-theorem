import PlattAssemblyKernel
import PlattCertificates.Count131072.C074192
import PlattCertificates.Count131072.C074193
import PlattCertificates.Count131072.C074194
import PlattCertificates.Count131072.C074195
import PlattCertificates.Count131072.C074196
import PlattCertificates.Count131072.C074197
import PlattCertificates.Count131072.C074198
import PlattCertificates.Count131072.C074199
import PlattCertificates.Count131072.C074200
import PlattCertificates.Count131072.C074201
import PlattCertificates.Count131072.C074202
import PlattCertificates.Count131072.C074203
import PlattCertificates.Count131072.C074204
import PlattCertificates.Count131072.C074205
import PlattCertificates.Count131072.C074206
import PlattCertificates.Count131072.C074207
import PlattCertificates.Count131072.C074208
import PlattCertificates.Count131072.C074209
import PlattCertificates.Count131072.C074210
import PlattCertificates.Count131072.C074211
import PlattCertificates.Count131072.C074212
import PlattCertificates.Count131072.C074213
import PlattCertificates.Count131072.C074214
import PlattCertificates.Count131072.C074215
import PlattCertificates.Count131072.C074216
import PlattCertificates.Count131072.C074217
import PlattCertificates.Count131072.C074218
import PlattCertificates.Count131072.C074219
import PlattCertificates.Count131072.C074220
import PlattCertificates.Count131072.C074221
import PlattCertificates.Count131072.C074222
import PlattCertificates.Count131072.C074223
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000131
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74192 : List PrefixCut := [⟨64,162661588,162661686⟩]
theorem checked74192 : checkPrefixCuts (2^48) 9728425985 10 Manual.Count131072.C074192.packed 64 cuts74192 = true := by
 decide +kernel
def cuts74193 : List PrefixCut := [⟨64,165234397,165234501⟩]
theorem checked74193 : checkPrefixCuts (2^48) 9728557057 10 Manual.Count131072.C074193.packed 64 cuts74193 = true := by
 decide +kernel
def cuts74194 : List PrefixCut := [⟨14,35905131,35905152⟩,
⟨64,163959153,163959247⟩]
theorem checked74194 : checkPrefixCuts (2^48) 9728688129 10 Manual.Count131072.C074194.packed 64 cuts74194 = true := by
 decide +kernel
def pointBounds74194 : List (Nat × Nat × Nat) := [(9728716800,116526607635074,116526997563261)]
theorem point_links_checked74194 : (cuts74194.take 1).map (fun c => (9728688129-1+2*2^10*c.k,116526571729943+c.lower,116526961658109+c.upper)) = pointBounds74194 := by
 decide +kernel
def cuts74195 : List PrefixCut := [⟨64,167023740,167023831⟩]
theorem checked74195 : checkPrefixCuts (2^48) 9728819201 10 Manual.Count131072.C074195.packed 64 cuts74195 = true := by
 decide +kernel
def cuts74196 : List PrefixCut := [⟨35,89080320,89080377⟩,
⟨64,163578621,163578728⟩]
theorem checked74196 : checkPrefixCuts (2^48) 9728950273 10 Manual.Count131072.C074196.packed 64 cuts74196 = true := by
 decide +kernel
def pointBounds74196 : List (Nat × Nat × Nat) := [(9729021952,116526991793156,116527381721564)]
theorem point_links_checked74196 : (cuts74196.take 1).map (fun c => (9728950273-1+2*2^10*c.k,116526902712836+c.lower,116527292641187+c.upper)) = pointBounds74196 := by
 decide +kernel
def cuts74197 : List PrefixCut := [⟨64,165138698,165138796⟩]
theorem checked74197 : checkPrefixCuts (2^48) 9729081345 10 Manual.Count131072.C074197.packed 64 cuts74197 = true := by
 decide +kernel
def cuts74198 : List PrefixCut := [⟨56,143698949,143699040⟩,
⟨64,165281131,165281233⟩]
theorem checked74198 : checkPrefixCuts (2^48) 9729212417 10 Manual.Count131072.C074198.packed 64 cuts74198 = true := by
 decide +kernel
def pointBounds74198 : List (Nat × Nat × Nat) := [(9729327104,116527375129104,116527765057751)]
theorem point_links_checked74198 : (cuts74198.take 1).map (fun c => (9729212417-1+2*2^10*c.k,116527231430155+c.lower,116527621358711+c.upper)) = pointBounds74198 := by
 decide +kernel
def cuts74199 : List PrefixCut := [⟨64,164873875,164873974⟩]
theorem checked74199 : checkPrefixCuts (2^48) 9729343489 10 Manual.Count131072.C074199.packed 64 cuts74199 = true := by
 decide +kernel
def cuts74200 : List PrefixCut := [⟨64,162354750,162354844⟩]
theorem checked74200 : checkPrefixCuts (2^48) 9729474561 10 Manual.Count131072.C074200.packed 64 cuts74200 = true := by
 decide +kernel
def cuts74201 : List PrefixCut := [⟨13,33355937,33355957⟩,
⟨64,162468283,162468383⟩]
theorem checked74201 : checkPrefixCuts (2^48) 9729605633 10 Manual.Count131072.C074201.packed 64 cuts74201 = true := by
 decide +kernel
def pointBounds74201 : List (Nat × Nat × Nat) := [(9729632256,116527757295848,116528147224719)]
theorem point_links_checked74201 : (cuts74201.take 1).map (fun c => (9729605633-1+2*2^10*c.k,116527723939911+c.lower,116528113868762+c.upper)) = pointBounds74201 := by
 decide +kernel
def cuts74202 : List PrefixCut := [⟨64,165879740,165879834⟩]
theorem checked74202 : checkPrefixCuts (2^48) 9729736705 10 Manual.Count131072.C074202.packed 64 cuts74202 = true := by
 decide +kernel
def cuts74203 : List PrefixCut := [⟨34,85976542,85976593⟩,
⟨64,164315333,164315434⟩]
theorem checked74203 : checkPrefixCuts (2^48) 9729867777 10 Manual.Count131072.C074203.packed 64 cuts74203 = true := by
 decide +kernel
def pointBounds74203 : List (Nat × Nat × Nat) := [(9729937408,116528138264476,116528528193572)]
theorem point_links_checked74203 : (cuts74203.take 1).map (fun c => (9729867777-1+2*2^10*c.k,116528052287934+c.lower,116528442216979+c.upper)) = pointBounds74203 := by
 decide +kernel
def cuts74204 : List PrefixCut := [⟨64,166453829,166453925⟩]
theorem checked74204 : checkPrefixCuts (2^48) 9729998849 10 Manual.Count131072.C074204.packed 64 cuts74204 = true := by
 decide +kernel
def cuts74205 : List PrefixCut := [⟨55,141602596,141602682⟩,
⟨64,165091979,165092078⟩]
theorem checked74205 : checkPrefixCuts (2^48) 9730129921 10 Manual.Count131072.C074205.packed 64 cuts74205 = true := by
 decide +kernel
def pointBounds74205 : List (Nat × Nat × Nat) := [(9730242560,116528524659692,116528914589020)]
theorem point_links_checked74205 : (cuts74205.take 1).map (fun c => (9730129921-1+2*2^10*c.k,116528383057096+c.lower,116528772986338+c.upper)) = pointBounds74205 := by
 decide +kernel
def cuts74206 : List PrefixCut := [⟨64,163469803,163469899⟩]
theorem checked74206 : checkPrefixCuts (2^48) 9730260993 10 Manual.Count131072.C074206.packed 64 cuts74206 = true := by
 decide +kernel
def cuts74207 : List PrefixCut := [⟨64,164856111,164856208⟩]
theorem checked74207 : checkPrefixCuts (2^48) 9730392065 10 Manual.Count131072.C074207.packed 64 cuts74207 = true := by
 decide +kernel
def cuts74208 : List PrefixCut := [⟨12,30836149,30836167⟩,
⟨64,166473792,166473892⟩]
theorem checked74208 : checkPrefixCuts (2^48) 9730523137 10 Manual.Count131072.C074208.packed 64 cuts74208 = true := by
 decide +kernel
def pointBounds74208 : List (Nat × Nat × Nat) := [(9730547712,116528907311138,116529297240690)]
theorem point_links_checked74208 : (cuts74208.take 1).map (fun c => (9730523137-1+2*2^10*c.k,116528876474989+c.lower,116529266404523+c.upper)) = pointBounds74208 := by
 decide +kernel
def cuts74209 : List PrefixCut := [⟨64,167281501,167281607⟩]
theorem checked74209 : checkPrefixCuts (2^48) 9730654209 10 Manual.Count131072.C074209.packed 64 cuts74209 = true := by
 decide +kernel
def cuts74210 : List PrefixCut := [⟨33,84753552,84753593⟩,
⟨64,164097381,164097470⟩]
theorem checked74210 : checkPrefixCuts (2^48) 9730785281 10 Manual.Count131072.C074210.packed 64 cuts74210 = true := by
 decide +kernel
def pointBounds74210 : List (Nat × Nat × Nat) := [(9730852864,116529294983834,116529684913615)]
theorem point_links_checked74210 : (cuts74210.take 1).map (fun c => (9730785281-1+2*2^10*c.k,116529210230282+c.lower,116529600160022+c.upper)) = pointBounds74210 := by
 decide +kernel
def cuts74211 : List PrefixCut := [⟨64,162967063,162967166⟩]
theorem checked74211 : checkPrefixCuts (2^48) 9730916353 10 Manual.Count131072.C074211.packed 64 cuts74211 = true := by
 decide +kernel
def cuts74212 : List PrefixCut := [⟨54,138320701,138320782⟩,
⟨64,163369826,163369924⟩]
theorem checked74212 : checkPrefixCuts (2^48) 9731047425 10 Manual.Count131072.C074212.packed 64 cuts74212 = true := by
 decide +kernel
def pointBounds74212 : List (Nat × Nat × Nat) := [(9731158016,116529675615427,116530065545440)]
theorem point_links_checked74212 : (cuts74212.take 1).map (fun c => (9731047425-1+2*2^10*c.k,116529537294726+c.lower,116529927224658+c.upper)) = pointBounds74212 := by
 decide +kernel
def cuts74213 : List PrefixCut := [⟨64,166115485,166115592⟩]
theorem checked74213 : checkPrefixCuts (2^48) 9731178497 10 Manual.Count131072.C074213.packed 64 cuts74213 = true := by
 decide +kernel
def cuts74214 : List PrefixCut := [⟨64,163365436,163365532⟩]
theorem checked74214 : checkPrefixCuts (2^48) 9731309569 10 Manual.Count131072.C074214.packed 64 cuts74214 = true := by
 decide +kernel
def cuts74215 : List PrefixCut := [⟨11,28692851,28692867⟩,
⟨64,165821769,165821873⟩]
theorem checked74215 : checkPrefixCuts (2^48) 9731440641 10 Manual.Count131072.C074215.packed 64 cuts74215 = true := by
 decide +kernel
def pointBounds74215 : List (Nat × Nat × Nat) := [(9731463168,116530058838324,116530448768573)]
theorem point_links_checked74215 : (cuts74215.take 1).map (fun c => (9731440641-1+2*2^10*c.k,116530030145473+c.lower,116530420075706+c.upper)) = pointBounds74215 := by
 decide +kernel
def cuts74216 : List PrefixCut := [⟨64,165848453,165848558⟩]
theorem checked74216 : checkPrefixCuts (2^48) 9731571713 10 Manual.Count131072.C074216.packed 64 cuts74216 = true := by
 decide +kernel
def cuts74217 : List PrefixCut := [⟨32,81853222,81853278⟩,
⟨64,165180981,165181088⟩]
theorem checked74217 : checkPrefixCuts (2^48) 9731702785 10 Manual.Count131072.C074217.packed 64 cuts74217 = true := by
 decide +kernel
def pointBounds74217 : List (Nat × Nat × Nat) := [(9731768320,116530443668917,116530833599415)]
theorem point_links_checked74217 : (cuts74217.take 1).map (fun c => (9731702785-1+2*2^10*c.k,116530361815695+c.lower,116530751746137+c.upper)) = pointBounds74217 := by
 decide +kernel
def cuts74218 : List PrefixCut := [⟨64,166277838,166277942⟩]
theorem checked74218 : checkPrefixCuts (2^48) 9731833857 10 Manual.Count131072.C074218.packed 64 cuts74218 = true := by
 decide +kernel
def cuts74219 : List PrefixCut := [⟨53,136861545,136861624⟩,
⟨64,165465763,165465857⟩]
theorem checked74219 : checkPrefixCuts (2^48) 9731964929 10 Manual.Count131072.C074219.packed 64 cuts74219 = true := by
 decide +kernel
def pointBounds74219 : List (Nat × Nat × Nat) := [(9732073472,116530830136059,116531220066791)]
theorem point_links_checked74219 : (cuts74219.take 1).map (fun c => (9731964929-1+2*2^10*c.k,116530693274514+c.lower,116531083205167+c.upper)) = pointBounds74219 := by
 decide +kernel
def cuts74220 : List PrefixCut := [⟨64,166533644,166533743⟩]
theorem checked74220 : checkPrefixCuts (2^48) 9732096001 10 Manual.Count131072.C074220.packed 64 cuts74220 = true := by
 decide +kernel
def cuts74221 : List PrefixCut := [⟨64,164796117,164796210⟩]
theorem checked74221 : checkPrefixCuts (2^48) 9732227073 10 Manual.Count131072.C074221.packed 64 cuts74221 = true := by
 decide +kernel
def cuts74222 : List PrefixCut := [⟨10,26665643,26665657⟩,
⟨64,165603688,165603785⟩]
theorem checked74222 : checkPrefixCuts (2^48) 9732358145 10 Manual.Count131072.C074222.packed 64 cuts74222 = true := by
 decide +kernel
def pointBounds74222 : List (Nat × Nat × Nat) := [(9732378624,116531216735681,116531606666634)]
theorem point_links_checked74222 : (cuts74222.take 1).map (fun c => (9732358145-1+2*2^10*c.k,116531190070038+c.lower,116531580000977+c.upper)) = pointBounds74222 := by
 decide +kernel
def cuts74223 : List PrefixCut := [⟨64,163663742,163663841⟩]
theorem checked74223 : checkPrefixCuts (2^48) 9732489217 10 Manual.Count131072.C074223.packed 64 cuts74223 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000131
