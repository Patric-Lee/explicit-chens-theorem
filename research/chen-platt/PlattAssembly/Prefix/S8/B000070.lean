import PlattAssemblyKernel
import PlattCertificates.Count131072.C072240
import PlattCertificates.Count131072.C072241
import PlattCertificates.Count131072.C072242
import PlattCertificates.Count131072.C072243
import PlattCertificates.Count131072.C072244
import PlattCertificates.Count131072.C072245
import PlattCertificates.Count131072.C072246
import PlattCertificates.Count131072.C072247
import PlattCertificates.Count131072.C072248
import PlattCertificates.Count131072.C072249
import PlattCertificates.Count131072.C072250
import PlattCertificates.Count131072.C072251
import PlattCertificates.Count131072.C072252
import PlattCertificates.Count131072.C072253
import PlattCertificates.Count131072.C072254
import PlattCertificates.Count131072.C072255
import PlattCertificates.Count131072.C072256
import PlattCertificates.Count131072.C072257
import PlattCertificates.Count131072.C072258
import PlattCertificates.Count131072.C072259
import PlattCertificates.Count131072.C072260
import PlattCertificates.Count131072.C072261
import PlattCertificates.Count131072.C072262
import PlattCertificates.Count131072.C072263
import PlattCertificates.Count131072.C072264
import PlattCertificates.Count131072.C072265
import PlattCertificates.Count131072.C072266
import PlattCertificates.Count131072.C072267
import PlattCertificates.Count131072.C072268
import PlattCertificates.Count131072.C072269
import PlattCertificates.Count131072.C072270
import PlattCertificates.Count131072.C072271
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000070
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72240 : List PrefixCut := [⟨64,171809341,171809438⟩]
theorem checked72240 : checkPrefixCuts (2^48) 9472573441 10 Manual.Count131072.C072240.packed 64 cuts72240 = true := by
 decide +kernel
def cuts72241 : List PrefixCut := [⟨64,169875540,169875636⟩]
theorem checked72241 : checkPrefixCuts (2^48) 9472704513 10 Manual.Count131072.C072241.packed 64 cuts72241 = true := by
 decide +kernel
def cuts72242 : List PrefixCut := [⟨5,12420403,12420411⟩,
⟨64,168892621,168892725⟩]
theorem checked72242 : checkPrefixCuts (2^48) 9472835585 10 Manual.Count131072.C072242.packed 64 cuts72242 = true := by
 decide +kernel
def pointBounds72242 : List (Nat × Nat × Nat) := [(9472845824,116200173000769,116200562734351)]
theorem point_links_checked72242 : (cuts72242.take 1).map (fun c => (9472835585-1+2*2^10*c.k,116200160580366+c.lower,116200550313940+c.upper)) = pointBounds72242 := by
 decide +kernel
def cuts72243 : List PrefixCut := [⟨64,168622873,168622980⟩]
theorem checked72243 : checkPrefixCuts (2^48) 9472966657 10 Manual.Count131072.C072243.packed 64 cuts72243 = true := by
 decide +kernel
def cuts72244 : List PrefixCut := [⟨22,58772329,58772364⟩,
⟨64,169452516,169452621⟩]
theorem checked72244 : checkPrefixCuts (2^48) 9473097729 10 Manual.Count131072.C072244.packed 64 cuts72244 = true := by
 decide +kernel
def pointBounds72244 : List (Nat × Nat × Nat) := [(9473142784,116200556868189,116200946602009)]
theorem point_links_checked72244 : (cuts72244.take 1).map (fun c => (9473097729-1+2*2^10*c.k,116200498095860+c.lower,116200887829645+c.upper)) = pointBounds72244 := by
 decide +kernel
def cuts72245 : List PrefixCut := [⟨64,169479892,169479994⟩]
theorem checked72245 : checkPrefixCuts (2^48) 9473228801 10 Manual.Count131072.C072245.packed 64 cuts72245 = true := by
 decide +kernel
def cuts72246 : List PrefixCut := [⟨39,103279374,103279431⟩,
⟨64,169269564,169269655⟩]
theorem checked72246 : checkPrefixCuts (2^48) 9473359873 10 Manual.Count131072.C072246.packed 64 cuts72246 = true := by
 decide +kernel
def pointBounds72246 : List (Nat × Nat × Nat) := [(9473439744,116200940307642,116201330041691)]
theorem point_links_checked72246 : (cuts72246.take 1).map (fun c => (9473359873-1+2*2^10*c.k,116200837028268+c.lower,116201226762260+c.upper)) = pointBounds72246 := by
 decide +kernel
def cuts72247 : List PrefixCut := [⟨64,170633949,170634047⟩]
theorem checked72247 : checkPrefixCuts (2^48) 9473490945 10 Manual.Count131072.C072247.packed 64 cuts72247 = true := by
 decide +kernel
def cuts72248 : List PrefixCut := [⟨56,145198904,145198989⟩,
⟨64,166501726,166501822⟩]
theorem checked72248 : checkPrefixCuts (2^48) 9473622017 10 Manual.Count131072.C072248.packed 64 cuts72248 = true := by
 decide +kernel
def pointBounds72248 : List (Nat × Nat × Nat) := [(9473736704,116201322130685,116201711864951)]
theorem point_links_checked72248 : (cuts72248.take 1).map (fun c => (9473622017-1+2*2^10*c.k,116201176931781+c.lower,116201566665962+c.upper)) = pointBounds72248 := by
 decide +kernel
def cuts72249 : List PrefixCut := [⟨64,169262525,169262628⟩]
theorem checked72249 : checkPrefixCuts (2^48) 9473753089 10 Manual.Count131072.C072249.packed 64 cuts72249 = true := by
 decide +kernel
def cuts72250 : List PrefixCut := [⟨64,167744954,167745061⟩]
theorem checked72250 : checkPrefixCuts (2^48) 9473884161 10 Manual.Count131072.C072250.packed 64 cuts72250 = true := by
 decide +kernel
def cuts72251 : List PrefixCut := [⟨9,23797849,23797861⟩,
⟨64,172169424,172169525⟩]
theorem checked72251 : checkPrefixCuts (2^48) 9474015233 10 Manual.Count131072.C072251.packed 64 cuts72251 = true := by
 decide +kernel
def pointBounds72251 : List (Nat × Nat × Nat) := [(9474033664,116201704238835,116202093973334)]
theorem point_links_checked72251 : (cuts72251.take 1).map (fun c => (9474015233-1+2*2^10*c.k,116201680440986+c.lower,116202070175473+c.upper)) = pointBounds72251 := by
 decide +kernel
def cuts72252 : List PrefixCut := [⟨64,168780144,168780242⟩]
theorem checked72252 : checkPrefixCuts (2^48) 9474146305 10 Manual.Count131072.C072252.packed 64 cuts72252 = true := by
 decide +kernel
def cuts72253 : List PrefixCut := [⟨26,67618354,67618394⟩,
⟨64,169045189,169045289⟩]
theorem checked72253 : checkPrefixCuts (2^48) 9474277377 10 Manual.Count131072.C072253.packed 64 cuts72253 = true := by
 decide +kernel
def pointBounds72253 : List (Nat × Nat × Nat) := [(9474330624,116202089008908,116202478743634)]
theorem point_links_checked72253 : (cuts72253.take 1).map (fun c => (9474277377-1+2*2^10*c.k,116202021390554+c.lower,116202411125240+c.upper)) = pointBounds72253 := by
 decide +kernel
def cuts72254 : List PrefixCut := [⟨64,171627521,171627624⟩]
theorem checked72254 : checkPrefixCuts (2^48) 9474408449 10 Manual.Count131072.C072254.packed 64 cuts72254 = true := by
 decide +kernel
def cuts72255 : List PrefixCut := [⟨43,114733915,114733984⟩,
⟨64,170258565,170258664⟩]
theorem checked72255 : checkPrefixCuts (2^48) 9474539521 10 Manual.Count131072.C072255.packed 64 cuts72255 = true := by
 decide +kernel
def pointBounds72255 : List (Nat × Nat × Nat) := [(9474627584,116202476797179,116202866532137)]
theorem point_links_checked72255 : (cuts72255.take 1).map (fun c => (9474539521-1+2*2^10*c.k,116202362063264+c.lower,116202751798153+c.upper)) = pointBounds72255 := by
 decide +kernel
def cuts72256 : List PrefixCut := [⟨64,170404742,170404844⟩]
theorem checked72256 : checkPrefixCuts (2^48) 9474670593 10 Manual.Count131072.C072256.packed 64 cuts72256 = true := by
 decide +kernel
def cuts72257 : List PrefixCut := [⟨60,157360846,157360943⟩,
⟨64,167461341,167461443⟩]
theorem checked72257 : checkPrefixCuts (2^48) 9474801665 10 Manual.Count131072.C072257.packed 64 cuts72257 = true := by
 decide +kernel
def pointBounds72257 : List (Nat × Nat × Nat) := [(9474924544,116202860087417,116203249822604)]
theorem point_links_checked72257 : (cuts72257.take 1).map (fun c => (9474801665-1+2*2^10*c.k,116202702726571+c.lower,116203092461661+c.upper)) = pointBounds72257 := by
 decide +kernel
def cuts72258 : List PrefixCut := [⟨64,168350228,168350332⟩]
theorem checked72258 : checkPrefixCuts (2^48) 9474932737 10 Manual.Count131072.C072258.packed 64 cuts72258 = true := by
 decide +kernel
def cuts72259 : List PrefixCut := [⟨64,169922365,169922467⟩]
theorem checked72259 : checkPrefixCuts (2^48) 9475063809 10 Manual.Count131072.C072259.packed 64 cuts72259 = true := by
 decide +kernel
def cuts72260 : List PrefixCut := [⟨13,32974170,32974189⟩,
⟨64,168969404,168969505⟩]
theorem checked72260 : checkPrefixCuts (2^48) 9475194881 10 Manual.Count131072.C072260.packed 64 cuts72260 = true := by
 decide +kernel
def pointBounds72260 : List (Nat × Nat × Nat) := [(9475221504,116203241434675,116203631170092)]
theorem point_links_checked72260 : (cuts72260.take 1).map (fun c => (9475194881-1+2*2^10*c.k,116203208460505+c.lower,116203598195903+c.upper)) = pointBounds72260 := by
 decide +kernel
def cuts72261 : List PrefixCut := [⟨64,167036194,167036293⟩]
theorem checked72261 : checkPrefixCuts (2^48) 9475325953 10 Manual.Count131072.C072261.packed 64 cuts72261 = true := by
 decide +kernel
def cuts72262 : List PrefixCut := [⟨30,81215070,81215115⟩,
⟨64,172262059,172262153⟩]
theorem checked72262 : checkPrefixCuts (2^48) 9475457025 10 Manual.Count131072.C072262.packed 64 cuts72262 = true := by
 decide +kernel
def pointBounds72262 : List (Nat × Nat × Nat) := [(9475518464,116203625681173,116204015416816)]
theorem point_links_checked72262 : (cuts72262.take 1).map (fun c => (9475457025-1+2*2^10*c.k,116203544466103+c.lower,116203934201701+c.upper)) = pointBounds72262 := by
 decide +kernel
def cuts72263 : List PrefixCut := [⟨64,169259451,169259546⟩]
theorem checked72263 : checkPrefixCuts (2^48) 9475588097 10 Manual.Count131072.C072263.packed 64 cuts72263 = true := by
 decide +kernel
def cuts72264 : List PrefixCut := [⟨47,122264572,122264650⟩,
⟨64,167712458,167712566⟩]
theorem checked72264 : checkPrefixCuts (2^48) 9475719169 10 Manual.Count131072.C072264.packed 64 cuts72264 = true := by
 decide +kernel
def pointBounds72264 : List (Nat × Nat × Nat) := [(9475815424,116204008252185,116204397988050)]
theorem point_links_checked72264 : (cuts72264.take 1).map (fun c => (9475719169-1+2*2^10*c.k,116203885987613+c.lower,116204275723400+c.upper)) = pointBounds72264 := by
 decide +kernel
def cuts72265 : List PrefixCut := [⟨64,169700346,169700445⟩]
theorem checked72265 : checkPrefixCuts (2^48) 9475850241 10 Manual.Count131072.C072265.packed 64 cuts72265 = true := by
 decide +kernel
def cuts72266 : List PrefixCut := [⟨64,170648514,170648611⟩]
theorem checked72266 : checkPrefixCuts (2^48) 9475981313 10 Manual.Count131072.C072266.packed 64 cuts72266 = true := by
 decide +kernel
def pointBounds72266 : List (Nat × Nat × Nat) := [(9476112384,116204394048931,116204783785022)]
theorem point_links_checked72266 : (cuts72266.take 1).map (fun c => (9475981313-1+2*2^10*c.k,116204223400417+c.lower,116204613136411+c.upper)) = pointBounds72266 := by
 decide +kernel
def cuts72267 : List PrefixCut := [⟨64,167646095,167646197⟩]
theorem checked72267 : checkPrefixCuts (2^48) 9476112385 10 Manual.Count131072.C072267.packed 64 cuts72267 = true := by
 decide +kernel
def cuts72268 : List PrefixCut := [⟨64,166128935,166129040⟩]
theorem checked72268 : checkPrefixCuts (2^48) 9476243457 10 Manual.Count131072.C072268.packed 64 cuts72268 = true := by
 decide +kernel
def cuts72269 : List PrefixCut := [⟨17,44019473,44019500⟩,
⟨64,168681053,168681156⟩]
theorem checked72269 : checkPrefixCuts (2^48) 9476374529 10 Manual.Count131072.C072269.packed 64 cuts72269 = true := by
 decide +kernel
def pointBounds72269 : List (Nat × Nat × Nat) := [(9476409344,116204771843434,116205161579759)]
theorem point_links_checked72269 : (cuts72269.take 1).map (fun c => (9476374529-1+2*2^10*c.k,116204727823961+c.lower,116205117560259+c.upper)) = pointBounds72269 := by
 decide +kernel
def cuts72270 : List PrefixCut := [⟨64,170015325,170015431⟩]
theorem checked72270 : checkPrefixCuts (2^48) 9476505601 10 Manual.Count131072.C072270.packed 64 cuts72270 = true := by
 decide +kernel
def cuts72271 : List PrefixCut := [⟨34,90412505,90412556⟩,
⟨64,169508045,169508144⟩]
theorem checked72271 : checkPrefixCuts (2^48) 9476636673 10 Manual.Count131072.C072271.packed 64 cuts72271 = true := by
 decide +kernel
def pointBounds72271 : List (Nat × Nat × Nat) := [(9476706304,116205156932844,116205546669402)]
theorem point_links_checked72271 : (cuts72271.take 1).map (fun c => (9476636673-1+2*2^10*c.k,116205066520339+c.lower,116205456256846+c.upper)) = pointBounds72271 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000070
