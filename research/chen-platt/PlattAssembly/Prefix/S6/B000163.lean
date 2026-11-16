import PlattAssemblyKernel
import PlattCertificates.Count131072.C055216
import PlattCertificates.Count131072.C055217
import PlattCertificates.Count131072.C055218
import PlattCertificates.Count131072.C055219
import PlattCertificates.Count131072.C055220
import PlattCertificates.Count131072.C055221
import PlattCertificates.Count131072.C055222
import PlattCertificates.Count131072.C055223
import PlattCertificates.Count131072.C055224
import PlattCertificates.Count131072.C055225
import PlattCertificates.Count131072.C055226
import PlattCertificates.Count131072.C055227
import PlattCertificates.Count131072.C055228
import PlattCertificates.Count131072.C055229
import PlattCertificates.Count131072.C055230
import PlattCertificates.Count131072.C055231
import PlattCertificates.Count131072.C055232
import PlattCertificates.Count131072.C055233
import PlattCertificates.Count131072.C055234
import PlattCertificates.Count131072.C055235
import PlattCertificates.Count131072.C055236
import PlattCertificates.Count131072.C055237
import PlattCertificates.Count131072.C055238
import PlattCertificates.Count131072.C055239
import PlattCertificates.Count131072.C055240
import PlattCertificates.Count131072.C055241
import PlattCertificates.Count131072.C055242
import PlattCertificates.Count131072.C055243
import PlattCertificates.Count131072.C055244
import PlattCertificates.Count131072.C055245
import PlattCertificates.Count131072.C055246
import PlattCertificates.Count131072.C055247
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000163
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts55216 : List PrefixCut := [⟨64,223002553,223002682⟩]
theorem checked55216 : checkPrefixCuts (2^48) 7241203713 10 Manual.Count131072.C055216.packed 64 cuts55216 = true := by
 decide +kernel
def cuts55217 : List PrefixCut := [⟨27,93522259,93522313⟩,
⟨64,224047997,224048126⟩]
theorem checked55217 : checkPrefixCuts (2^48) 7241334785 10 Manual.Count131072.C055217.packed 64 cuts55217 = true := by
 decide +kernel
def pointBounds55217 : List (Nat × Nat × Nat) := [(7241390080,112889372781326,112889760603712)]
theorem point_links_checked55217 : (cuts55217.take 1).map (fun c => (7241334785-1+2*2^10*c.k,112889279259067+c.lower,112889667081399+c.upper)) = pointBounds55217 := by
 decide +kernel
def cuts55218 : List PrefixCut := [⟨64,224082824,224082952⟩]
theorem checked55218 : checkPrefixCuts (2^48) 7241465857 10 Manual.Count131072.C055218.packed 64 cuts55218 = true := by
 decide +kernel
def cuts55219 : List PrefixCut := [⟨10,35370900,35370920⟩,
⟨64,226799565,226799692⟩]
theorem checked55219 : checkPrefixCuts (2^48) 7241596929 10 Manual.Count131072.C055219.packed 64 cuts55219 = true := by
 decide +kernel
def pointBounds55219 : List (Nat × Nat × Nat) := [(7241617408,112889762760788,112890150583397)]
theorem point_links_checked55219 : (cuts55219.take 1).map (fun c => (7241596929-1+2*2^10*c.k,112889727389888+c.lower,112890115212477+c.upper)) = pointBounds55219 := by
 decide +kernel
def cuts55220 : List PrefixCut := [⟨57,199704587,199704702⟩,
⟨64,225085264,225085394⟩]
theorem checked55220 : checkPrefixCuts (2^48) 7241728001 10 Manual.Count131072.C055220.packed 64 cuts55220 = true := by
 decide +kernel
def pointBounds55220 : List (Nat × Nat × Nat) := [(7241844736,112890153894040,112890541716871)]
theorem point_links_checked55220 : (cuts55220.take 1).map (fun c => (7241728001-1+2*2^10*c.k,112889954189453+c.lower,112890342012169+c.upper)) = pointBounds55220 := by
 decide +kernel
def cuts55221 : List PrefixCut := [⟨64,225314402,225314529⟩]
theorem checked55221 : checkPrefixCuts (2^48) 7241859073 10 Manual.Count131072.C055221.packed 64 cuts55221 = true := by
 decide +kernel
def cuts55222 : List PrefixCut := [⟨40,138832365,138832444⟩,
⟨64,225349179,225349307⟩]
theorem checked55222 : checkPrefixCuts (2^48) 7241990145 10 Manual.Count131072.C055222.packed 64 cuts55222 = true := by
 decide +kernel
def pointBounds55222 : List (Nat × Nat × Nat) := [(7242072064,112890543421484,112890931244536)]
theorem point_links_checked55222 : (cuts55222.take 1).map (fun c => (7241990145-1+2*2^10*c.k,112890404589119+c.lower,112890792412092+c.upper)) = pointBounds55222 := by
 decide +kernel
def cuts55223 : List PrefixCut := [⟨64,222779973,222780103⟩]
theorem checked55223 : checkPrefixCuts (2^48) 7242121217 10 Manual.Count131072.C055223.packed 64 cuts55223 = true := by
 decide +kernel
def cuts55224 : List PrefixCut := [⟨23,79829799,79829845⟩,
⟨64,224019601,224019730⟩]
theorem checked55224 : checkPrefixCuts (2^48) 7242252289 10 Manual.Count131072.C055224.packed 64 cuts55224 = true := by
 decide +kernel
def pointBounds55224 : List (Nat × Nat × Nat) := [(7242299392,112890932548070,112891320371347)]
theorem point_links_checked55224 : (cuts55224.take 1).map (fun c => (7242252289-1+2*2^10*c.k,112890852718271+c.lower,112891240541502+c.upper)) = pointBounds55224 := by
 decide +kernel
def cuts55225 : List PrefixCut := [⟨64,225881049,225881177⟩]
theorem checked55225 : checkPrefixCuts (2^48) 7242383361 10 Manual.Count131072.C055225.packed 64 cuts55225 = true := by
 decide +kernel
def cuts55226 : List PrefixCut := [⟨6,21569641,21569653⟩,
⟨64,225449469,225449596⟩]
theorem checked55226 : checkPrefixCuts (2^48) 7242514433 10 Manual.Count131072.C055226.packed 64 cuts55226 = true := by
 decide +kernel
def pointBounds55226 : List (Nat × Nat × Nat) := [(7242526720,112891324188562,112891712012062)]
theorem point_links_checked55226 : (cuts55226.take 1).map (fun c => (7242514433-1+2*2^10*c.k,112891302618921+c.lower,112891690442409+c.upper)) = pointBounds55226 := by
 decide +kernel
def cuts55227 : List PrefixCut := [⟨53,183395709,183395811⟩,
⟨64,221403628,221403751⟩]
theorem checked55227 : checkPrefixCuts (2^48) 7242645505 10 Manual.Count131072.C055227.packed 64 cuts55227 = true := by
 decide +kernel
def pointBounds55227 : List (Nat × Nat × Nat) := [(7242754048,112891711464099,112892099287816)]
theorem point_links_checked55227 : (cuts55227.take 1).map (fun c => (7242645505-1+2*2^10*c.k,112891528068390+c.lower,112891915892005+c.upper)) = pointBounds55227 := by
 decide +kernel
def cuts55228 : List PrefixCut := [⟨64,225596757,225596887⟩]
theorem checked55228 : checkPrefixCuts (2^48) 7242776577 10 Manual.Count131072.C055228.packed 64 cuts55228 = true := by
 decide +kernel
def cuts55229 : List PrefixCut := [⟨36,127389453,127389525⟩,
⟨64,227263745,227263872⟩]
theorem checked55229 : checkPrefixCuts (2^48) 7242907649 10 Manual.Count131072.C055229.packed 64 cuts55229 = true := by
 decide +kernel
def pointBounds55229 : List (Nat × Nat × Nat) := [(7242981376,112892102458228,112892490282168)]
theorem point_links_checked55229 : (cuts55229.take 1).map (fun c => (7242907649-1+2*2^10*c.k,112891975068775+c.lower,112892362892643+c.upper)) = pointBounds55229 := by
 decide +kernel
def cuts55230 : List PrefixCut := [⟨64,225705170,225705299⟩]
theorem checked55230 : checkPrefixCuts (2^48) 7243038721 10 Manual.Count131072.C055230.packed 64 cuts55230 = true := by
 decide +kernel
def cuts55231 : List PrefixCut := [⟨19,66918004,66918041⟩,
⟨64,225429080,225429207⟩]
theorem checked55231 : checkPrefixCuts (2^48) 7243169793 10 Manual.Count131072.C055231.packed 64 cuts55231 = true := by
 decide +kernel
def pointBounds55231 : List (Nat × Nat × Nat) := [(7243208704,112892494955694,112892882779855)]
theorem point_links_checked55231 : (cuts55231.take 1).map (fun c => (7243169793-1+2*2^10*c.k,112892428037690+c.lower,112892815861814+c.upper)) = pointBounds55231 := by
 decide +kernel
def cuts55232 : List PrefixCut := [⟨64,223831765,223831892⟩]
theorem checked55232 : checkPrefixCuts (2^48) 7243300865 10 Manual.Count131072.C055232.packed 64 cuts55232 = true := by
 decide +kernel
def cuts55233 : List PrefixCut := [⟨2,7344411,7344415⟩,
⟨64,223866579,223866705⟩]
theorem checked55233 : checkPrefixCuts (2^48) 7243431937 10 Manual.Count131072.C055233.packed 64 cuts55233 = true := by
 decide +kernel
def pointBounds55233 : List (Nat × Nat × Nat) := [(7243436032,112892884642946,112893272467328)]
theorem point_links_checked55233 : (cuts55233.take 1).map (fun c => (7243431937-1+2*2^10*c.k,112892877298535+c.lower,112893265122913+c.upper)) = pointBounds55233 := by
 decide +kernel
def cuts55234 : List PrefixCut := [⟨49,170627032,170627130⟩,
⟨64,222308174,222308302⟩]
theorem checked55234 : checkPrefixCuts (2^48) 7243563009 10 Manual.Count131072.C055234.packed 64 cuts55234 = true := by
 decide +kernel
def pointBounds55234 : List (Nat × Nat × Nat) := [(7243663360,112893271792146,112893659616748)]
theorem point_links_checked55234 : (cuts55234.take 1).map (fun c => (7243563009-1+2*2^10*c.k,112893101165114+c.lower,112893488989618+c.upper)) = pointBounds55234 := by
 decide +kernel
def cuts55235 : List PrefixCut := [⟨64,223897319,223897444⟩]
theorem checked55235 : checkPrefixCuts (2^48) 7243694081 10 Manual.Count131072.C055235.packed 64 cuts55235 = true := by
 decide +kernel
def cuts55236 : List PrefixCut := [⟨32,114511709,114511772⟩,
⟨64,227351540,227351666⟩]
theorem checked55236 : checkPrefixCuts (2^48) 7243825153 10 Manual.Count131072.C055236.packed 64 cuts55236 = true := by
 decide +kernel
def pointBounds55236 : List (Nat × Nat × Nat) := [(7243890688,112893661882316,112894049707136)]
theorem point_links_checked55236 : (cuts55236.take 1).map (fun c => (7243825153-1+2*2^10*c.k,112893547370607+c.lower,112893935195364+c.upper)) = pointBounds55236 := by
 decide +kernel
def cuts55237 : List PrefixCut := [⟨64,226181726,226181855⟩]
theorem checked55237 : checkPrefixCuts (2^48) 7243956225 10 Manual.Count131072.C055237.packed 64 cuts55237 = true := by
 decide +kernel
def cuts55238 : List PrefixCut := [⟨15,52610660,52610690⟩,
⟨64,224973112,224973239⟩]
theorem checked55238 : checkPrefixCuts (2^48) 7244087297 10 Manual.Count131072.C055238.packed 64 cuts55238 = true := by
 decide +kernel
def pointBounds55238 : List (Nat × Nat × Nat) := [(7244118016,112894053514533,112894441339575)]
theorem point_links_checked55238 : (cuts55238.take 1).map (fun c => (7244087297-1+2*2^10*c.k,112894000903873+c.lower,112894388728885+c.upper)) = pointBounds55238 := by
 decide +kernel
def cuts55239 : List PrefixCut := [⟨62,215721680,215721803⟩,
⟨64,223104019,223104146⟩]
theorem checked55239 : checkPrefixCuts (2^48) 7244218369 10 Manual.Count131072.C055239.packed 64 cuts55239 = true := by
 decide +kernel
def pointBounds55239 : List (Nat × Nat × Nat) := [(7244345344,112894441598665,112894829423927)]
theorem point_links_checked55239 : (cuts55239.take 1).map (fun c => (7244218369-1+2*2^10*c.k,112894225876985+c.lower,112894613702124+c.upper)) = pointBounds55239 := by
 decide +kernel
def cuts55240 : List PrefixCut := [⟨64,226324870,226324998⟩]
theorem checked55240 : checkPrefixCuts (2^48) 7244349441 10 Manual.Count131072.C055240.packed 64 cuts55240 = true := by
 decide +kernel
def cuts55241 : List PrefixCut := [⟨45,157511910,157511997⟩,
⟨64,223639893,223640018⟩]
theorem checked55241 : checkPrefixCuts (2^48) 7244480513 10 Manual.Count131072.C055241.packed 64 cuts55241 = true := by
 decide +kernel
def pointBounds55241 : List (Nat × Nat × Nat) := [(7244572672,112894832817784,112895220643265)]
theorem point_links_checked55241 : (cuts55241.take 1).map (fun c => (7244480513-1+2*2^10*c.k,112894675305874+c.lower,112895063131268+c.upper)) = pointBounds55241 := by
 decide +kernel
def cuts55242 : List PrefixCut := [⟨64,224063225,224063352⟩]
theorem checked55242 : checkPrefixCuts (2^48) 7244611585 10 Manual.Count131072.C055242.packed 64 cuts55242 = true := by
 decide +kernel
def cuts55243 : List PrefixCut := [⟨28,98762149,98762205⟩,
⟨64,224253435,224253565⟩]
theorem checked55243 : checkPrefixCuts (2^48) 7244742657 10 Manual.Count131072.C055243.packed 64 cuts55243 = true := by
 decide +kernel
def pointBounds55243 : List (Nat × Nat × Nat) := [(7244800000,112895221771141,112895609596843)]
theorem point_links_checked55243 : (cuts55243.take 1).map (fun c => (7244742657-1+2*2^10*c.k,112895123008992+c.lower,112895510834638+c.upper)) = pointBounds55243 := by
 decide +kernel
def cuts55244 : List PrefixCut := [⟨64,224055109,224055236⟩]
theorem checked55244 : checkPrefixCuts (2^48) 7244873729 10 Manual.Count131072.C055244.packed 64 cuts55244 = true := by
 decide +kernel
def cuts55245 : List PrefixCut := [⟨11,37413349,37413370⟩,
⟨64,222924393,222924517⟩]
theorem checked55245 : checkPrefixCuts (2^48) 7245004801 10 Manual.Count131072.C055245.packed 64 cuts55245 = true := by
 decide +kernel
def pointBounds55245 : List (Nat × Nat × Nat) := [(7245027328,112895608730885,112895996556809)]
theorem point_links_checked55245 : (cuts55245.take 1).map (fun c => (7245004801-1+2*2^10*c.k,112895571317536+c.lower,112895959143439+c.upper)) = pointBounds55245 := by
 decide +kernel
def cuts55246 : List PrefixCut := [⟨58,201358885,201359000⟩,
⟨64,221366388,221366515⟩]
theorem checked55246 : checkPrefixCuts (2^48) 7245135873 10 Manual.Count131072.C055246.packed 64 cuts55246 = true := by
 decide +kernel
def pointBounds55246 : List (Nat × Nat × Nat) := [(7245254656,112895995600814,112896383426956)]
theorem point_links_checked55246 : (cuts55246.take 1).map (fun c => (7245135873-1+2*2^10*c.k,112895794241929+c.lower,112896182067956+c.upper)) = pointBounds55246 := by
 decide +kernel
def cuts55247 : List PrefixCut := [⟨64,223576759,223576891⟩]
theorem checked55247 : checkPrefixCuts (2^48) 7245266945 10 Manual.Count131072.C055247.packed 64 cuts55247 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000163
