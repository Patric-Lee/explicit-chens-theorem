import PlattAssemblyKernel
import PlattCertificates.Count131072.C056240
import PlattCertificates.Count131072.C056241
import PlattCertificates.Count131072.C056242
import PlattCertificates.Count131072.C056243
import PlattCertificates.Count131072.C056244
import PlattCertificates.Count131072.C056245
import PlattCertificates.Count131072.C056246
import PlattCertificates.Count131072.C056247
import PlattCertificates.Count131072.C056248
import PlattCertificates.Count131072.C056249
import PlattCertificates.Count131072.C056250
import PlattCertificates.Count131072.C056251
import PlattCertificates.Count131072.C056252
import PlattCertificates.Count131072.C056253
import PlattCertificates.Count131072.C056254
import PlattCertificates.Count131072.C056255
import PlattCertificates.Count131072.C056256
import PlattCertificates.Count131072.C056257
import PlattCertificates.Count131072.C056258
import PlattCertificates.Count131072.C056259
import PlattCertificates.Count131072.C056260
import PlattCertificates.Count131072.C056261
import PlattCertificates.Count131072.C056262
import PlattCertificates.Count131072.C056263
import PlattCertificates.Count131072.C056264
import PlattCertificates.Count131072.C056265
import PlattCertificates.Count131072.C056266
import PlattCertificates.Count131072.C056267
import PlattCertificates.Count131072.C056268
import PlattCertificates.Count131072.C056269
import PlattCertificates.Count131072.C056270
import PlattCertificates.Count131072.C056271
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000195
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts56240 : List PrefixCut := [⟨64,220127451,220127579⟩]
theorem checked56240 : checkPrefixCuts (2^48) 7375421441 10 Manual.Count131072.C056240.packed 64 cuts56240 = true := by
 decide +kernel
def cuts56241 : List PrefixCut := [⟨18,62587538,62587571⟩,
⟨64,223214735,223214855⟩]
theorem checked56241 : checkPrefixCuts (2^48) 7375552513 10 Manual.Count131072.C056241.packed 64 cuts56241 = true := by
 decide +kernel
def pointBounds56241 : List (Nat × Nat × Nat) := [(7375589376,113116941787376,113117329738982)]
theorem point_links_checked56241 : (cuts56241.take 1).map (fun c => (7375552513-1+2*2^10*c.k,113116879199838+c.lower,113117267151411+c.upper)) = pointBounds56241 := by
 decide +kernel
def cuts56242 : List PrefixCut := [⟨64,217066654,217066776⟩]
theorem checked56242 : checkPrefixCuts (2^48) 7375683585 10 Manual.Count131072.C056242.packed 64 cuts56242 = true := by
 decide +kernel
def cuts56243 : List PrefixCut := [⟨3,10380024,10380030⟩,
⟨64,220726316,220726437⟩]
theorem checked56243 : checkPrefixCuts (2^48) 7375814657 10 Manual.Count131072.C056243.packed 64 cuts56243 = true := by
 decide +kernel
def pointBounds56243 : List (Nat × Nat × Nat) := [(7375820800,113117329861251,113117717813072)]
theorem point_links_checked56243 : (cuts56243.take 1).map (fun c => (7375814657-1+2*2^10*c.k,113117319481227+c.lower,113117707433042+c.upper)) = pointBounds56243 := by
 decide +kernel
def cuts56244 : List PrefixCut := [⟨52,180730113,180730219⟩,
⟨64,222554110,222554239⟩]
theorem checked56244 : checkPrefixCuts (2^48) 7375945729 10 Manual.Count131072.C056244.packed 64 cuts56244 = true := by
 decide +kernel
def pointBounds56244 : List (Nat × Nat × Nat) := [(7376052224,113117720937656,113118108889698)]
theorem point_links_checked56244 : (cuts56244.take 1).map (fun c => (7375945729-1+2*2^10*c.k,113117540207543+c.lower,113117928159479+c.upper)) = pointBounds56244 := by
 decide +kernel
def cuts56245 : List PrefixCut := [⟨64,216330039,216330160⟩]
theorem checked56245 : checkPrefixCuts (2^48) 7376076801 10 Manual.Count131072.C056245.packed 64 cuts56245 = true := by
 decide +kernel
def cuts56246 : List PrefixCut := [⟨37,128101913,128101982⟩,
⟨64,220829018,220829140⟩]
theorem checked56246 : checkPrefixCuts (2^48) 7376207873 10 Manual.Count131072.C056246.packed 64 cuts56246 = true := by
 decide +kernel
def pointBounds56246 : List (Nat × Nat × Nat) := [(7376283648,113118107193605,113118495145860)]
theorem point_links_checked56246 : (cuts56246.take 1).map (fun c => (7376207873-1+2*2^10*c.k,113117979091692+c.lower,113118367043878+c.upper)) = pointBounds56246 := by
 decide +kernel
def cuts56247 : List PrefixCut := [⟨64,219909283,219909406⟩]
theorem checked56247 : checkPrefixCuts (2^48) 7376338945 10 Manual.Count131072.C056247.packed 64 cuts56247 = true := by
 decide +kernel
def cuts56248 : List PrefixCut := [⟨22,74714079,74714121⟩,
⟨64,218455358,218455480⟩]
theorem checked56248 : checkPrefixCuts (2^48) 7376470017 10 Manual.Count131072.C056248.packed 64 cuts56248 = true := by
 decide +kernel
def pointBounds56248 : List (Nat × Nat × Nat) := [(7376515072,113118494544072,113118882496545)]
theorem point_links_checked56248 : (cuts56248.take 1).map (fun c => (7376470017-1+2*2^10*c.k,113118419829993+c.lower,113118807782424+c.upper)) = pointBounds56248 := by
 decide +kernel
def cuts56249 : List PrefixCut := [⟨64,218985694,218985819⟩]
theorem checked56249 : checkPrefixCuts (2^48) 7376601089 10 Manual.Count131072.C056249.packed 64 cuts56249 = true := by
 decide +kernel
def cuts56250 : List PrefixCut := [⟨7,23161354,23161367⟩,
⟨64,218676538,218676660⟩]
theorem checked56250 : checkPrefixCuts (2^48) 7376732161 10 Manual.Count131072.C056250.packed 64 cuts56250 = true := by
 decide +kernel
def pointBounds56250 : List (Nat × Nat × Nat) := [(7376746496,113118880432399,113119268385090)]
theorem point_links_checked56250 : (cuts56250.take 1).map (fun c => (7376732161-1+2*2^10*c.k,113118857271045+c.lower,113119245223723+c.upper)) = pointBounds56250 := by
 decide +kernel
def cuts56251 : List PrefixCut := [⟨56,193413532,193413641⟩,
⟨64,220771247,220771372⟩]
theorem checked56251 : checkPrefixCuts (2^48) 7376863233 10 Manual.Count131072.C056251.packed 64 cuts56251 = true := by
 decide +kernel
def pointBounds56251 : List (Nat × Nat × Nat) := [(7376977920,113119269361115,113119657314024)]
theorem point_links_checked56251 : (cuts56251.take 1).map (fun c => (7376863233-1+2*2^10*c.k,113119075947583+c.lower,113119463900383+c.upper)) = pointBounds56251 := by
 decide +kernel
def cuts56252 : List PrefixCut := [⟨64,222789567,222789694⟩]
theorem checked56252 : checkPrefixCuts (2^48) 7376994305 10 Manual.Count131072.C056252.packed 64 cuts56252 = true := by
 decide +kernel
def cuts56253 : List PrefixCut := [⟨41,141821666,141821746⟩,
⟨64,222594821,222594947⟩]
theorem checked56253 : checkPrefixCuts (2^48) 7377125377 10 Manual.Count131072.C056253.packed 64 cuts56253 = true := by
 decide +kernel
def pointBounds56253 : List (Nat × Nat × Nat) := [(7377209344,113119661330063,113120049283195)]
theorem point_links_checked56253 : (cuts56253.take 1).map (fun c => (7377125377-1+2*2^10*c.k,113119519508397+c.lower,113119907461449+c.upper)) = pointBounds56253 := by
 decide +kernel
def cuts56254 : List PrefixCut := [⟨64,220377949,220378072⟩]
theorem checked56254 : checkPrefixCuts (2^48) 7377256449 10 Manual.Count131072.C056254.packed 64 cuts56254 = true := by
 decide +kernel
def cuts56255 : List PrefixCut := [⟨26,86417897,86417949⟩,
⟨64,215032543,215032669⟩]
theorem checked56255 : checkPrefixCuts (2^48) 7377387521 10 Manual.Count131072.C056255.packed 64 cuts56255 = true := by
 decide +kernel
def pointBounds56255 : List (Nat × Nat × Nat) := [(7377440768,113120048899064,113120436852417)]
theorem point_links_checked56255 : (cuts56255.take 1).map (fun c => (7377387521-1+2*2^10*c.k,113119962481167+c.lower,113120350434468+c.upper)) = pointBounds56255 := by
 decide +kernel
def cuts56256 : List PrefixCut := [⟨64,220904246,220904374⟩]
theorem checked56256 : checkPrefixCuts (2^48) 7377518593 10 Manual.Count131072.C056256.packed 64 cuts56256 = true := by
 decide +kernel
def cuts56257 : List PrefixCut := [⟨11,37732647,37732668⟩,
⟨64,219336095,219336219⟩]
theorem checked56257 : checkPrefixCuts (2^48) 7377649665 10 Manual.Count131072.C056257.packed 64 cuts56257 = true := by
 decide +kernel
def pointBounds56257 : List (Nat × Nat × Nat) := [(7377672192,113120436150603,113120824104179)]
theorem point_links_checked56257 : (cuts56257.take 1).map (fun c => (7377649665-1+2*2^10*c.k,113120398417956+c.lower,113120786371511+c.upper)) = pointBounds56257 := by
 decide +kernel
def cuts56258 : List PrefixCut := [⟨60,208268415,208268534⟩,
⟨64,221964641,221964767⟩]
theorem checked56258 : checkPrefixCuts (2^48) 7377780737 10 Manual.Count131072.C056258.packed 64 cuts56258 = true := by
 decide +kernel
def pointBounds56258 : List (Nat × Nat × Nat) := [(7377903616,113120826022466,113121213976264)]
theorem point_links_checked56258 : (cuts56258.take 1).map (fun c => (7377780737-1+2*2^10*c.k,113120617754051+c.lower,113121005707730+c.upper)) = pointBounds56258 := by
 decide +kernel
def cuts56259 : List PrefixCut := [⟨64,223219676,223219803⟩]
theorem checked56259 : checkPrefixCuts (2^48) 7377911809 10 Manual.Count131072.C056259.packed 64 cuts56259 = true := by
 decide +kernel
def cuts56260 : List PrefixCut := [⟨45,150425879,150425966⟩,
⟨64,215776431,215776555⟩]
theorem checked56260 : checkPrefixCuts (2^48) 7378042881 10 Manual.Count131072.C056260.packed 64 cuts56260 = true := by
 decide +kernel
def pointBounds56260 : List (Nat × Nat × Nat) := [(7378135040,113121213364247,113121601318266)]
theorem point_links_checked56260 : (cuts56260.take 1).map (fun c => (7378042881-1+2*2^10*c.k,113121062938368+c.lower,113121450892300+c.upper)) = pointBounds56260 := by
 decide +kernel
def cuts56261 : List PrefixCut := [⟨64,222296159,222296282⟩]
theorem checked56261 : checkPrefixCuts (2^48) 7378173953 10 Manual.Count131072.C056261.packed 64 cuts56261 = true := by
 decide +kernel
def cuts56262 : List PrefixCut := [⟨30,103383336,103383394⟩,
⟨64,220041427,220041552⟩]
theorem checked56262 : checkPrefixCuts (2^48) 7378305025 10 Manual.Count131072.C056262.packed 64 cuts56262 = true := by
 decide +kernel
def pointBounds56262 : List (Nat × Nat × Nat) := [(7378366464,113121604394294,113121992348531)]
theorem point_links_checked56262 : (cuts56262.take 1).map (fun c => (7378305025-1+2*2^10*c.k,113121501010958+c.lower,113121888965137+c.upper)) = pointBounds56262 := by
 decide +kernel
def cuts56263 : List PrefixCut := [⟨64,218740497,218740624⟩]
theorem checked56263 : checkPrefixCuts (2^48) 7378436097 10 Manual.Count131072.C056263.packed 64 cuts56263 = true := by
 decide +kernel
def cuts56264 : List PrefixCut := [⟨15,50469218,50469246⟩,
⟨64,217210716,217210839⟩]
theorem checked56264 : checkPrefixCuts (2^48) 7378567169 10 Manual.Count131072.C056264.packed 64 cuts56264 = true := by
 decide +kernel
def pointBounds56264 : List (Nat × Nat × Nat) := [(7378597888,113121990262100,113122378216559)]
theorem point_links_checked56264 : (cuts56264.take 1).map (fun c => (7378567169-1+2*2^10*c.k,113121939792882+c.lower,113122327747313+c.upper)) = pointBounds56264 := by
 decide +kernel
def cuts56265 : List PrefixCut := [⟨64,217893493,217893616⟩]
theorem checked56265 : checkPrefixCuts (2^48) 7378698241 10 Manual.Count131072.C056265.packed 64 cuts56265 = true := by
 decide +kernel
def pointBounds56265 : List (Nat × Nat × Nat) := [(7378829312,113122374897091,113122762851768)]
theorem point_links_checked56265 : (cuts56265.take 1).map (fun c => (7378698241-1+2*2^10*c.k,113122157003598+c.lower,113122544958152+c.upper)) = pointBounds56265 := by
 decide +kernel
def cuts56266 : List PrefixCut := [⟨64,221055730,221055848⟩]
theorem checked56266 : checkPrefixCuts (2^48) 7378829313 10 Manual.Count131072.C056266.packed 64 cuts56266 = true := by
 decide +kernel
def cuts56267 : List PrefixCut := [⟨49,168793153,168793248⟩,
⟨64,219869313,219869438⟩]
theorem checked56267 : checkPrefixCuts (2^48) 7378960385 10 Manual.Count131072.C056267.packed 64 cuts56267 = true := by
 decide +kernel
def pointBounds56267 : List (Nat × Nat × Nat) := [(7379060736,113122764745974,113123152700864)]
theorem point_links_checked56267 : (cuts56267.take 1).map (fun c => (7378960385-1+2*2^10*c.k,113122595952821+c.lower,113122983907616+c.upper)) = pointBounds56267 := by
 decide +kernel
def cuts56268 : List PrefixCut := [⟨64,218682911,218683039⟩]
theorem checked56268 : checkPrefixCuts (2^48) 7379091457 10 Manual.Count131072.C056268.packed 64 cuts56268 = true := by
 decide +kernel
def cuts56269 : List PrefixCut := [⟨34,117674455,117674523⟩,
⟨64,221272820,221272949⟩]
theorem checked56269 : checkPrefixCuts (2^48) 7379222529 10 Manual.Count131072.C056269.packed 64 cuts56269 = true := by
 decide +kernel
def pointBounds56269 : List (Nat × Nat × Nat) := [(7379292160,113123152179500,113123540134616)]
theorem point_links_checked56269 : (cuts56269.take 1).map (fun c => (7379222529-1+2*2^10*c.k,113123034505045+c.lower,113123422460093+c.upper)) = pointBounds56269 := by
 decide +kernel
def cuts56270 : List PrefixCut := [⟨64,219438027,219438153⟩]
theorem checked56270 : checkPrefixCuts (2^48) 7379353601 10 Manual.Count131072.C056270.packed 64 cuts56270 = true := by
 decide +kernel
def cuts56271 : List PrefixCut := [⟨19,66025172,66025210⟩,
⟨64,220997960,220998082⟩]
theorem checked56271 : checkPrefixCuts (2^48) 7379484673 10 Manual.Count131072.C056271.packed 64 cuts56271 = true := by
 decide +kernel
def pointBounds56271 : List (Nat × Nat × Nat) := [(7379523584,113123541241064,113123929196405)]
theorem point_links_checked56271 : (cuts56271.take 1).map (fun c => (7379484673-1+2*2^10*c.k,113123475215892+c.lower,113123863171195+c.upper)) = pointBounds56271 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000195
