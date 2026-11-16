import PlattAssemblyKernel
import PlattCertificates.Count131072.C074288
import PlattCertificates.Count131072.C074289
import PlattCertificates.Count131072.C074290
import PlattCertificates.Count131072.C074291
import PlattCertificates.Count131072.C074292
import PlattCertificates.Count131072.C074293
import PlattCertificates.Count131072.C074294
import PlattCertificates.Count131072.C074295
import PlattCertificates.Count131072.C074296
import PlattCertificates.Count131072.C074297
import PlattCertificates.Count131072.C074298
import PlattCertificates.Count131072.C074299
import PlattCertificates.Count131072.C074300
import PlattCertificates.Count131072.C074301
import PlattCertificates.Count131072.C074302
import PlattCertificates.Count131072.C074303
import PlattCertificates.Count131072.C074304
import PlattCertificates.Count131072.C074305
import PlattCertificates.Count131072.C074306
import PlattCertificates.Count131072.C074307
import PlattCertificates.Count131072.C074308
import PlattCertificates.Count131072.C074309
import PlattCertificates.Count131072.C074310
import PlattCertificates.Count131072.C074311
import PlattCertificates.Count131072.C074312
import PlattCertificates.Count131072.C074313
import PlattCertificates.Count131072.C074314
import PlattCertificates.Count131072.C074315
import PlattCertificates.Count131072.C074316
import PlattCertificates.Count131072.C074317
import PlattCertificates.Count131072.C074318
import PlattCertificates.Count131072.C074319
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000134
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74288 : List PrefixCut := [⟨64,163982933,163983038⟩]
theorem checked74288 : checkPrefixCuts (2^48) 9741008897 10 Manual.Count131072.C074288.packed 64 cuts74288 = true := by
 decide +kernel
def cuts74289 : List PrefixCut := [⟨43,112605166,112605234⟩,
⟨64,167390374,167390477⟩]
theorem checked74289 : checkPrefixCuts (2^48) 9741139969 10 Manual.Count131072.C074289.packed 64 cuts74289 = true := by
 decide +kernel
def pointBounds74289 : List (Nat × Nat × Nat) := [(9741228032,116542337692036,116542727629644)]
theorem point_links_checked74289 : (cuts74289.take 1).map (fun c => (9741139969-1+2*2^10*c.k,116542225086870+c.lower,116542615024410+c.upper)) = pointBounds74289 := by
 decide +kernel
def cuts74290 : List PrefixCut := [⟨64,165105433,165105528⟩]
theorem checked74290 : checkPrefixCuts (2^48) 9741271041 10 Manual.Count131072.C074290.packed 64 cuts74290 = true := by
 decide +kernel
def cuts74291 : List PrefixCut := [⟨64,163282851,163282946⟩]
theorem checked74291 : checkPrefixCuts (2^48) 9741402113 10 Manual.Count131072.C074291.packed 64 cuts74291 = true := by
 decide +kernel
def pointBounds74291 : List (Nat × Nat × Nat) := [(9741533184,116542720865528,116543110803361)]
theorem point_links_checked74291 : (cuts74291.take 1).map (fun c => (9741402113-1+2*2^10*c.k,116542557582677+c.lower,116542947520415+c.upper)) = pointBounds74291 := by
 decide +kernel
def cuts74292 : List PrefixCut := [⟨64,167874813,167874919⟩]
theorem checked74292 : checkPrefixCuts (2^48) 9741533185 10 Manual.Count131072.C074292.packed 64 cuts74292 = true := by
 decide +kernel
def cuts74293 : List PrefixCut := [⟨64,163047300,163047396⟩]
theorem checked74293 : checkPrefixCuts (2^48) 9741664257 10 Manual.Count131072.C074293.packed 64 cuts74293 = true := by
 decide +kernel
def cuts74294 : List PrefixCut := [⟨21,55677717,55677744⟩,
⟨64,164403110,164403202⟩]
theorem checked74294 : checkPrefixCuts (2^48) 9741795329 10 Manual.Count131072.C074294.packed 64 cuts74294 = true := by
 decide +kernel
def pointBounds74294 : List (Nat × Nat × Nat) := [(9741838336,116543107465358,116543497403420)]
theorem point_links_checked74294 : (cuts74294.take 1).map (fun c => (9741795329-1+2*2^10*c.k,116543051787641+c.lower,116543441725676+c.upper)) = pointBounds74294 := by
 decide +kernel
def cuts74295 : List PrefixCut := [⟨64,162696207,162696306⟩]
theorem checked74295 : checkPrefixCuts (2^48) 9741926401 10 Manual.Count131072.C074295.packed 64 cuts74295 = true := by
 decide +kernel
def cuts74296 : List PrefixCut := [⟨42,108405145,108405215⟩,
⟨64,165727735,165727837⟩]
theorem checked74296 : checkPrefixCuts (2^48) 9742057473 10 Manual.Count131072.C074296.packed 64 cuts74296 = true := by
 decide +kernel
def pointBounds74296 : List (Nat × Nat × Nat) := [(9742143488,116543487292103,116543877230399)]
theorem point_links_checked74296 : (cuts74296.take 1).map (fun c => (9742057473-1+2*2^10*c.k,116543378886958+c.lower,116543768825184+c.upper)) = pointBounds74296 := by
 decide +kernel
def cuts74297 : List PrefixCut := [⟨64,164656499,164656591⟩]
theorem checked74297 : checkPrefixCuts (2^48) 9742188545 10 Manual.Count131072.C074297.packed 64 cuts74297 = true := by
 decide +kernel
def cuts74298 : List PrefixCut := [⟨63,165434384,165434484⟩,
⟨64,167919061,167919163⟩]
theorem checked74298 : checkPrefixCuts (2^48) 9742319617 10 Manual.Count131072.C074298.packed 64 cuts74298 = true := by
 decide +kernel
def pointBounds74298 : List (Nat × Nat × Nat) := [(9742448640,116543874705576,116544264644096)]
theorem point_links_checked74298 : (cuts74298.take 1).map (fun c => (9742319617-1+2*2^10*c.k,116543709271192+c.lower,116544099209612+c.upper)) = pointBounds74298 := by
 decide +kernel
def cuts74299 : List PrefixCut := [⟨64,165663258,165663360⟩]
theorem checked74299 : checkPrefixCuts (2^48) 9742450689 10 Manual.Count131072.C074299.packed 64 cuts74299 = true := by
 decide +kernel
def cuts74300 : List PrefixCut := [⟨64,164592072,164592174⟩]
theorem checked74300 : checkPrefixCuts (2^48) 9742581761 10 Manual.Count131072.C074300.packed 64 cuts74300 = true := by
 decide +kernel
def cuts74301 : List PrefixCut := [⟨20,51830010,51830040⟩,
⟨64,162394172,162394267⟩]
theorem checked74301 : checkPrefixCuts (2^48) 9742712833 10 Manual.Count131072.C074301.packed 64 cuts74301 = true := by
 decide +kernel
def pointBounds74301 : List (Nat × Nat × Nat) := [(9742753792,116544259275593,116544649214349)]
theorem point_links_checked74301 : (cuts74301.take 1).map (fun c => (9742712833-1+2*2^10*c.k,116544207445583+c.lower,116544597384309+c.upper)) = pointBounds74301 := by
 decide +kernel
def cuts74302 : List PrefixCut := [⟨64,163952058,163952156⟩]
theorem checked74302 : checkPrefixCuts (2^48) 9742843905 10 Manual.Count131072.C074302.packed 64 cuts74302 = true := by
 decide +kernel
def cuts74303 : List PrefixCut := [⟨41,104668151,104668214⟩,
⟨64,164152078,164152176⟩]
theorem checked74303 : checkPrefixCuts (2^48) 9742974977 10 Manual.Count131072.C074303.packed 64 cuts74303 = true := by
 decide +kernel
def pointBounds74303 : List (Nat × Nat × Nat) := [(9743058944,116544638459964,116545028398946)]
theorem point_links_checked74303 : (cuts74303.take 1).map (fun c => (9742974977-1+2*2^10*c.k,116544533791813+c.lower,116544923730732+c.upper)) = pointBounds74303 := by
 decide +kernel
def cuts74304 : List PrefixCut := [⟨64,164640996,164641091⟩]
theorem checked74304 : checkPrefixCuts (2^48) 9743106049 10 Manual.Count131072.C074304.packed 64 cuts74304 = true := by
 decide +kernel
def cuts74305 : List PrefixCut := [⟨62,161027676,161027772⟩,
⟨64,165852118,165852217⟩]
theorem checked74305 : checkPrefixCuts (2^48) 9743237121 10 Manual.Count131072.C074305.packed 64 cuts74305 = true := by
 decide +kernel
def pointBounds74305 : List (Nat × Nat × Nat) := [(9743364096,116545023612563,116545413551771)]
theorem point_links_checked74305 : (cuts74305.take 1).map (fun c => (9743237121-1+2*2^10*c.k,116544862584887+c.lower,116545252523999+c.upper)) = pointBounds74305 := by
 decide +kernel
def cuts74306 : List PrefixCut := [⟨64,166167657,166167759⟩]
theorem checked74306 : checkPrefixCuts (2^48) 9743368193 10 Manual.Count131072.C074306.packed 64 cuts74306 = true := by
 decide +kernel
def cuts74307 : List PrefixCut := [⟨64,165212110,165212210⟩]
theorem checked74307 : checkPrefixCuts (2^48) 9743499265 10 Manual.Count131072.C074307.packed 64 cuts74307 = true := by
 decide +kernel
def cuts74308 : List PrefixCut := [⟨19,48531897,48531926⟩,
⟨64,165209877,165209983⟩]
theorem checked74308 : checkPrefixCuts (2^48) 9743630337 10 Manual.Count131072.C074308.packed 64 cuts74308 = true := by
 decide +kernel
def pointBounds74308 : List (Nat × Nat × Nat) := [(9743669248,116545408348669,116545798288111)]
theorem point_links_checked74308 : (cuts74308.take 1).map (fun c => (9743630337-1+2*2^10*c.k,116545359816772+c.lower,116545749756185+c.upper)) = pointBounds74308 := by
 decide +kernel
def cuts74309 : List PrefixCut := [⟨64,166132069,166132168⟩]
theorem checked74309 : checkPrefixCuts (2^48) 9743761409 10 Manual.Count131072.C074309.packed 64 cuts74309 = true := by
 decide +kernel
def cuts74310 : List PrefixCut := [⟨40,104369436,104369494⟩,
⟨64,165205456,165205549⟩]
theorem checked74310 : checkPrefixCuts (2^48) 9743892481 10 Manual.Count131072.C074310.packed 64 cuts74310 = true := by
 decide +kernel
def pointBounds74310 : List (Nat × Nat × Nat) := [(9743974400,116545795528154,116546185467830)]
theorem point_links_checked74310 : (cuts74310.take 1).map (fun c => (9743892481-1+2*2^10*c.k,116545691158718+c.lower,116546081098336+c.upper)) = pointBounds74310 := by
 decide +kernel
def cuts74311 : List PrefixCut := [⟨64,165492088,165492193⟩]
theorem checked74311 : checkPrefixCuts (2^48) 9744023553 10 Manual.Count131072.C074311.packed 64 cuts74311 = true := by
 decide +kernel
def cuts74312 : List PrefixCut := [⟨61,157170652,157170747⟩,
⟨64,164796598,164796697⟩]
theorem checked74312 : checkPrefixCuts (2^48) 9744154625 10 Manual.Count131072.C074312.packed 64 cuts74312 = true := by
 decide +kernel
def pointBounds74312 : List (Nat × Nat × Nat) := [(9744279552,116546179026914,116546568966825)]
theorem point_links_checked74312 : (cuts74312.take 1).map (fun c => (9744154625-1+2*2^10*c.k,116546021856262+c.lower,116546411796078+c.upper)) = pointBounds74312 := by
 decide +kernel
def cuts74313 : List PrefixCut := [⟨64,164909923,164910017⟩]
theorem checked74313 : checkPrefixCuts (2^48) 9744285697 10 Manual.Count131072.C074313.packed 64 cuts74313 = true := by
 decide +kernel
def cuts74314 : List PrefixCut := [⟨64,161354772,161354870⟩]
theorem checked74314 : checkPrefixCuts (2^48) 9744416769 10 Manual.Count131072.C074314.packed 64 cuts74314 = true := by
 decide +kernel
def cuts74315 : List PrefixCut := [⟨18,46303165,46303194⟩,
⟨64,161554806,161554906⟩]
theorem checked74315 : checkPrefixCuts (2^48) 9744547841 10 Manual.Count131072.C074315.packed 64 cuts74315 = true := by
 decide +kernel
def pointBounds74315 : List (Nat × Nat × Nat) := [(9744584704,116546559220720,116546949160856)]
theorem point_links_checked74315 : (cuts74315.take 1).map (fun c => (9744547841-1+2*2^10*c.k,116546512917555+c.lower,116546902857662+c.upper)) = pointBounds74315 := by
 decide +kernel
def cuts74316 : List PrefixCut := [⟨64,166549699,166549796⟩]
theorem checked74316 : checkPrefixCuts (2^48) 9744678913 10 Manual.Count131072.C074316.packed 64 cuts74316 = true := by
 decide +kernel
def cuts74317 : List PrefixCut := [⟨39,99853639,99853704⟩,
⟨64,163832326,163832429⟩]
theorem checked74317 : checkPrefixCuts (2^48) 9744809985 10 Manual.Count131072.C074317.packed 64 cuts74317 = true := by
 decide +kernel
def pointBounds74317 : List (Nat × Nat × Nat) := [(9744889856,116546940875699,116547330816068)]
theorem point_links_checked74317 : (cuts74317.take 1).map (fun c => (9744809985-1+2*2^10*c.k,116546841022060+c.lower,116547230962364+c.upper)) = pointBounds74317 := by
 decide +kernel
def cuts74318 : List PrefixCut := [⟨64,166227500,166227598⟩]
theorem checked74318 : checkPrefixCuts (2^48) 9744941057 10 Manual.Count131072.C074318.packed 64 cuts74318 = true := by
 decide +kernel
def cuts74319 : List PrefixCut := [⟨60,156029405,156029499⟩,
⟨64,166658512,166658612⟩]
theorem checked74319 : checkPrefixCuts (2^48) 9745072129 10 Manual.Count131072.C074319.packed 64 cuts74319 = true := by
 decide +kernel
def pointBounds74319 : List (Nat × Nat × Nat) := [(9745195008,116547327111291,116547717051890)]
theorem point_links_checked74319 : (cuts74319.take 1).map (fun c => (9745072129-1+2*2^10*c.k,116547171081886+c.lower,116547561022391+c.upper)) = pointBounds74319 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000134
