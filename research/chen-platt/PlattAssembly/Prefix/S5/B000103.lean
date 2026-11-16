import PlattAssemblyKernel
import PlattCertificates.Count131072.C043296
import PlattCertificates.Count131072.C043297
import PlattCertificates.Count131072.C043298
import PlattCertificates.Count131072.C043299
import PlattCertificates.Count131072.C043300
import PlattCertificates.Count131072.C043301
import PlattCertificates.Count131072.C043302
import PlattCertificates.Count131072.C043303
import PlattCertificates.Count131072.C043304
import PlattCertificates.Count131072.C043305
import PlattCertificates.Count131072.C043306
import PlattCertificates.Count131072.C043307
import PlattCertificates.Count131072.C043308
import PlattCertificates.Count131072.C043309
import PlattCertificates.Count131072.C043310
import PlattCertificates.Count131072.C043311
import PlattCertificates.Count131072.C043312
import PlattCertificates.Count131072.C043313
import PlattCertificates.Count131072.C043314
import PlattCertificates.Count131072.C043315
import PlattCertificates.Count131072.C043316
import PlattCertificates.Count131072.C043317
import PlattCertificates.Count131072.C043318
import PlattCertificates.Count131072.C043319
import PlattCertificates.Count131072.C043320
import PlattCertificates.Count131072.C043321
import PlattCertificates.Count131072.C043322
import PlattCertificates.Count131072.C043323
import PlattCertificates.Count131072.C043324
import PlattCertificates.Count131072.C043325
import PlattCertificates.Count131072.C043326
import PlattCertificates.Count131072.C043327
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000103
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts43296 : List PrefixCut := [⟨64,289014198,289014363⟩]
theorem checked43296 : checkPrefixCuts (2^48) 5678825473 10 Manual.Count131072.C043296.packed 64 cuts43296 = true := by
 decide +kernel
def cuts43297 : List PrefixCut := [⟨6,25773535,25773549⟩,
⟨64,287917112,287917280⟩]
theorem checked43297 : checkPrefixCuts (2^48) 5678956545 10 Manual.Count131072.C043297.packed 64 cuts43297 = true := by
 decide +kernel
def pointBounds43297 : List (Nat × Nat × Nat) := [(5678968832,109859945437968,109860331527670)]
theorem point_links_checked43297 : (cuts43297.take 1).map (fun c => (5678956545-1+2*2^10*c.k,109859919664433+c.lower,109860305754121+c.upper)) = pointBounds43297 := by
 decide +kernel
def cuts43298 : List PrefixCut := [⟨29,127129458,127129533⟩,
⟨64,288158247,288158413⟩]
theorem checked43298 : checkPrefixCuts (2^48) 5679087617 10 Manual.Count131072.C043298.packed 64 cuts43298 = true := by
 decide +kernel
def pointBounds43298 : List (Nat × Nat × Nat) := [(5679147008,109860334711003,109860720800934)]
theorem point_links_checked43298 : (cuts43298.take 1).map (fun c => (5679087617-1+2*2^10*c.k,109860207581545+c.lower,109860593671401+c.upper)) = pointBounds43298 := by
 decide +kernel
def cuts43299 : List PrefixCut := [⟨52,235963695,235963829⟩,
⟨64,290481038,290481204⟩]
theorem checked43299 : checkPrefixCuts (2^48) 5679218689 10 Manual.Count131072.C043299.packed 64 cuts43299 = true := by
 decide +kernel
def pointBounds43299 : List (Nat × Nat × Nat) := [(5679325184,109860731703487,109861117793643)]
theorem point_links_checked43299 : (cuts43299.take 1).map (fun c => (5679218689-1+2*2^10*c.k,109860495739792+c.lower,109860881829814+c.upper)) = pointBounds43299 := by
 decide +kernel
def cuts43300 : List PrefixCut := [⟨64,291862019,291862188⟩]
theorem checked43300 : checkPrefixCuts (2^48) 5679349761 10 Manual.Count131072.C043300.packed 64 cuts43300 = true := by
 decide +kernel
def cuts43301 : List PrefixCut := [⟨11,50501509,50501536⟩,
⟨64,290219820,290219986⟩]
theorem checked43301 : checkPrefixCuts (2^48) 5679480833 10 Manual.Count131072.C043301.packed 64 cuts43301 = true := by
 decide +kernel
def pointBounds43301 : List (Nat × Nat × Nat) := [(5679503360,109861128584358,109861514674742)]
theorem point_links_checked43301 : (cuts43301.take 1).map (fun c => (5679480833-1+2*2^10*c.k,109861078082849+c.lower,109861464173206+c.upper)) = pointBounds43301 := by
 decide +kernel
def cuts43302 : List PrefixCut := [⟨34,155019056,155019145⟩,
⟨64,288032585,288032754⟩]
theorem checked43302 : checkPrefixCuts (2^48) 5679611905 10 Manual.Count131072.C043302.packed 64 cuts43302 = true := by
 decide +kernel
def pointBounds43302 : List (Nat × Nat × Nat) := [(5679681536,109861523321725,109861909412337)]
theorem point_links_checked43302 : (cuts43302.take 1).map (fun c => (5679611905-1+2*2^10*c.k,109861368302669+c.lower,109861754393192+c.upper)) = pointBounds43302 := by
 decide +kernel
def cuts43303 : List PrefixCut := [⟨57,259630043,259630191⟩,
⟨64,290949814,290949982⟩]
theorem checked43303 : checkPrefixCuts (2^48) 5679742977 10 Manual.Count131072.C043303.packed 64 cuts43303 = true := by
 decide +kernel
def pointBounds43303 : List (Nat × Nat × Nat) := [(5679859712,109861915965297,109862302056137)]
theorem point_links_checked43303 : (cuts43303.take 1).map (fun c => (5679742977-1+2*2^10*c.k,109861656335254+c.lower,109862042425946+c.upper)) = pointBounds43303 := by
 decide +kernel
def cuts43304 : List PrefixCut := [⟨64,288613961,288614133⟩]
theorem checked43304 : checkPrefixCuts (2^48) 5679874049 10 Manual.Count131072.C043304.packed 64 cuts43304 = true := by
 decide +kernel
def cuts43305 : List PrefixCut := [⟨16,72945333,72945375⟩,
⟨64,293414105,293414271⟩]
theorem checked43305 : checkPrefixCuts (2^48) 5680005121 10 Manual.Count131072.C043305.packed 64 cuts43305 = true := by
 decide +kernel
def pointBounds43305 : List (Nat × Nat × Nat) := [(5680037888,109862308844362,109862694935436)]
theorem point_links_checked43305 : (cuts43305.take 1).map (fun c => (5680005121-1+2*2^10*c.k,109862235899029+c.lower,109862621990061+c.upper)) = pointBounds43305 := by
 decide +kernel
def cuts43306 : List PrefixCut := [⟨39,175173045,175173146⟩,
⟨64,286866256,286866421⟩]
theorem checked43306 : checkPrefixCuts (2^48) 5680136193 10 Manual.Count131072.C043306.packed 64 cuts43306 = true := by
 decide +kernel
def pointBounds43306 : List (Nat × Nat × Nat) := [(5680216064,109862704486179,109863090577478)]
theorem point_links_checked43306 : (cuts43306.take 1).map (fun c => (5680136193-1+2*2^10*c.k,109862529313134+c.lower,109862915404332+c.upper)) = pointBounds43306 := by
 decide +kernel
def cuts43307 : List PrefixCut := [⟨62,279724183,279724337⟩,
⟨64,289783235,289783395⟩]
theorem checked43307 : checkPrefixCuts (2^48) 5680267265 10 Manual.Count131072.C043307.packed 64 cuts43307 = true := by
 decide +kernel
def pointBounds43307 : List (Nat × Nat × Nat) := [(5680394240,109863095903573,109863481995090)]
theorem point_links_checked43307 : (cuts43307.take 1).map (fun c => (5680267265-1+2*2^10*c.k,109862816179390+c.lower,109863202270753+c.upper)) = pointBounds43307 := by
 decide +kernel
def cuts43308 : List PrefixCut := [⟨64,291064911,291065080⟩]
theorem checked43308 : checkPrefixCuts (2^48) 5680398337 10 Manual.Count131072.C043308.packed 64 cuts43308 = true := by
 decide +kernel
def cuts43309 : List PrefixCut := [⟨21,94493058,94493116⟩,
⟨64,287936501,287936678⟩]
theorem checked43309 : checkPrefixCuts (2^48) 5680529409 10 Manual.Count131072.C043309.packed 64 cuts43309 = true := by
 decide +kernel
def pointBounds43309 : List (Nat × Nat × Nat) := [(5680572416,109863491520594,109863877612344)]
theorem point_links_checked43309 : (cuts43309.take 1).map (fun c => (5680529409-1+2*2^10*c.k,109863397027536+c.lower,109863783119228+c.upper)) = pointBounds43309 := by
 decide +kernel
def cuts43310 : List PrefixCut := [⟨44,197850298,197850414⟩,
⟨64,288673090,288673261⟩]
theorem checked43310 : checkPrefixCuts (2^48) 5680660481 10 Manual.Count131072.C043310.packed 64 cuts43310 = true := by
 decide +kernel
def pointBounds43310 : List (Nat × Nat × Nat) := [(5680750592,109863882814335,109864268906320)]
theorem point_links_checked43310 : (cuts43310.take 1).map (fun c => (5680660481-1+2*2^10*c.k,109863684964037+c.lower,109864071055906+c.upper)) = pointBounds43310 := by
 decide +kernel
def cuts43311 : List PrefixCut := [⟨64,289558278,289558441⟩]
theorem checked43311 : checkPrefixCuts (2^48) 5680791553 10 Manual.Count131072.C043311.packed 64 cuts43311 = true := by
 decide +kernel
def cuts43312 : List PrefixCut := [⟨3,13526431,13526437⟩,
⟨64,288312930,288313099⟩]
theorem checked43312 : checkPrefixCuts (2^48) 5680922625 10 Manual.Count131072.C043312.packed 64 cuts43312 = true := by
 decide +kernel
def pointBounds43312 : List (Nat × Nat × Nat) := [(5680928768,109864276721836,109864662814045)]
theorem point_links_checked43312 : (cuts43312.take 1).map (fun c => (5680922625-1+2*2^10*c.k,109864263195405+c.lower,109864649287608+c.upper)) = pointBounds43312 := by
 decide +kernel
def cuts43313 : List PrefixCut := [⟨26,119306803,119306871⟩,
⟨64,289743132,289743300⟩]
theorem checked43313 : checkPrefixCuts (2^48) 5681053697 10 Manual.Count131072.C043313.packed 64 cuts43313 = true := by
 decide +kernel
def pointBounds43313 : List (Nat × Nat × Nat) := [(5681106944,109864670815138,109865056907578)]
theorem point_links_checked43313 : (cuts43313.take 1).map (fun c => (5681053697-1+2*2^10*c.k,109864551508335+c.lower,109864937600707+c.upper)) = pointBounds43313 := by
 decide +kernel
def cuts43314 : List PrefixCut := [⟨49,224338254,224338381⟩,
⟨64,291965944,291966110⟩]
theorem checked43314 : checkPrefixCuts (2^48) 5681184769 10 Manual.Count131072.C043314.packed 64 cuts43314 = true := by
 decide +kernel
def pointBounds43314 : List (Nat × Nat × Nat) := [(5681285120,109865065589721,109865451682388)]
theorem point_links_checked43314 : (cuts43314.take 1).map (fun c => (5681184769-1+2*2^10*c.k,109864841251467+c.lower,109865227344007+c.upper)) = pointBounds43314 := by
 decide +kernel
def cuts43315 : List PrefixCut := [⟨64,285865386,285865550⟩]
theorem checked43315 : checkPrefixCuts (2^48) 5681315841 10 Manual.Count131072.C043315.packed 64 cuts43315 = true := by
 decide +kernel
def cuts43316 : List PrefixCut := [⟨8,36215749,36215769⟩,
⟨64,287939540,287939706⟩]
theorem checked43316 : checkPrefixCuts (2^48) 5681446913 10 Manual.Count131072.C043316.packed 64 cuts43316 = true := by
 decide +kernel
def pointBounds43316 : List (Nat × Nat × Nat) := [(5681463296,109865455298546,109865841391436)]
theorem point_links_checked43316 : (cuts43316.take 1).map (fun c => (5681446913-1+2*2^10*c.k,109865419082797+c.lower,109865805175667+c.upper)) = pointBounds43316 := by
 decide +kernel
def cuts43317 : List PrefixCut := [⟨31,139954448,139954531⟩,
⟨64,288378762,288378931⟩]
theorem checked43317 : checkPrefixCuts (2^48) 5681577985 10 Manual.Count131072.C043317.packed 64 cuts43317 = true := by
 decide +kernel
def pointBounds43317 : List (Nat × Nat × Nat) := [(5681641472,109865846976785,109866233069904)]
theorem point_links_checked43317 : (cuts43317.take 1).map (fun c => (5681577985-1+2*2^10*c.k,109865707022337+c.lower,109866093115373+c.upper)) = pointBounds43317 := by
 decide +kernel
def cuts43318 : List PrefixCut := [⟨54,249434186,249434328⟩,
⟨64,294911428,294911595⟩]
theorem checked43318 : checkPrefixCuts (2^48) 5681709057 10 Manual.Count131072.C043318.packed 64 cuts43318 = true := by
 decide +kernel
def pointBounds43318 : List (Nat × Nat × Nat) := [(5681819648,109866244835285,109866630928632)]
theorem point_links_checked43318 : (cuts43318.take 1).map (fun c => (5681709057-1+2*2^10*c.k,109865995401099+c.lower,109866381494304+c.upper)) = pointBounds43318 := by
 decide +kernel
def cuts43319 : List PrefixCut := [⟨64,291337792,291337960⟩]
theorem checked43319 : checkPrefixCuts (2^48) 5681840129 10 Manual.Count131072.C043319.packed 64 cuts43319 = true := by
 decide +kernel
def cuts43320 : List PrefixCut := [⟨13,58207307,58207338⟩,
⟨64,288408330,288408492⟩]
theorem checked43320 : checkPrefixCuts (2^48) 5681971201 10 Manual.Count131072.C043320.packed 64 cuts43320 = true := by
 decide +kernel
def pointBounds43320 : List (Nat × Nat × Nat) := [(5681997824,109866639857626,109867025951197)]
theorem point_links_checked43320 : (cuts43320.take 1).map (fun c => (5681971201-1+2*2^10*c.k,109866581650319+c.lower,109866967743859+c.upper)) = pointBounds43320 := by
 decide +kernel
def cuts43321 : List PrefixCut := [⟨36,159409384,159409471⟩,
⟨64,285875331,285875494⟩]
theorem checked43321 : checkPrefixCuts (2^48) 5682102273 10 Manual.Count131072.C043321.packed 64 cuts43321 = true := by
 decide +kernel
def pointBounds43321 : List (Nat × Nat × Nat) := [(5682176000,109867029468033,109867415561822)]
theorem point_links_checked43321 : (cuts43321.take 1).map (fun c => (5682102273-1+2*2^10*c.k,109866870058649+c.lower,109867256152351+c.upper)) = pointBounds43321 := by
 decide +kernel
def cuts43322 : List PrefixCut := [⟨59,266054809,266054964⟩,
⟨64,288642707,288642874⟩]
theorem checked43322 : checkPrefixCuts (2^48) 5682233345 10 Manual.Count131072.C043322.packed 64 cuts43322 = true := by
 decide +kernel
def pointBounds43322 : List (Nat × Nat × Nat) := [(5682354176,109867421988789,109867808082809)]
theorem point_links_checked43322 : (cuts43322.take 1).map (fun c => (5682233345-1+2*2^10*c.k,109867155933980+c.lower,109867542027845+c.upper)) = pointBounds43322 := by
 decide +kernel
def cuts43323 : List PrefixCut := [⟨64,287447238,287447403⟩]
theorem checked43323 : checkPrefixCuts (2^48) 5682364417 10 Manual.Count131072.C043323.packed 64 cuts43323 = true := by
 decide +kernel
def cuts43324 : List PrefixCut := [⟨18,83315377,83315426⟩,
⟨64,292938808,292938978⟩]
theorem checked43324 : checkPrefixCuts (2^48) 5682495489 10 Manual.Count131072.C043324.packed 64 cuts43324 = true := by
 decide +kernel
def pointBounds43324 : List (Nat × Nat × Nat) := [(5682532352,109867815339302,109868201433548)]
theorem point_links_checked43324 : (cuts43324.take 1).map (fun c => (5682495489-1+2*2^10*c.k,109867732023925+c.lower,109868118118122+c.upper)) = pointBounds43324 := by
 decide +kernel
def cuts43325 : List PrefixCut := [⟨41,184754980,184755087⟩,
⟨64,288721805,288721971⟩]
theorem checked43325 : checkPrefixCuts (2^48) 5682626561 10 Manual.Count131072.C043325.packed 64 cuts43325 = true := by
 decide +kernel
def pointBounds43325 : List (Nat × Nat × Nat) := [(5682710528,109868209717713,109868595812187)]
theorem point_links_checked43325 : (cuts43325.take 1).map (fun c => (5682626561-1+2*2^10*c.k,109868024962733+c.lower,109868411057100+c.upper)) = pointBounds43325 := by
 decide +kernel
def cuts43326 : List PrefixCut := [⟨64,286535783,286535948⟩]
theorem checked43326 : checkPrefixCuts (2^48) 5682757633 10 Manual.Count131072.C043326.packed 64 cuts43326 = true := by
 decide +kernel
def pointBounds43326 : List (Nat × Nat × Nat) := [(5682888704,109868600220321,109868986315019)]
theorem point_links_checked43326 : (cuts43326.take 1).map (fun c => (5682757633-1+2*2^10*c.k,109868313684538+c.lower,109868699779071+c.upper)) = pointBounds43326 := by
 decide +kernel
def cuts43327 : List PrefixCut := [⟨64,287816984,287817150⟩]
theorem checked43327 : checkPrefixCuts (2^48) 5682888705 10 Manual.Count131072.C043327.packed 64 cuts43327 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000103
