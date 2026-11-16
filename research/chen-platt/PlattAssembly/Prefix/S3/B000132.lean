import PlattAssemblyKernel
import PlattCertificates.Count131072.C024224
import PlattCertificates.Count131072.C024225
import PlattCertificates.Count131072.C024226
import PlattCertificates.Count131072.C024227
import PlattCertificates.Count131072.C024228
import PlattCertificates.Count131072.C024229
import PlattCertificates.Count131072.C024230
import PlattCertificates.Count131072.C024231
import PlattCertificates.Count131072.C024232
import PlattCertificates.Count131072.C024233
import PlattCertificates.Count131072.C024234
import PlattCertificates.Count131072.C024235
import PlattCertificates.Count131072.C024236
import PlattCertificates.Count131072.C024237
import PlattCertificates.Count131072.C024238
import PlattCertificates.Count131072.C024239
import PlattCertificates.Count131072.C024240
import PlattCertificates.Count131072.C024241
import PlattCertificates.Count131072.C024242
import PlattCertificates.Count131072.C024243
import PlattCertificates.Count131072.C024244
import PlattCertificates.Count131072.C024245
import PlattCertificates.Count131072.C024246
import PlattCertificates.Count131072.C024247
import PlattCertificates.Count131072.C024248
import PlattCertificates.Count131072.C024249
import PlattCertificates.Count131072.C024250
import PlattCertificates.Count131072.C024251
import PlattCertificates.Count131072.C024252
import PlattCertificates.Count131072.C024253
import PlattCertificates.Count131072.C024254
import PlattCertificates.Count131072.C024255
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000132
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24224 : List PrefixCut := [⟨18,74994348,74994391⟩,
⟨116,484578060,484578338⟩,
⟨128,536372744,536373053⟩]
theorem checked24224 : checkPrefixCuts (2^48) 3179020289 9 Manual.Count131072.C024224.packed 128 cuts24224 = true := by
 decide +kernel
def pointBounds24224 : List (Nat × Nat × Nat) := [(3179038720,102493282168163,102493663956743),(3179139072,102493691751875,102494073540690)]
theorem point_links_checked24224 : (cuts24224.take 2).map (fun c => (3179020289-1+2*2^9*c.k,102493207173815+c.lower,102493588962352+c.upper)) = pointBounds24224 := by
 decide +kernel
def cuts24225 : List PrefixCut := [⟨86,354765850,354766045⟩,
⟨128,528470929,528471225⟩]
theorem checked24225 : checkPrefixCuts (2^48) 3179151361 9 Manual.Count131072.C024225.packed 128 cuts24225 = true := by
 decide +kernel
def pointBounds24225 : List (Nat × Nat × Nat) := [(3179239424,102494098312409,102494480101450)]
theorem point_links_checked24225 : (cuts24225.take 1).map (fun c => (3179151361-1+2*2^9*c.k,102493743546559+c.lower,102494125335405+c.upper)) = pointBounds24225 := by
 decide +kernel
def cuts24226 : List PrefixCut := [⟨56,229743909,229744042⟩,
⟨128,526412888,526413188⟩]
theorem checked24226 : checkPrefixCuts (2^48) 3179282433 9 Manual.Count131072.C024226.packed 128 cuts24226 = true := by
 decide +kernel
def pointBounds24226 : List (Nat × Nat × Nat) := [(3179339776,102494501761397,102494883550672)]
theorem point_links_checked24226 : (cuts24226.take 1).map (fun c => (3179282433-1+2*2^9*c.k,102494272017488+c.lower,102494653806630+c.upper)) = pointBounds24226 := by
 decide +kernel
def cuts24227 : List PrefixCut := [⟨26,105970503,105970563⟩,
⟨124,512138377,512138669⟩,
⟨128,528604372,528604673⟩]
theorem checked24227 : checkPrefixCuts (2^48) 3179413505 9 Manual.Count131072.C024227.packed 128 cuts24227 = true := by
 decide +kernel
def pointBounds24227 : List (Nat × Nat × Nat) := [(3179440128,102494904400879,102495286190381),(3179540480,102495310568753,102495692358487)]
theorem point_links_checked24227 : (cuts24227.take 2).map (fun c => (3179413505-1+2*2^9*c.k,102494798430376+c.lower,102495180219818+c.upper)) = pointBounds24227 := by
 decide +kernel
def cuts24228 : List PrefixCut := [⟨94,385085744,385085963⟩,
⟨128,526900599,526900900⟩]
theorem checked24228 : checkPrefixCuts (2^48) 3179544577 9 Manual.Count131072.C024228.packed 128 cuts24228 = true := by
 decide +kernel
def pointBounds24228 : List (Nat × Nat × Nat) := [(3179640832,102495712120492,102496093910454)]
theorem point_links_checked24228 : (cuts24228.take 1).map (fun c => (3179544577-1+2*2^9*c.k,102495327034748+c.lower,102495708824491+c.upper)) = pointBounds24228 := by
 decide +kernel
def cuts24229 : List PrefixCut := [⟨64,264592947,264593096⟩,
⟨128,533517958,533518255⟩]
theorem checked24229 : checkPrefixCuts (2^48) 3179675649 9 Manual.Count131072.C024229.packed 128 cuts24229 = true := by
 decide +kernel
def pointBounds24229 : List (Nat × Nat × Nat) := [(3179741184,102496118528294,102496500318487)]
theorem point_links_checked24229 : (cuts24229.take 1).map (fun c => (3179675649-1+2*2^9*c.k,102495853935347+c.lower,102496235725391+c.upper)) = pointBounds24229 := by
 decide +kernel
def cuts24230 : List PrefixCut := [⟨34,138001128,138001205⟩,
⟨128,527742319,527742613⟩]
theorem checked24230 : checkPrefixCuts (2^48) 3179806721 9 Manual.Count131072.C024230.packed 128 cuts24230 = true := by
 decide +kernel
def pointBounds24230 : List (Nat × Nat × Nat) := [(3179841536,102496525454433,102496907244851)]
theorem point_links_checked24230 : (cuts24230.take 1).map (fun c => (3179806721-1+2*2^9*c.k,102496387453305+c.lower,102496769243646+c.upper)) = pointBounds24230 := by
 decide +kernel
def cuts24231 : List PrefixCut := [⟨4,16109874,16109884⟩,
⟨102,425842665,425842906⟩,
⟨128,530641549,530641851⟩]
theorem checked24231 : checkPrefixCuts (2^48) 3179937793 9 Manual.Count131072.C024231.packed 128 cuts24231 = true := by
 decide +kernel
def pointBounds24231 : List (Nat × Nat × Nat) := [(3179941888,102496931305498,102497313096143),(3180042240,102497341038289,102497722829165)]
theorem point_links_checked24231 : (cuts24231.take 2).map (fun c => (3179937793-1+2*2^9*c.k,102496915195624+c.lower,102497296986259+c.upper)) = pointBounds24231 := by
 decide +kernel
def cuts24232 : List PrefixCut := [⟨72,301646082,301646255⟩,
⟨128,534779693,534779990⟩]
theorem checked24232 : checkPrefixCuts (2^48) 3180068865 9 Manual.Count131072.C024232.packed 128 cuts24232 = true := by
 decide +kernel
def pointBounds24232 : List (Nat × Nat × Nat) := [(3180142592,102497747483255,102498129274365)]
theorem point_links_checked24232 : (cuts24232.take 1).map (fun c => (3180068865-1+2*2^9*c.k,102497445837173+c.lower,102497827628110+c.upper)) = pointBounds24232 := by
 decide +kernel
def cuts24233 : List PrefixCut := [⟨42,173210068,173210171⟩,
⟨128,526615081,526615385⟩]
theorem checked24233 : checkPrefixCuts (2^48) 3180199937 9 Manual.Count131072.C024233.packed 128 cuts24233 = true := by
 decide +kernel
def pointBounds24233 : List (Nat × Nat × Nat) := [(3180242944,102498153826934,102498535618271)]
theorem point_links_checked24233 : (cuts24233.take 1).map (fun c => (3180199937-1+2*2^9*c.k,102497980616866+c.lower,102498362408100+c.upper)) = pointBounds24233 := by
 decide +kernel
def cuts24234 : List PrefixCut := [⟨12,47881062,47881088⟩,
⟨110,457916201,457916461⟩,
⟨128,534558509,534558812⟩]
theorem checked24234 : checkPrefixCuts (2^48) 3180331009 9 Manual.Count131072.C024234.packed 128 cuts24234 = true := by
 decide +kernel
def pointBounds24234 : List (Nat × Nat × Nat) := [(3180343296,102498555113009,102498936904573),(3180443648,102498965148148,102499346939946)]
theorem point_links_checked24234 : (cuts24234.take 2).map (fun c => (3180331009-1+2*2^9*c.k,102498507231947+c.lower,102498889023485+c.upper)) = pointBounds24234 := by
 decide +kernel
def cuts24235 : List PrefixCut := [⟨80,326742472,326742657⟩,
⟨128,524447675,524447970⟩]
theorem checked24235 : checkPrefixCuts (2^48) 3180462081 9 Manual.Count131072.C024235.packed 128 cuts24235 = true := by
 decide +kernel
def pointBounds24235 : List (Nat × Nat × Nat) := [(3180544000,102499368532928,102499750324954)]
theorem point_links_checked24235 : (cuts24235.take 1).map (fun c => (3180462081-1+2*2^9*c.k,102499041790456+c.lower,102499423582297+c.upper)) = pointBounds24235 := by
 decide +kernel
def cuts24236 : List PrefixCut := [⟨50,202303893,202304009⟩,
⟨128,529293204,529293511⟩]
theorem checked24236 : checkPrefixCuts (2^48) 3180593153 9 Manual.Count131072.C024236.packed 128 cuts24236 = true := by
 decide +kernel
def pointBounds24236 : List (Nat × Nat × Nat) := [(3180644352,102499768542024,102500150334276)]
theorem point_links_checked24236 : (cuts24236.take 1).map (fun c => (3180593153-1+2*2^9*c.k,102499566238131+c.lower,102499948030267+c.upper)) = pointBounds24236 := by
 decide +kernel
def cuts24237 : List PrefixCut := [⟨20,81679663,81679708⟩,
⟨118,485203137,485203415⟩,
⟨128,525643279,525643579⟩]
theorem checked24237 : checkPrefixCuts (2^48) 3180724225 9 Manual.Count131072.C024237.packed 128 cuts24237 = true := by
 decide +kernel
def pointBounds24237 : List (Nat × Nat × Nat) := [(3180744704,102500177210998,102500559003486),(3180845056,102500580734472,102500962527193)]
theorem point_links_checked24237 : (cuts24237.take 2).map (fun c => (3180724225-1+2*2^9*c.k,102500095531335+c.lower,102500477323778+c.upper)) = pointBounds24237 := by
 decide +kernel
def cuts24238 : List PrefixCut := [⟨88,366433192,366433389⟩,
⟨128,526064185,526064473⟩]
theorem checked24238 : checkPrefixCuts (2^48) 3180855297 9 Manual.Count131072.C024238.packed 128 cuts24238 = true := by
 decide +kernel
def pointBounds24238 : List (Nat × Nat × Nat) := [(3180945408,102500987607806,102501369400746)]
theorem point_links_checked24238 : (cuts24238.take 1).map (fun c => (3180855297-1+2*2^9*c.k,102500621174614+c.lower,102501002967357+c.upper)) = pointBounds24238 := by
 decide +kernel
def cuts24239 : List PrefixCut := [⟨58,241123971,241124108⟩,
⟨128,534890942,534891242⟩]
theorem checked24239 : checkPrefixCuts (2^48) 3180986369 9 Manual.Count131072.C024239.packed 128 cuts24239 = true := by
 decide +kernel
def pointBounds24239 : List (Nat × Nat × Nat) := [(3181045760,102501388362770,102501770155938)]
theorem point_links_checked24239 : (cuts24239.take 1).map (fun c => (3180986369-1+2*2^9*c.k,102501147238799+c.lower,102501529031830+c.upper)) = pointBounds24239 := by
 decide +kernel
def cuts24240 : List PrefixCut := [⟨28,115115891,115115955⟩,
⟨126,514872266,514872548⟩,
⟨128,523985645,523985932⟩]
theorem checked24240 : checkPrefixCuts (2^48) 3181117441 9 Manual.Count131072.C024240.packed 128 cuts24240 = true := by
 decide +kernel
def pointBounds24240 : List (Nat × Nat × Nat) := [(3181146112,102501797245632,102502179039027),(3181246464,102502197002007,102502578795620)]
theorem point_links_checked24240 : (cuts24240.take 2).map (fun c => (3181117441-1+2*2^9*c.k,102501682129741+c.lower,102502063923072+c.upper)) = pointBounds24240 := by
 decide +kernel
def cuts24241 : List PrefixCut := [⟨96,393550228,393550452⟩,
⟨128,527945562,527945863⟩]
theorem checked24241 : checkPrefixCuts (2^48) 3181248513 9 Manual.Count131072.C024241.packed 128 cuts24241 = true := by
 decide +kernel
def pointBounds24241 : List (Nat × Nat × Nat) := [(3181346816,102502599665614,102502981459456)]
theorem point_links_checked24241 : (cuts24241.take 1).map (fun c => (3181248513-1+2*2^9*c.k,102502206115386+c.lower,102502587909004+c.upper)) = pointBounds24241 := by
 decide +kernel
def cuts24242 : List PrefixCut := [⟨66,273387090,273387248⟩,
⟨128,531816619,531816923⟩]
theorem checked24242 : checkPrefixCuts (2^48) 3181379585 9 Manual.Count131072.C024242.packed 128 cuts24242 = true := by
 decide +kernel
def pointBounds24242 : List (Nat × Nat × Nat) := [(3181447168,102503007448038,102503389242115)]
theorem point_links_checked24242 : (cuts24242.take 1).map (fun c => (3181379585-1+2*2^9*c.k,102502734060948+c.lower,102503115854867+c.upper)) = pointBounds24242 := by
 decide +kernel
def cuts24243 : List PrefixCut := [⟨36,150047821,150047903⟩,
⟨128,532414065,532414363⟩]
theorem checked24243 : checkPrefixCuts (2^48) 3181510657 9 Manual.Count131072.C024243.packed 128 cuts24243 = true := by
 decide +kernel
def pointBounds24243 : List (Nat × Nat × Nat) := [(3181547520,102503415925388,102503797719693)]
theorem point_links_checked24243 : (cuts24243.take 1).map (fun c => (3181510657-1+2*2^9*c.k,102503265877567+c.lower,102503647671790+c.upper)) = pointBounds24243 := by
 decide +kernel
def cuts24244 : List PrefixCut := [⟨6,24594205,24594218⟩,
⟨104,429949437,429949682⟩,
⟨128,528499606,528499903⟩]
theorem checked24244 : checkPrefixCuts (2^48) 3181641729 9 Manual.Count131072.C024244.packed 128 cuts24244 = true := by
 decide +kernel
def pointBounds24244 : List (Nat × Nat × Nat) := [(3181647872,102503822885837,102504204680371),(3181748224,102504228241069,102504610035835)]
theorem point_links_checked24244 : (cuts24244.take 2).map (fun c => (3181641729-1+2*2^9*c.k,102503798291632+c.lower,102504180086153+c.upper)) = pointBounds24244 := by
 decide +kernel
def cuts24245 : List PrefixCut := [⟨74,308207676,308207852⟩,
⟨128,530689409,530689715⟩]
theorem checked24245 : checkPrefixCuts (2^48) 3181772801 9 Manual.Count131072.C024245.packed 128 cuts24245 = true := by
 decide +kernel
def pointBounds24245 : List (Nat × Nat × Nat) := [(3181848576,102504634998914,102505016793908)]
theorem point_links_checked24245 : (cuts24245.take 1).map (fun c => (3181772801-1+2*2^9*c.k,102504326791238+c.lower,102504708586056+c.upper)) = pointBounds24245 := by
 decide +kernel
def cuts24246 : List PrefixCut := [⟨44,182936382,182936483⟩,
⟨128,526333070,526333369⟩]
theorem checked24246 : checkPrefixCuts (2^48) 3181903873 9 Manual.Count131072.C024246.packed 128 cuts24246 = true := by
 decide +kernel
def pointBounds24246 : List (Nat × Nat × Nat) := [(3181948928,102505040417029,102505422212254)]
theorem point_links_checked24246 : (cuts24246.take 1).map (fun c => (3181903873-1+2*2^9*c.k,102504857480647+c.lower,102505239275771+c.upper)) = pointBounds24246 := by
 decide +kernel
def cuts24247 : List PrefixCut := [⟨14,59708686,59708718⟩,
⟨112,456963362,456963621⟩,
⟨128,522507842,522508139⟩]
theorem checked24247 : checkPrefixCuts (2^48) 3182034945 9 Manual.Count131072.C024247.packed 128 cuts24247 = true := by
 decide +kernel
def pointBounds24247 : List (Nat × Nat × Nat) := [(3182049280,102505443522403,102505825317858),(3182149632,102505840777079,102506222572761)]
theorem point_links_checked24247 : (cuts24247.take 2).map (fun c => (3182034945-1+2*2^9*c.k,102505383813717+c.lower,102505765609140+c.upper)) = pointBounds24247 := by
 decide +kernel
def cuts24248 : List PrefixCut := [⟨82,336739447,336739639⟩,
⟨128,532127446,532127749⟩]
theorem checked24248 : checkPrefixCuts (2^48) 3182166017 9 Manual.Count131072.C024248.packed 128 cuts24248 = true := by
 decide +kernel
def pointBounds24248 : List (Nat × Nat × Nat) := [(3182249984,102506243061006,102506624856918)]
theorem point_links_checked24248 : (cuts24248.take 1).map (fun c => (3182166017-1+2*2^9*c.k,102505906321559+c.lower,102506288117279+c.upper)) = pointBounds24248 := by
 decide +kernel
def cuts24249 : List PrefixCut := [⟨52,215905201,215905320⟩,
⟨128,528744538,528744842⟩]
theorem checked24249 : checkPrefixCuts (2^48) 3182297089 9 Manual.Count131072.C024249.packed 128 cuts24249 = true := by
 decide +kernel
def pointBounds24249 : List (Nat × Nat × Nat) := [(3182350336,102506654354206,102507036150348)]
theorem point_links_checked24249 : (cuts24249.take 1).map (fun c => (3182297089-1+2*2^9*c.k,102506438449005+c.lower,102506820245028+c.upper)) = pointBounds24249 := by
 decide +kernel
def cuts24250 : List PrefixCut := [⟨22,91364998,91365050⟩,
⟨120,500067324,500067599⟩,
⟨128,532791254,532791547⟩]
theorem checked24250 : checkPrefixCuts (2^48) 3182428161 9 Manual.Count131072.C024250.packed 128 cuts24250 = true := by
 decide +kernel
def pointBounds24250 : List (Nat × Nat × Nat) := [(3182450688,102507058558541,102507440354920),(3182551040,102507467260867,102507849057469)]
theorem point_links_checked24250 : (cuts24250.take 2).map (fun c => (3182428161-1+2*2^9*c.k,102506967193543+c.lower,102507348989870+c.upper)) = pointBounds24250 := by
 decide +kernel
def cuts24251 : List PrefixCut := [⟨90,364821828,364822039⟩,
⟨128,521625664,521625966⟩]
theorem checked24251 : checkPrefixCuts (2^48) 3182559233 9 Manual.Count131072.C024251.packed 128 cuts24251 = true := by
 decide +kernel
def pointBounds24251 : List (Nat × Nat × Nat) := [(3182651392,102507864806625,102508246603456)]
theorem point_links_checked24251 : (cuts24251.take 1).map (fun c => (3182559233-1+2*2^9*c.k,102507499984797+c.lower,102507881781417+c.upper)) = pointBounds24251 := by
 decide +kernel
def cuts24252 : List PrefixCut := [⟨60,253464583,253464724⟩,
⟨128,534339285,534339587⟩]
theorem checked24252 : checkPrefixCuts (2^48) 3182690305 9 Manual.Count131072.C024252.packed 128 cuts24252 = true := by
 decide +kernel
def pointBounds24252 : List (Nat × Nat × Nat) := [(3182751744,102508275075044,102508656872107)]
theorem point_links_checked24252 : (cuts24252.take 1).map (fun c => (3182690305-1+2*2^9*c.k,102508021610461+c.lower,102508403407383+c.upper)) = pointBounds24252 := by
 decide +kernel
def cuts24253 : List PrefixCut := [⟨30,125401160,125401229⟩,
⟨128,527507913,527508210⟩]
theorem checked24253 : checkPrefixCuts (2^48) 3182821377 9 Manual.Count131072.C024253.packed 128 cuts24253 = true := by
 decide +kernel
def pointBounds24253 : List (Nat × Nat × Nat) := [(3182852096,102508681350906,102509063148199),(3182952448,102509083457659,102509465255180)]
theorem point_links_checked24253 : (cuts24253.take 2).map (fun c => (3182821377-1+2*2^9*c.k,102508555949746+c.lower,102508937746970+c.upper)) = pointBounds24253 := by
 decide +kernel
def cuts24254 : List PrefixCut := [⟨98,410229700,410229933⟩,
⟨128,534737456,534737761⟩]
theorem checked24254 : checkPrefixCuts (2^48) 3182952449 9 Manual.Count131072.C024254.packed 128 cuts24254 = true := by
 decide +kernel
def pointBounds24254 : List (Nat × Nat × Nat) := [(3183052800,102509493687359,102509875485113)]
theorem point_links_checked24254 : (cuts24254.take 1).map (fun c => (3182952449-1+2*2^9*c.k,102509083457659+c.lower,102509465255180+c.upper)) = pointBounds24254 := by
 decide +kernel
def cuts24255 : List PrefixCut := [⟨68,276600950,276601107⟩,
⟨128,529321263,529321564⟩]
theorem checked24255 : checkPrefixCuts (2^48) 3183083521 9 Manual.Count131072.C024255.packed 128 cuts24255 = true := by
 decide +kernel
def pointBounds24255 : List (Nat × Nat × Nat) := [(3183153152,102509894796065,102510276594048)]
theorem point_links_checked24255 : (cuts24255.take 1).map (fun c => (3183083521-1+2*2^9*c.k,102509618195115+c.lower,102509999992941+c.upper)) = pointBounds24255 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000132
