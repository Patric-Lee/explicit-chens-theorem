import PlattAssemblyKernel
import PlattCertificates.Count131072.C057392
import PlattCertificates.Count131072.C057393
import PlattCertificates.Count131072.C057394
import PlattCertificates.Count131072.C057395
import PlattCertificates.Count131072.C057396
import PlattCertificates.Count131072.C057397
import PlattCertificates.Count131072.C057398
import PlattCertificates.Count131072.C057399
import PlattCertificates.Count131072.C057400
import PlattCertificates.Count131072.C057401
import PlattCertificates.Count131072.C057402
import PlattCertificates.Count131072.C057403
import PlattCertificates.Count131072.C057404
import PlattCertificates.Count131072.C057405
import PlattCertificates.Count131072.C057406
import PlattCertificates.Count131072.C057407
import PlattCertificates.Count131072.C057408
import PlattCertificates.Count131072.C057409
import PlattCertificates.Count131072.C057410
import PlattCertificates.Count131072.C057411
import PlattCertificates.Count131072.C057412
import PlattCertificates.Count131072.C057413
import PlattCertificates.Count131072.C057414
import PlattCertificates.Count131072.C057415
import PlattCertificates.Count131072.C057416
import PlattCertificates.Count131072.C057417
import PlattCertificates.Count131072.C057418
import PlattCertificates.Count131072.C057419
import PlattCertificates.Count131072.C057420
import PlattCertificates.Count131072.C057421
import PlattCertificates.Count131072.C057422
import PlattCertificates.Count131072.C057423
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000231
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57392 : List PrefixCut := [⟨64,214477181,214477305⟩]
theorem checked57392 : checkPrefixCuts (2^48) 7526416385 10 Manual.Count131072.C057392.packed 64 cuts57392 = true := by
 decide +kernel
def cuts57393 : List PrefixCut := [⟨39,130180392,130180467⟩,
⟨64,214510820,214510942⟩]
theorem checked57393 : checkPrefixCuts (2^48) 7526547457 10 Manual.Count131072.C057393.packed 64 cuts57393 = true := by
 decide +kernel
def pointBounds57393 : List (Nat × Nat × Nat) := [(7526627328,113367986836303,113368374930535)]
theorem point_links_checked57393 : (cuts57393.take 1).map (fun c => (7526547457-1+2*2^10*c.k,113367856655911+c.lower,113368244750068+c.upper)) = pointBounds57393 := by
 decide +kernel
def cuts57394 : List PrefixCut := [⟨64,215292424,215292539⟩]
theorem checked57394 : checkPrefixCuts (2^48) 7526678529 10 Manual.Count131072.C057394.packed 64 cuts57394 = true := by
 decide +kernel
def cuts57395 : List PrefixCut := [⟨26,85599848,85599896⟩,
⟨64,212708348,212708467⟩]
theorem checked57395 : checkPrefixCuts (2^48) 7526809601 10 Manual.Count131072.C057395.packed 64 cuts57395 = true := by
 decide +kernel
def pointBounds57395 : List (Nat × Nat × Nat) := [(7526862848,113368372059003,113368760153445)]
theorem point_links_checked57395 : (cuts57395.take 1).map (fun c => (7526809601-1+2*2^10*c.k,113368286459155+c.lower,113368674553549+c.upper)) = pointBounds57395 := by
 decide +kernel
def cuts57396 : List PrefixCut := [⟨64,217902596,217902717⟩]
theorem checked57396 : checkPrefixCuts (2^48) 7526940673 10 Manual.Count131072.C057396.packed 64 cuts57396 = true := by
 decide +kernel
def cuts57397 : List PrefixCut := [⟨13,42966783,42966809⟩,
⟨64,216664771,216664900⟩]
theorem checked57397 : checkPrefixCuts (2^48) 7527071745 10 Manual.Count131072.C057397.packed 64 cuts57397 = true := by
 decide +kernel
def pointBounds57397 : List (Nat × Nat × Nat) := [(7527098368,113368760036882,113369148131542)]
theorem point_links_checked57397 : (cuts57397.take 1).map (fun c => (7527071745-1+2*2^10*c.k,113368717070099+c.lower,113369105164733+c.upper)) = pointBounds57397 := by
 decide +kernel
def cuts57398 : List PrefixCut := [⟨64,213071165,213071289⟩]
theorem checked57398 : checkPrefixCuts (2^48) 7527202817 10 Manual.Count131072.C057398.packed 64 cuts57398 = true := by
 decide +kernel
def pointBounds57398 : List (Nat × Nat × Nat) := [(7527333888,113369146806035,113369534900922)]
theorem point_links_checked57398 : (cuts57398.take 1).map (fun c => (7527202817-1+2*2^10*c.k,113368933734870+c.lower,113369321829633+c.upper)) = pointBounds57398 := by
 decide +kernel
def cuts57399 : List PrefixCut := [⟨64,215647616,215647739⟩]
theorem checked57399 : checkPrefixCuts (2^48) 7527333889 10 Manual.Count131072.C057399.packed 64 cuts57399 = true := by
 decide +kernel
def cuts57400 : List PrefixCut := [⟨51,174512182,174512281⟩,
⟨64,218186585,218186710⟩]
theorem checked57400 : checkPrefixCuts (2^48) 7527464961 10 Manual.Count131072.C057400.packed 64 cuts57400 = true := by
 decide +kernel
def pointBounds57400 : List (Nat × Nat × Nat) := [(7527569408,113369536965833,113369925060942)]
theorem point_links_checked57400 : (cuts57400.take 1).map (fun c => (7527464961-1+2*2^10*c.k,113369362453651+c.lower,113369750548661+c.upper)) = pointBounds57400 := by
 decide +kernel
def cuts57401 : List PrefixCut := [⟨64,215266180,215266306⟩]
theorem checked57401 : checkPrefixCuts (2^48) 7527596033 10 Manual.Count131072.C057401.packed 64 cuts57401 = true := by
 decide +kernel
def cuts57402 : List PrefixCut := [⟨38,127355644,127355715⟩,
⟨64,214065909,214066031⟩]
theorem checked57402 : checkPrefixCuts (2^48) 7527727105 10 Manual.Count131072.C057402.packed 64 cuts57402 = true := by
 decide +kernel
def pointBounds57402 : List (Nat × Nat × Nat) := [(7527804928,113369923262060,113370311357392)]
theorem point_links_checked57402 : (cuts57402.take 1).map (fun c => (7527727105-1+2*2^10*c.k,113369795906416+c.lower,113370184001677+c.upper)) = pointBounds57402 := by
 decide +kernel
def cuts57403 : List PrefixCut := [⟨64,216193449,216193573⟩]
theorem checked57403 : checkPrefixCuts (2^48) 7527858177 10 Manual.Count131072.C057403.packed 64 cuts57403 = true := by
 decide +kernel
def cuts57404 : List PrefixCut := [⟨25,83492589,83492638⟩,
⟨64,214394966,214395091⟩]
theorem checked57404 : checkPrefixCuts (2^48) 7527989249 10 Manual.Count131072.C057404.packed 64 cuts57404 = true := by
 decide +kernel
def pointBounds57404 : List (Nat × Nat × Nat) := [(7528040448,113370309658363,113370697753919)]
theorem point_links_checked57404 : (cuts57404.take 1).map (fun c => (7527989249-1+2*2^10*c.k,113370226165774+c.lower,113370614261281+c.upper)) = pointBounds57404 := by
 decide +kernel
def cuts57405 : List PrefixCut := [⟨64,213867778,213867903⟩]
theorem checked57405 : checkPrefixCuts (2^48) 7528120321 10 Manual.Count131072.C057405.packed 64 cuts57405 = true := by
 decide +kernel
def cuts57406 : List PrefixCut := [⟨12,40866270,40866293⟩,
⟨64,214761395,214761514⟩]
theorem checked57406 : checkPrefixCuts (2^48) 7528251393 10 Manual.Count131072.C057406.packed 64 cuts57406 = true := by
 decide +kernel
def pointBounds57406 : List (Nat × Nat × Nat) := [(7528275968,113370695294788,113371083390568)]
theorem point_links_checked57406 : (cuts57406.take 1).map (fun c => (7528251393-1+2*2^10*c.k,113370654428518+c.lower,113371042524275+c.upper)) = pointBounds57406 := by
 decide +kernel
def cuts57407 : List PrefixCut := [⟨63,210084166,210084283⟩,
⟨64,213411685,213411804⟩]
theorem checked57407 : checkPrefixCuts (2^48) 7528382465 10 Manual.Count131072.C057407.packed 64 cuts57407 = true := by
 decide +kernel
def pointBounds57407 : List (Nat × Nat × Nat) := [(7528511488,113371079274079,113371467370072)]
theorem point_links_checked57407 : (cuts57407.take 1).map (fun c => (7528382465-1+2*2^10*c.k,113370869189913+c.lower,113371257285789+c.upper)) = pointBounds57407 := by
 decide +kernel
def cuts57408 : List PrefixCut := [⟨64,216137266,216137388⟩]
theorem checked57408 : checkPrefixCuts (2^48) 7528513537 10 Manual.Count131072.C057408.packed 64 cuts57408 = true := by
 decide +kernel
def cuts57409 : List PrefixCut := [⟨50,168914190,168914286⟩,
⟨64,215236205,215236327⟩]
theorem checked57409 : checkPrefixCuts (2^48) 7528644609 10 Manual.Count131072.C057409.packed 64 cuts57409 = true := by
 decide +kernel
def pointBounds57409 : List (Nat × Nat × Nat) := [(7528747008,113371467653054,113371855749267)]
theorem point_links_checked57409 : (cuts57409.take 1).map (fun c => (7528644609-1+2*2^10*c.k,113371298738864+c.lower,113371686834981+c.upper)) = pointBounds57409 := by
 decide +kernel
def cuts57410 : List PrefixCut := [⟨64,219569261,219569384⟩]
theorem checked57410 : checkPrefixCuts (2^48) 7528775681 10 Manual.Count131072.C057410.packed 64 cuts57410 = true := by
 decide +kernel
def cuts57411 : List PrefixCut := [⟨37,125578579,125578648⟩,
⟨64,217060606,217060727⟩]
theorem checked57411 : checkPrefixCuts (2^48) 7528906753 10 Manual.Count131072.C057411.packed 64 cuts57411 = true := by
 decide +kernel
def pointBounds57411 : List (Nat × Nat × Nat) := [(7528982528,113371859122909,113372247219340)]
theorem point_links_checked57411 : (cuts57411.take 1).map (fun c => (7528906753-1+2*2^10*c.k,113371733544330+c.lower,113372121640692+c.upper)) = pointBounds57411 := by
 decide +kernel
def cuts57412 : List PrefixCut := [⟨64,216159590,216159710⟩]
theorem checked57412 : checkPrefixCuts (2^48) 7529037825 10 Manual.Count131072.C057412.packed 64 cuts57412 = true := by
 decide +kernel
def cuts57413 : List PrefixCut := [⟨24,81124298,81124343⟩,
⟨64,214996924,214997048⟩]
theorem checked57413 : checkPrefixCuts (2^48) 7529168897 10 Manual.Count131072.C057413.packed 64 cuts57413 = true := by
 decide +kernel
def pointBounds57413 : List (Nat × Nat × Nat) := [(7529218048,113372247888824,113372635985472)]
theorem point_links_checked57413 : (cuts57413.take 1).map (fun c => (7529168897-1+2*2^10*c.k,113372166764526+c.lower,113372554861129+c.upper)) = pointBounds57413 := by
 decide +kernel
def cuts57414 : List PrefixCut := [⟨64,212488467,212488589⟩]
theorem checked57414 : checkPrefixCuts (2^48) 7529299969 10 Manual.Count131072.C057414.packed 64 cuts57414 = true := by
 decide +kernel
def cuts57415 : List PrefixCut := [⟨11,36448652,36448671⟩,
⟨64,216409976,216410097⟩]
theorem checked57415 : checkPrefixCuts (2^48) 7529431041 10 Manual.Count131072.C057415.packed 64 cuts57415 = true := by
 decide +kernel
def pointBounds57415 : List (Nat × Nat × Nat) := [(7529453568,113372630698569,113373018795437)]
theorem point_links_checked57415 : (cuts57415.take 1).map (fun c => (7529431041-1+2*2^10*c.k,113372594249917+c.lower,113372982346766+c.upper)) = pointBounds57415 := by
 decide +kernel
def cuts57416 : List PrefixCut := [⟨62,206051371,206051489⟩,
⟨64,212817512,212817634⟩]
theorem checked57416 : checkPrefixCuts (2^48) 7529562113 10 Manual.Count131072.C057416.packed 64 cuts57416 = true := by
 decide +kernel
def pointBounds57416 : List (Nat × Nat × Nat) := [(7529689088,113373016711264,113373404808352)]
theorem point_links_checked57416 : (cuts57416.take 1).map (fun c => (7529562113-1+2*2^10*c.k,113372810659893+c.lower,113373198756863+c.upper)) = pointBounds57416 := by
 decide +kernel
def cuts57417 : List PrefixCut := [⟨64,217486503,217486620⟩]
theorem checked57417 : checkPrefixCuts (2^48) 7529693185 10 Manual.Count131072.C057417.packed 64 cuts57417 = true := by
 decide +kernel
def cuts57418 : List PrefixCut := [⟨49,166794410,166794503⟩,
⟨64,217370584,217370703⟩]
theorem checked57418 : checkPrefixCuts (2^48) 7529824257 10 Manual.Count131072.C057418.packed 64 cuts57418 = true := by
 decide +kernel
def pointBounds57418 : List (Nat × Nat × Nat) := [(7529924608,113373407758318,113373795855620)]
theorem point_links_checked57418 : (cuts57418.take 1).map (fun c => (7529824257-1+2*2^10*c.k,113373240963908+c.lower,113373629061117+c.upper)) = pointBounds57418 := by
 decide +kernel
def cuts57419 : List PrefixCut := [⟨64,216880862,216880985⟩]
theorem checked57419 : checkPrefixCuts (2^48) 7529955329 10 Manual.Count131072.C057419.packed 64 cuts57419 = true := by
 decide +kernel
def cuts57420 : List PrefixCut := [⟨36,116998934,116999003⟩,
⟨64,209700162,209700283⟩]
theorem checked57420 : checkPrefixCuts (2^48) 7530086401 10 Manual.Count131072.C057420.packed 64 cuts57420 = true := by
 decide +kernel
def pointBounds57420 : List (Nat × Nat × Nat) := [(7530160128,113373792214288,113374180311808)]
theorem point_links_checked57420 : (cuts57420.take 1).map (fun c => (7530086401-1+2*2^10*c.k,113373675215354+c.lower,113374063312805+c.upper)) = pointBounds57420 := by
 decide +kernel
def cuts57421 : List PrefixCut := [⟨64,216611620,216611746⟩]
theorem checked57421 : checkPrefixCuts (2^48) 7530217473 10 Manual.Count131072.C057421.packed 64 cuts57421 = true := by
 decide +kernel
def cuts57422 : List PrefixCut := [⟨23,75691698,75691744⟩,
⟨64,212982161,212982285⟩]
theorem checked57422 : checkPrefixCuts (2^48) 7530348545 10 Manual.Count131072.C057422.packed 64 cuts57422 = true := by
 decide +kernel
def pointBounds57422 : List (Nat × Nat × Nat) := [(7530395648,113374177218834,113374565316578)]
theorem point_links_checked57422 : (cuts57422.take 1).map (fun c => (7530348545-1+2*2^10*c.k,113374101527136+c.lower,113374489624834+c.upper)) = pointBounds57422 := by
 decide +kernel
def cuts57423 : List PrefixCut := [⟨64,215781786,215781909⟩]
theorem checked57423 : checkPrefixCuts (2^48) 7530479617 10 Manual.Count131072.C057423.packed 64 cuts57423 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000231
