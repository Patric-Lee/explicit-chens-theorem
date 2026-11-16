import PlattAssemblyKernel
import PlattCertificates.Count131072.C065216
import PlattCertificates.Count131072.C065217
import PlattCertificates.Count131072.C065218
import PlattCertificates.Count131072.C065219
import PlattCertificates.Count131072.C065220
import PlattCertificates.Count131072.C065221
import PlattCertificates.Count131072.C065222
import PlattCertificates.Count131072.C065223
import PlattCertificates.Count131072.C065224
import PlattCertificates.Count131072.C065225
import PlattCertificates.Count131072.C065226
import PlattCertificates.Count131072.C065227
import PlattCertificates.Count131072.C065228
import PlattCertificates.Count131072.C065229
import PlattCertificates.Count131072.C065230
import PlattCertificates.Count131072.C065231
import PlattCertificates.Count131072.C065232
import PlattCertificates.Count131072.C065233
import PlattCertificates.Count131072.C065234
import PlattCertificates.Count131072.C065235
import PlattCertificates.Count131072.C065236
import PlattCertificates.Count131072.C065237
import PlattCertificates.Count131072.C065238
import PlattCertificates.Count131072.C065239
import PlattCertificates.Count131072.C065240
import PlattCertificates.Count131072.C065241
import PlattCertificates.Count131072.C065242
import PlattCertificates.Count131072.C065243
import PlattCertificates.Count131072.C065244
import PlattCertificates.Count131072.C065245
import PlattCertificates.Count131072.C065246
import PlattCertificates.Count131072.C065247
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000163
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65216 : List PrefixCut := [⟨64,191292594,191292700⟩]
theorem checked65216 : checkPrefixCuts (2^48) 8551923713 10 Manual.Count131072.C065216.packed 64 cuts65216 = true := by
 decide +kernel
def cuts65217 : List PrefixCut := [⟨63,182896894,182897008⟩,
⟨64,185957769,185957884⟩]
theorem checked65217 : checkPrefixCuts (2^48) 8552054785 10 Manual.Count131072.C065217.packed 64 cuts65217 = true := by
 decide +kernel
def pointBounds65217 : List (Nat × Nat × Nat) := [(8552183808,114944611310153,114945000308094)]
theorem point_links_checked65217 : (cuts65217.take 1).map (fun c => (8552054785-1+2*2^10*c.k,114944428413259+c.lower,114944817411086+c.upper)) = pointBounds65217 := by
 decide +kernel
def cuts65218 : List PrefixCut := [⟨64,188917018,188917134⟩]
theorem checked65218 : checkPrefixCuts (2^48) 8552185857 10 Manual.Count131072.C065218.packed 64 cuts65218 = true := by
 decide +kernel
def cuts65219 : List PrefixCut := [⟨64,189638211,189638320⟩]
theorem checked65219 : checkPrefixCuts (2^48) 8552316929 10 Manual.Count131072.C065219.packed 64 cuts65219 = true := by
 decide +kernel
def cuts65220 : List PrefixCut := [⟨2,6450676,6450680⟩,
⟨64,188516297,188516402⟩]
theorem checked65220 : checkPrefixCuts (2^48) 8552448001 10 Manual.Count131072.C065220.packed 64 cuts65220 = true := by
 decide +kernel
def pointBounds65220 : List (Nat × Nat × Nat) := [(8552452096,114944999376933,114945388375104)]
theorem point_links_checked65220 : (cuts65220.take 1).map (fun c => (8552448001-1+2*2^10*c.k,114944992926257+c.lower,114945381924424+c.upper)) = pointBounds65220 := by
 decide +kernel
def cuts65221 : List PrefixCut := [⟨64,190488072,190488178⟩]
theorem checked65221 : checkPrefixCuts (2^48) 8552579073 10 Manual.Count131072.C065221.packed 64 cuts65221 = true := by
 decide +kernel
def cuts65222 : List PrefixCut := [⟨5,15500888,15500897⟩,
⟨64,190419323,190419437⟩]
theorem checked65222 : checkPrefixCuts (2^48) 8552710145 10 Manual.Count131072.C065222.packed 64 cuts65222 = true := by
 decide +kernel
def pointBounds65222 : List (Nat × Nat × Nat) := [(8552720384,114945387431514,114945776429901)]
theorem point_links_checked65222 : (cuts65222.take 1).map (fun c => (8552710145-1+2*2^10*c.k,114945371930626+c.lower,114945760929004+c.upper)) = pointBounds65222 := by
 decide +kernel
def cuts65223 : List PrefixCut := [⟨64,188145636,188145747⟩]
theorem checked65223 : checkPrefixCuts (2^48) 8552841217 10 Manual.Count131072.C065223.packed 64 cuts65223 = true := by
 decide +kernel
def cuts65224 : List PrefixCut := [⟨8,23925257,23925270⟩,
⟨64,190018577,190018680⟩]
theorem checked65224 : checkPrefixCuts (2^48) 8552972289 10 Manual.Count131072.C065224.packed 64 cuts65224 = true := by
 decide +kernel
def pointBounds65224 : List (Nat × Nat × Nat) := [(8552988672,114945774420842,114946163419458)]
theorem point_links_checked65224 : (cuts65224.take 1).map (fun c => (8552972289-1+2*2^10*c.k,114945750495585+c.lower,114946139494188+c.upper)) = pointBounds65224 := by
 decide +kernel
def cuts65225 : List PrefixCut := [⟨64,189785295,189785409⟩]
theorem checked65225 : checkPrefixCuts (2^48) 8553103361 10 Manual.Count131072.C065225.packed 64 cuts65225 = true := by
 decide +kernel
def cuts65226 : List PrefixCut := [⟨11,32382011,32382033⟩,
⟨64,188301516,188301626⟩]
theorem checked65226 : checkPrefixCuts (2^48) 8553234433 10 Manual.Count131072.C065226.packed 64 cuts65226 = true := by
 decide +kernel
def pointBounds65226 : List (Nat × Nat × Nat) := [(8553256960,114946162681468,114946551680310)]
theorem point_links_checked65226 : (cuts65226.take 1).map (fun c => (8553234433-1+2*2^10*c.k,114946130299457+c.lower,114946519298277+c.upper)) = pointBounds65226 := by
 decide +kernel
def cuts65227 : List PrefixCut := [⟨64,188134089,188134203⟩]
theorem checked65227 : checkPrefixCuts (2^48) 8553365505 10 Manual.Count131072.C065227.packed 64 cuts65227 = true := by
 decide +kernel
def cuts65228 : List PrefixCut := [⟨14,41167316,41167340⟩,
⟨64,188559007,188559112⟩]
theorem checked65228 : checkPrefixCuts (2^48) 8553496577 10 Manual.Count131072.C065228.packed 64 cuts65228 = true := by
 decide +kernel
def pointBounds65228 : List (Nat × Nat × Nat) := [(8553525248,114946547902378,114946936901446)]
theorem point_links_checked65228 : (cuts65228.take 1).map (fun c => (8553496577-1+2*2^10*c.k,114946506735062+c.lower,114946895734106+c.upper)) = pointBounds65228 := by
 decide +kernel
def cuts65229 : List PrefixCut := [⟨64,192175871,192175981⟩]
theorem checked65229 : checkPrefixCuts (2^48) 8553627649 10 Manual.Count131072.C065229.packed 64 cuts65229 = true := by
 decide +kernel
def cuts65230 : List PrefixCut := [⟨17,49458483,49458510⟩,
⟨64,186940823,186940929⟩]
theorem checked65230 : checkPrefixCuts (2^48) 8553758721 10 Manual.Count131072.C065230.packed 64 cuts65230 = true := by
 decide +kernel
def pointBounds65230 : List (Nat × Nat × Nat) := [(8553793536,114946936928423,114947325927709)]
theorem point_links_checked65230 : (cuts65230.take 1).map (fun c => (8553758721-1+2*2^10*c.k,114946887469940+c.lower,114947276469199+c.upper)) = pointBounds65230 := by
 decide +kernel
def cuts65231 : List PrefixCut := [⟨64,187563164,187563271⟩]
theorem checked65231 : checkPrefixCuts (2^48) 8553889793 10 Manual.Count131072.C065231.packed 64 cuts65231 = true := by
 decide +kernel
def cuts65232 : List PrefixCut := [⟨20,59920891,59920927⟩,
⟨64,191278578,191278692⟩]
theorem checked65232 : checkPrefixCuts (2^48) 8554020865 10 Manual.Count131072.C065232.packed 64 cuts65232 = true := by
 decide +kernel
def pointBounds65232 : List (Nat × Nat × Nat) := [(8554061824,114947321894818,114947710894326)]
theorem point_links_checked65232 : (cuts65232.take 1).map (fun c => (8554020865-1+2*2^10*c.k,114947261973927+c.lower,114947650973399+c.upper)) = pointBounds65232 := by
 decide +kernel
def cuts65233 : List PrefixCut := [⟨64,187952279,187952385⟩]
theorem checked65233 : checkPrefixCuts (2^48) 8554151937 10 Manual.Count131072.C065233.packed 64 cuts65233 = true := by
 decide +kernel
def cuts65234 : List PrefixCut := [⟨23,68309675,68309718⟩,
⟨64,188870722,188870832⟩]
theorem checked65234 : checkPrefixCuts (2^48) 8554283009 10 Manual.Count131072.C065234.packed 64 cuts65234 = true := by
 decide +kernel
def pointBounds65234 : List (Nat × Nat × Nat) := [(8554330112,114947709514459,114948098514194)]
theorem point_links_checked65234 : (cuts65234.take 1).map (fun c => (8554283009-1+2*2^10*c.k,114947641204784+c.lower,114948030204476+c.upper)) = pointBounds65234 := by
 decide +kernel
def cuts65235 : List PrefixCut := [⟨64,188802010,188802121⟩]
theorem checked65235 : checkPrefixCuts (2^48) 8554414081 10 Manual.Count131072.C065235.packed 64 cuts65235 = true := by
 decide +kernel
def cuts65236 : List PrefixCut := [⟨26,77454708,77454754⟩,
⟨64,190279761,190279876⟩]
theorem checked65236 : checkPrefixCuts (2^48) 8554545153 10 Manual.Count131072.C065236.packed 64 cuts65236 = true := by
 decide +kernel
def pointBounds65236 : List (Nat × Nat × Nat) := [(8554598400,114948096332224,114948485332183)]
theorem point_links_checked65236 : (cuts65236.take 1).map (fun c => (8554545153-1+2*2^10*c.k,114948018877516+c.lower,114948407877429+c.upper)) = pointBounds65236 := by
 decide +kernel
def cuts65237 : List PrefixCut := [⟨64,188697511,188697623⟩]
theorem checked65237 : checkPrefixCuts (2^48) 8554676225 10 Manual.Count131072.C065237.packed 64 cuts65237 = true := by
 decide +kernel
def cuts65238 : List PrefixCut := [⟨29,85546306,85546356⟩,
⟨64,189944906,189945014⟩]
theorem checked65238 : checkPrefixCuts (2^48) 8554807297 10 Manual.Count131072.C065238.packed 64 cuts65238 = true := by
 decide +kernel
def pointBounds65238 : List (Nat × Nat × Nat) := [(8554866688,114948483401094,114948872401284)]
theorem point_links_checked65238 : (cuts65238.take 1).map (fun c => (8554807297-1+2*2^10*c.k,114948397854788+c.lower,114948786854928+c.upper)) = pointBounds65238 := by
 decide +kernel
def cuts65239 : List PrefixCut := [⟨64,186289911,186290017⟩]
theorem checked65239 : checkPrefixCuts (2^48) 8554938369 10 Manual.Count131072.C065239.packed 64 cuts65239 = true := by
 decide +kernel
def cuts65240 : List PrefixCut := [⟨32,96828844,96828902⟩,
⟨64,191090657,191090767⟩]
theorem checked65240 : checkPrefixCuts (2^48) 8555069441 10 Manual.Count131072.C065240.packed 64 cuts65240 = true := by
 decide +kernel
def pointBounds65240 : List (Nat × Nat × Nat) := [(8555134976,114948870918449,114949259918861)]
theorem point_links_checked65240 : (cuts65240.take 1).map (fun c => (8555069441-1+2*2^10*c.k,114948774089605+c.lower,114949163089959+c.upper)) = pointBounds65240 := by
 decide +kernel
def cuts65241 : List PrefixCut := [⟨64,185988081,185988189⟩]
theorem checked65241 : checkPrefixCuts (2^48) 8555200513 10 Manual.Count131072.C065241.packed 64 cuts65241 = true := by
 decide +kernel
def cuts65242 : List PrefixCut := [⟨35,104886431,104886492⟩,
⟨64,188485674,188485782⟩]
theorem checked65242 : checkPrefixCuts (2^48) 8555331585 10 Manual.Count131072.C065242.packed 64 cuts65242 = true := by
 decide +kernel
def pointBounds65242 : List (Nat × Nat × Nat) := [(8555403264,114949256054774,114949645055407)]
theorem point_links_checked65242 : (cuts65242.take 1).map (fun c => (8555331585-1+2*2^10*c.k,114949151168343+c.lower,114949540168915+c.upper)) = pointBounds65242 := by
 decide +kernel
def cuts65243 : List PrefixCut := [⟨64,188778872,188778975⟩]
theorem checked65243 : checkPrefixCuts (2^48) 8555462657 10 Manual.Count131072.C065243.packed 64 cuts65243 = true := by
 decide +kernel
def cuts65244 : List PrefixCut := [⟨38,110903757,110903821⟩,
⟨64,187657390,187657499⟩]
theorem checked65244 : checkPrefixCuts (2^48) 8555593729 10 Manual.Count131072.C065244.packed 64 cuts65244 = true := by
 decide +kernel
def pointBounds65244 : List (Nat × Nat × Nat) := [(8555671552,114949639336646,114950028337493)]
theorem point_links_checked65244 : (cuts65244.take 1).map (fun c => (8555593729-1+2*2^10*c.k,114949528432889+c.lower,114949917433672+c.upper)) = pointBounds65244 := by
 decide +kernel
def cuts65245 : List PrefixCut := [⟨64,187819025,187819129⟩]
theorem checked65245 : checkPrefixCuts (2^48) 8555724801 10 Manual.Count131072.C065245.packed 64 cuts65245 = true := by
 decide +kernel
def cuts65246 : List PrefixCut := [⟨41,123368804,123368877⟩,
⟨64,190546713,190546828⟩]
theorem checked65246 : checkPrefixCuts (2^48) 8555855873 10 Manual.Count131072.C065246.packed 64 cuts65246 = true := by
 decide +kernel
def pointBounds65246 : List (Nat × Nat × Nat) := [(8555939840,114950027278108,114950416279177)]
theorem point_links_checked65246 : (cuts65246.take 1).map (fun c => (8555855873-1+2*2^10*c.k,114949903909304+c.lower,114950292910300+c.upper)) = pointBounds65246 := by
 decide +kernel
def cuts65247 : List PrefixCut := [⟨64,188306743,188306848⟩]
theorem checked65247 : checkPrefixCuts (2^48) 8555986945 10 Manual.Count131072.C065247.packed 64 cuts65247 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000163
