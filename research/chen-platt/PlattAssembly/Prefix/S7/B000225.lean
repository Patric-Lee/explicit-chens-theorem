import PlattAssemblyKernel
import PlattCertificates.Count131072.C067200
import PlattCertificates.Count131072.C067201
import PlattCertificates.Count131072.C067202
import PlattCertificates.Count131072.C067203
import PlattCertificates.Count131072.C067204
import PlattCertificates.Count131072.C067205
import PlattCertificates.Count131072.C067206
import PlattCertificates.Count131072.C067207
import PlattCertificates.Count131072.C067208
import PlattCertificates.Count131072.C067209
import PlattCertificates.Count131072.C067210
import PlattCertificates.Count131072.C067211
import PlattCertificates.Count131072.C067212
import PlattCertificates.Count131072.C067213
import PlattCertificates.Count131072.C067214
import PlattCertificates.Count131072.C067215
import PlattCertificates.Count131072.C067216
import PlattCertificates.Count131072.C067217
import PlattCertificates.Count131072.C067218
import PlattCertificates.Count131072.C067219
import PlattCertificates.Count131072.C067220
import PlattCertificates.Count131072.C067221
import PlattCertificates.Count131072.C067222
import PlattCertificates.Count131072.C067223
import PlattCertificates.Count131072.C067224
import PlattCertificates.Count131072.C067225
import PlattCertificates.Count131072.C067226
import PlattCertificates.Count131072.C067227
import PlattCertificates.Count131072.C067228
import PlattCertificates.Count131072.C067229
import PlattCertificates.Count131072.C067230
import PlattCertificates.Count131072.C067231
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000225
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67200 : List PrefixCut := [⟨64,180089528,180089633⟩]
theorem checked67200 : checkPrefixCuts (2^48) 8811970561 10 Manual.Count131072.C067200.packed 64 cuts67200 = true := by
 decide +kernel
def cuts67201 : List PrefixCut := [⟨64,182131123,182131224⟩]
theorem checked67201 : checkPrefixCuts (2^48) 8812101633 10 Manual.Count131072.C067201.packed 64 cuts67201 = true := by
 decide +kernel
def cuts67202 : List PrefixCut := [⟨5,14948558,14948567⟩,
⟨64,182383946,182384055⟩]
theorem checked67202 : checkPrefixCuts (2^48) 8812232705 10 Manual.Count131072.C067202.packed 64 cuts67202 = true := by
 decide +kernel
def pointBounds67202 : List (Nat × Nat × Nat) := [(8812242944,115313032088353,115313421300240)]
theorem point_links_checked67202 : (cuts67202.take 1).map (fun c => (8812232705-1+2*2^10*c.k,115313017139795+c.lower,115313406351673+c.upper)) = pointBounds67202 := by
 decide +kernel
def cuts67203 : List PrefixCut := [⟨64,183051972,183052079⟩]
theorem checked67203 : checkPrefixCuts (2^48) 8812363777 10 Manual.Count131072.C067203.packed 64 cuts67203 = true := by
 decide +kernel
def cuts67204 : List PrefixCut := [⟨12,33441586,33441606⟩,
⟨64,183336721,183336829⟩]
theorem checked67204 : checkPrefixCuts (2^48) 8812494849 10 Manual.Count131072.C067204.packed 64 cuts67204 = true := by
 decide +kernel
def pointBounds67204 : List (Nat × Nat × Nat) := [(8812519424,115313416017299,115313805229413)]
theorem point_links_checked67204 : (cuts67204.take 1).map (fun c => (8812494849-1+2*2^10*c.k,115313382575713+c.lower,115313771787807+c.upper)) = pointBounds67204 := by
 decide +kernel
def cuts67205 : List PrefixCut := [⟨64,183014602,183014710⟩]
theorem checked67205 : checkPrefixCuts (2^48) 8812625921 10 Manual.Count131072.C067205.packed 64 cuts67205 = true := by
 decide +kernel
def cuts67206 : List PrefixCut := [⟨19,53690151,53690184⟩,
⟨64,182341150,182341256⟩]
theorem checked67206 : checkPrefixCuts (2^48) 8812756993 10 Manual.Count131072.C067206.packed 64 cuts67206 = true := by
 decide +kernel
def pointBounds67206 : List (Nat × Nat × Nat) := [(8812795904,115313802617187,115314191829530)]
theorem point_links_checked67206 : (cuts67206.take 1).map (fun c => (8812756993-1+2*2^10*c.k,115313748927036+c.lower,115314138139346+c.upper)) = pointBounds67206 := by
 decide +kernel
def cuts67207 : List PrefixCut := [⟨64,181188636,181188746⟩]
theorem checked67207 : checkPrefixCuts (2^48) 8812888065 10 Manual.Count131072.C067207.packed 64 cuts67207 = true := by
 decide +kernel
def cuts67208 : List PrefixCut := [⟨26,74352680,74352723⟩,
⟨64,180994324,180994432⟩]
theorem checked67208 : checkPrefixCuts (2^48) 8813019137 10 Manual.Count131072.C067208.packed 64 cuts67208 = true := by
 decide +kernel
def pointBounds67208 : List (Nat × Nat × Nat) := [(8813072384,115314186809502,115314576022071)]
theorem point_links_checked67208 : (cuts67208.take 1).map (fun c => (8813019137-1+2*2^10*c.k,115314112456822+c.lower,115314501669348+c.upper)) = pointBounds67208 := by
 decide +kernel
def cuts67209 : List PrefixCut := [⟨64,182588512,182588617⟩]
theorem checked67209 : checkPrefixCuts (2^48) 8813150209 10 Manual.Count131072.C067209.packed 64 cuts67209 = true := by
 decide +kernel
def cuts67210 : List PrefixCut := [⟨33,92395069,92395121⟩,
⟨64,180062744,180062844⟩]
theorem checked67210 : checkPrefixCuts (2^48) 8813281281 10 Manual.Count131072.C067210.packed 64 cuts67210 = true := by
 decide +kernel
def pointBounds67210 : List (Nat × Nat × Nat) := [(8813348864,115314568434727,115314957647518)]
theorem point_links_checked67210 : (cuts67210.take 1).map (fun c => (8813281281-1+2*2^10*c.k,115314476039658+c.lower,115314865252397+c.upper)) = pointBounds67210 := by
 decide +kernel
def cuts67211 : List PrefixCut := [⟨64,182774710,182774818⟩]
theorem checked67211 : checkPrefixCuts (2^48) 8813412353 10 Manual.Count131072.C067211.packed 64 cuts67211 = true := by
 decide +kernel
def cuts67212 : List PrefixCut := [⟨40,113598076,113598141⟩,
⟨64,182292944,182293051⟩]
theorem checked67212 : checkPrefixCuts (2^48) 8813543425 10 Manual.Count131072.C067212.packed 64 cuts67212 = true := by
 decide +kernel
def pointBounds67212 : List (Nat × Nat × Nat) := [(8813625344,115314952475188,115315341688200)]
theorem point_links_checked67212 : (cuts67212.take 1).map (fun c => (8813543425-1+2*2^10*c.k,115314838877112+c.lower,115315228090059+c.upper)) = pointBounds67212 := by
 decide +kernel
def cuts67213 : List PrefixCut := [⟨64,184813171,184813275⟩]
theorem checked67213 : checkPrefixCuts (2^48) 8813674497 10 Manual.Count131072.C067213.packed 64 cuts67213 = true := by
 decide +kernel
def cuts67214 : List PrefixCut := [⟨47,133266879,133266958⟩,
⟨64,183053968,183054073⟩]
theorem checked67214 : checkPrefixCuts (2^48) 8813805569 10 Manual.Count131072.C067214.packed 64 cuts67214 = true := by
 decide +kernel
def pointBounds67214 : List (Nat × Nat × Nat) := [(8813901824,115315339250106,115315728463343)]
theorem point_links_checked67214 : (cuts67214.take 1).map (fun c => (8813805569-1+2*2^10*c.k,115315205983227+c.lower,115315595196385+c.upper)) = pointBounds67214 := by
 decide +kernel
def cuts67215 : List PrefixCut := [⟨64,181390633,181390740⟩]
theorem checked67215 : checkPrefixCuts (2^48) 8813936641 10 Manual.Count131072.C067215.packed 64 cuts67215 = true := by
 decide +kernel
def cuts67216 : List PrefixCut := [⟨54,153477358,153477448⟩,
⟨64,180014756,180014863⟩]
theorem checked67216 : checkPrefixCuts (2^48) 8814067713 10 Manual.Count131072.C067216.packed 64 cuts67216 = true := by
 decide +kernel
def pointBounds67216 : List (Nat × Nat × Nat) := [(8814178304,115315723905186,115316113118646)]
theorem point_links_checked67216 : (cuts67216.take 1).map (fun c => (8814067713-1+2*2^10*c.k,115315570427828+c.lower,115315959641198+c.upper)) = pointBounds67216 := by
 decide +kernel
def cuts67217 : List PrefixCut := [⟨64,183620613,183620724⟩]
theorem checked67217 : checkPrefixCuts (2^48) 8814198785 10 Manual.Count131072.C067217.packed 64 cuts67217 = true := by
 decide +kernel
def cuts67218 : List PrefixCut := [⟨61,174836218,174836321⟩,
⟨64,182947281,182947388⟩]
theorem checked67218 : checkPrefixCuts (2^48) 8814329857 10 Manual.Count131072.C067218.packed 64 cuts67218 = true := by
 decide +kernel
def pointBounds67218 : List (Nat × Nat × Nat) := [(8814454784,115316108899415,115316498113106)]
theorem point_links_checked67218 : (cuts67218.take 1).map (fun c => (8814329857-1+2*2^10*c.k,115315934063197+c.lower,115316323276785+c.upper)) = pointBounds67218 := by
 decide +kernel
def cuts67219 : List PrefixCut := [⟨64,184860539,184860639⟩]
theorem checked67219 : checkPrefixCuts (2^48) 8814460929 10 Manual.Count131072.C067219.packed 64 cuts67219 = true := by
 decide +kernel
def cuts67220 : List PrefixCut := [⟨64,180866226,180866330⟩]
theorem checked67220 : checkPrefixCuts (2^48) 8814592001 10 Manual.Count131072.C067220.packed 64 cuts67220 = true := by
 decide +kernel
def cuts67221 : List PrefixCut := [⟨4,11240184,11240192⟩,
⟨64,184599586,184599695⟩]
theorem checked67221 : checkPrefixCuts (2^48) 8814723073 10 Manual.Count131072.C067221.packed 64 cuts67221 = true := by
 decide +kernel
def pointBounds67221 : List (Nat × Nat × Nat) := [(8814731264,115316493977427,115316883191334)]
theorem point_links_checked67221 : (cuts67221.take 1).map (fun c => (8814723073-1+2*2^10*c.k,115316482737243+c.lower,115316871951142+c.upper)) = pointBounds67221 := by
 decide +kernel
def cuts67222 : List PrefixCut := [⟨64,179870957,179871062⟩]
theorem checked67222 : checkPrefixCuts (2^48) 8814854145 10 Manual.Count131072.C067222.packed 64 cuts67222 = true := by
 decide +kernel
def cuts67223 : List PrefixCut := [⟨11,33144760,33144779⟩,
⟨64,185264665,185264778⟩]
theorem checked67223 : checkPrefixCuts (2^48) 8814985217 10 Manual.Count131072.C067223.packed 64 cuts67223 = true := by
 decide +kernel
def pointBounds67223 : List (Nat × Nat × Nat) := [(8815007744,115316880352546,115317269566678)]
theorem point_links_checked67223 : (cuts67223.take 1).map (fun c => (8814985217-1+2*2^10*c.k,115316847207786+c.lower,115317236421899+c.upper)) = pointBounds67223 := by
 decide +kernel
def cuts67224 : List PrefixCut := [⟨64,182196546,182196658⟩]
theorem checked67224 : checkPrefixCuts (2^48) 8815116289 10 Manual.Count131072.C067224.packed 64 cuts67224 = true := by
 decide +kernel
def cuts67225 : List PrefixCut := [⟨18,51056697,51056726⟩,
⟨64,179511707,179511808⟩]
theorem checked67225 : checkPrefixCuts (2^48) 8815247361 10 Manual.Count131072.C067225.packed 64 cuts67225 = true := by
 decide +kernel
def pointBounds67225 : List (Nat × Nat × Nat) := [(8815284224,115317265725694,115317654940061)]
theorem point_links_checked67225 : (cuts67225.take 1).map (fun c => (8815247361-1+2*2^10*c.k,115317214668997+c.lower,115317603883335+c.upper)) = pointBounds67225 := by
 decide +kernel
def cuts67226 : List PrefixCut := [⟨64,185799208,185799318⟩]
theorem checked67226 : checkPrefixCuts (2^48) 8815378433 10 Manual.Count131072.C067226.packed 64 cuts67226 = true := by
 decide +kernel
def cuts67227 : List PrefixCut := [⟨25,71074880,71074925⟩,
⟨64,181581770,181581880⟩]
theorem checked67227 : checkPrefixCuts (2^48) 8815509505 10 Manual.Count131072.C067227.packed 64 cuts67227 = true := by
 decide +kernel
def pointBounds67227 : List (Nat × Nat × Nat) := [(8815560704,115317651054792,115318040269386)]
theorem point_links_checked67227 : (cuts67227.take 1).map (fun c => (8815509505-1+2*2^10*c.k,115317579979912+c.lower,115317969194461+c.upper)) = pointBounds67227 := by
 decide +kernel
def cuts67228 : List PrefixCut := [⟨64,180653148,180653257⟩]
theorem checked67228 : checkPrefixCuts (2^48) 8815640577 10 Manual.Count131072.C067228.packed 64 cuts67228 = true := by
 decide +kernel
def cuts67229 : List PrefixCut := [⟨32,93294906,93294956⟩,
⟨64,183619798,183619899⟩]
theorem checked67229 : checkPrefixCuts (2^48) 8815771649 10 Manual.Count131072.C067229.packed 64 cuts67229 = true := by
 decide +kernel
def pointBounds67229 : List (Nat × Nat × Nat) := [(8815837184,115318035509736,115318424724554)]
theorem point_links_checked67229 : (cuts67229.take 1).map (fun c => (8815771649-1+2*2^10*c.k,115317942214830+c.lower,115318331429598+c.upper)) = pointBounds67229 := by
 decide +kernel
def cuts67230 : List PrefixCut := [⟨64,180967048,180967153⟩]
theorem checked67230 : checkPrefixCuts (2^48) 8815902721 10 Manual.Count131072.C067230.packed 64 cuts67230 = true := by
 decide +kernel
def cuts67231 : List PrefixCut := [⟨39,111682275,111682340⟩,
⟨64,184029376,184029483⟩]
theorem checked67231 : checkPrefixCuts (2^48) 8816033793 10 Manual.Count131072.C067231.packed 64 cuts67231 = true := by
 decide +kernel
def pointBounds67231 : List (Nat × Nat × Nat) := [(8816113664,115318418483951,115318807698990)]
theorem point_links_checked67231 : (cuts67231.take 1).map (fun c => (8816033793-1+2*2^10*c.k,115318306801676+c.lower,115318696016650+c.upper)) = pointBounds67231 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000225
