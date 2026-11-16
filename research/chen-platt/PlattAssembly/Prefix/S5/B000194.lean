import PlattAssemblyKernel
import PlattCertificates.Count131072.C046208
import PlattCertificates.Count131072.C046209
import PlattCertificates.Count131072.C046210
import PlattCertificates.Count131072.C046211
import PlattCertificates.Count131072.C046212
import PlattCertificates.Count131072.C046213
import PlattCertificates.Count131072.C046214
import PlattCertificates.Count131072.C046215
import PlattCertificates.Count131072.C046216
import PlattCertificates.Count131072.C046217
import PlattCertificates.Count131072.C046218
import PlattCertificates.Count131072.C046219
import PlattCertificates.Count131072.C046220
import PlattCertificates.Count131072.C046221
import PlattCertificates.Count131072.C046222
import PlattCertificates.Count131072.C046223
import PlattCertificates.Count131072.C046224
import PlattCertificates.Count131072.C046225
import PlattCertificates.Count131072.C046226
import PlattCertificates.Count131072.C046227
import PlattCertificates.Count131072.C046228
import PlattCertificates.Count131072.C046229
import PlattCertificates.Count131072.C046230
import PlattCertificates.Count131072.C046231
import PlattCertificates.Count131072.C046232
import PlattCertificates.Count131072.C046233
import PlattCertificates.Count131072.C046234
import PlattCertificates.Count131072.C046235
import PlattCertificates.Count131072.C046236
import PlattCertificates.Count131072.C046237
import PlattCertificates.Count131072.C046238
import PlattCertificates.Count131072.C046239
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000194
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46208 : List PrefixCut := [⟨64,269651627,269651777⟩]
theorem checked46208 : checkPrefixCuts (2^48) 6060507137 10 Manual.Count131072.C046208.packed 64 cuts46208 = true := by
 decide +kernel
def cuts46209 : List PrefixCut := [⟨6,26101003,26101018⟩,
⟨64,273918534,273918688⟩]
theorem checked46209 : checkPrefixCuts (2^48) 6060638209 10 Manual.Count131072.C046209.packed 64 cuts46209 = true := by
 decide +kernel
def pointBounds46209 : List (Nat × Nat × Nat) := [(6060650496,110673884242490,110674270802507)]
theorem point_links_checked46209 : (cuts46209.take 1).map (fun c => (6060638209-1+2*2^10*c.k,110673858141487+c.lower,110674244701489+c.upper)) = pointBounds46209 := by
 decide +kernel
def cuts46210 : List PrefixCut := [⟨35,146523982,146524071⟩,
⟨64,268386035,268386192⟩]
theorem checked46210 : checkPrefixCuts (2^48) 6060769281 10 Manual.Count131072.C046210.packed 64 cuts46210 = true := by
 decide +kernel
def pointBounds46210 : List (Nat × Nat × Nat) := [(6060840960,110674278584003,110674665144248)]
theorem point_links_checked46210 : (cuts46210.take 1).map (fun c => (6060769281-1+2*2^10*c.k,110674132060021+c.lower,110674518620177+c.upper)) = pointBounds46210 := by
 decide +kernel
def cuts46211 : List PrefixCut := [⟨64,272931409,272931569⟩]
theorem checked46211 : checkPrefixCuts (2^48) 6060900353 10 Manual.Count131072.C046211.packed 64 cuts46211 = true := by
 decide +kernel
def pointBounds46211 : List (Nat × Nat × Nat) := [(6061031424,110674673377465,110675059937938)]
theorem point_links_checked46211 : (cuts46211.take 1).map (fun c => (6060900353-1+2*2^10*c.k,110674400446056+c.lower,110674787006369+c.upper)) = pointBounds46211 := by
 decide +kernel
def cuts46212 : List PrefixCut := [⟨64,271810962,271811114⟩]
theorem checked46212 : checkPrefixCuts (2^48) 6061031425 10 Manual.Count131072.C046212.packed 64 cuts46212 = true := by
 decide +kernel
def cuts46213 : List PrefixCut := [⟨29,119812279,119812350⟩,
⟨64,266557514,266557667⟩]
theorem checked46213 : checkPrefixCuts (2^48) 6061162497 10 Manual.Count131072.C046213.packed 64 cuts46213 = true := by
 decide +kernel
def pointBounds46213 : List (Nat × Nat × Nat) := [(6061221888,110675065000706,110675451561402)]
theorem point_links_checked46213 : (cuts46213.take 1).map (fun c => (6061162497-1+2*2^10*c.k,110674945188427+c.lower,110675331749052+c.upper)) = pointBounds46213 := by
 decide +kernel
def cuts46214 : List PrefixCut := [⟨58,248534210,248534350⟩,
⟨64,273656698,273656853⟩]
theorem checked46214 : checkPrefixCuts (2^48) 6061293569 10 Manual.Count131072.C046214.packed 64 cuts46214 = true := by
 decide +kernel
def pointBounds46214 : List (Nat × Nat × Nat) := [(6061412352,110675460280151,110675846841069)]
theorem point_links_checked46214 : (cuts46214.take 1).map (fun c => (6061293569-1+2*2^10*c.k,110675211745941+c.lower,110675598306719+c.upper)) = pointBounds46214 := by
 decide +kernel
def cuts46215 : List PrefixCut := [⟨64,268914260,268914416⟩]
theorem checked46215 : checkPrefixCuts (2^48) 6061424641 10 Manual.Count131072.C046215.packed 64 cuts46215 = true := by
 decide +kernel
def cuts46216 : List PrefixCut := [⟨23,96400933,96400985⟩,
⟨64,272623277,272623433⟩]
theorem checked46216 : checkPrefixCuts (2^48) 6061555713 10 Manual.Count131072.C046216.packed 64 cuts46216 = true := by
 decide +kernel
def pointBounds46216 : List (Nat × Nat × Nat) := [(6061602816,110675850717832,110676237278973)]
theorem point_links_checked46216 : (cuts46216.take 1).map (fun c => (6061555713-1+2*2^10*c.k,110675754316899+c.lower,110676140877988+c.upper)) = pointBounds46216 := by
 decide +kernel
def cuts46217 : List PrefixCut := [⟨52,219914592,219914719⟩,
⟨64,271410083,271410239⟩]
theorem checked46217 : checkPrefixCuts (2^48) 6061686785 10 Manual.Count131072.C046217.packed 64 cuts46217 = true := by
 decide +kernel
def pointBounds46217 : List (Nat × Nat × Nat) := [(6061793280,110676246854768,110676633416140)]
theorem point_links_checked46217 : (cuts46217.take 1).map (fun c => (6061686785-1+2*2^10*c.k,110676026940176+c.lower,110676413501421+c.upper)) = pointBounds46217 := by
 decide +kernel
def cuts46218 : List PrefixCut := [⟨64,274236670,274236828⟩]
theorem checked46218 : checkPrefixCuts (2^48) 6061817857 10 Manual.Count131072.C046218.packed 64 cuts46218 = true := by
 decide +kernel
def cuts46219 : List PrefixCut := [⟨17,72388952,72388992⟩,
⟨64,272466322,272466479⟩]
theorem checked46219 : checkPrefixCuts (2^48) 6061948929 10 Manual.Count131072.C046219.packed 64 cuts46219 = true := by
 decide +kernel
def pointBounds46219 : List (Nat × Nat × Nat) := [(6061983744,110676644975881,110677031537480)]
theorem point_links_checked46219 : (cuts46219.take 1).map (fun c => (6061948929-1+2*2^10*c.k,110676572586929+c.lower,110676959148488+c.upper)) = pointBounds46219 := by
 decide +kernel
def cuts46220 : List PrefixCut := [⟨46,196545396,196545508⟩,
⟨64,273064016,273064167⟩]
theorem checked46220 : checkPrefixCuts (2^48) 6062080001 10 Manual.Count131072.C046220.packed 64 cuts46220 = true := by
 decide +kernel
def pointBounds46220 : List (Nat × Nat × Nat) := [(6062174208,110677041598647,110677428160475)]
theorem point_links_checked46220 : (cuts46220.take 1).map (fun c => (6062080001-1+2*2^10*c.k,110676845053251+c.lower,110677231614967+c.upper)) = pointBounds46220 := by
 decide +kernel
def cuts46221 : List PrefixCut := [⟨64,269575809,269575973⟩]
theorem checked46221 : checkPrefixCuts (2^48) 6062211073 10 Manual.Count131072.C046221.packed 64 cuts46221 = true := by
 decide +kernel
def cuts46222 : List PrefixCut := [⟨11,47358570,47358598⟩,
⟨64,271287904,271288064⟩]
theorem checked46222 : checkPrefixCuts (2^48) 6062342145 10 Manual.Count131072.C046222.packed 64 cuts46222 = true := by
 decide +kernel
def pointBounds46222 : List (Nat × Nat × Nat) := [(6062364672,110677435051646,110677821613705)]
theorem point_links_checked46222 : (cuts46222.take 1).map (fun c => (6062342145-1+2*2^10*c.k,110677387693076+c.lower,110677774255107+c.upper)) = pointBounds46222 := by
 decide +kernel
def cuts46223 : List PrefixCut := [⟨40,164961311,164961405⟩,
⟨64,264828450,264828606⟩]
theorem checked46223 : checkPrefixCuts (2^48) 6062473217 10 Manual.Count131072.C046223.packed 64 cuts46223 = true := by
 decide +kernel
def pointBounds46223 : List (Nat × Nat × Nat) := [(6062555136,110677823942291,110678210504576)]
theorem point_links_checked46223 : (cuts46223.take 1).map (fun c => (6062473217-1+2*2^10*c.k,110677658980980+c.lower,110678045543171+c.upper)) = pointBounds46223 := by
 decide +kernel
def cuts46224 : List PrefixCut := [⟨64,269836899,269837054⟩]
theorem checked46224 : checkPrefixCuts (2^48) 6062604289 10 Manual.Count131072.C046224.packed 64 cuts46224 = true := by
 decide +kernel
def cuts46225 : List PrefixCut := [⟨5,21634986,21634998⟩,
⟨64,268763283,268763436⟩]
theorem checked46225 : checkPrefixCuts (2^48) 6062735361 10 Manual.Count131072.C046225.packed 64 cuts46225 = true := by
 decide +kernel
def pointBounds46225 : List (Nat × Nat × Nat) := [(6062745600,110678215281315,110678601843829)]
theorem point_links_checked46225 : (cuts46225.take 1).map (fun c => (6062735361-1+2*2^10*c.k,110678193646329+c.lower,110678580208831+c.upper)) = pointBounds46225 := by
 decide +kernel
def cuts46226 : List PrefixCut := [⟨34,142341420,142341505⟩,
⟨64,270382328,270382482⟩]
theorem checked46226 : checkPrefixCuts (2^48) 6062866433 10 Manual.Count131072.C046226.packed 64 cuts46226 = true := by
 decide +kernel
def pointBounds46226 : List (Nat × Nat × Nat) := [(6062936064,110678604751032,110678991313772)]
theorem point_links_checked46226 : (cuts46226.take 1).map (fun c => (6062866433-1+2*2^10*c.k,110678462409612+c.lower,110678848972267+c.upper)) = pointBounds46226 := by
 decide +kernel
def cuts46227 : List PrefixCut := [⟨63,269030223,269030380⟩,
⟨64,272744146,272744306⟩]
theorem checked46227 : checkPrefixCuts (2^48) 6062997505 10 Manual.Count131072.C046227.packed 64 cuts46227 = true := by
 decide +kernel
def pointBounds46227 : List (Nat × Nat × Nat) := [(6063126528,110679001822163,110679388385129)]
theorem point_links_checked46227 : (cuts46227.take 1).map (fun c => (6062997505-1+2*2^10*c.k,110678732791940+c.lower,110679119354749+c.upper)) = pointBounds46227 := by
 decide +kernel
def cuts46228 : List PrefixCut := [⟨64,269906422,269906574⟩]
theorem checked46228 : checkPrefixCuts (2^48) 6063128577 10 Manual.Count131072.C046228.packed 64 cuts46228 = true := by
 decide +kernel
def cuts46229 : List PrefixCut := [⟨28,118471020,118471085⟩,
⟨64,268693627,268693777⟩]
theorem checked46229 : checkPrefixCuts (2^48) 6063259649 10 Manual.Count131072.C046229.packed 64 cuts46229 = true := by
 decide +kernel
def pointBounds46229 : List (Nat × Nat × Nat) := [(6063316992,110679393913528,110679780476714)]
theorem point_links_checked46229 : (cuts46229.take 1).map (fun c => (6063259649-1+2*2^10*c.k,110679275442508+c.lower,110679662005629+c.upper)) = pointBounds46229 := by
 decide +kernel
def cuts46230 : List PrefixCut := [⟨57,238606946,238607091⟩,
⟨64,268270016,268270179⟩]
theorem checked46230 : checkPrefixCuts (2^48) 6063390721 10 Manual.Count131072.C046230.packed 64 cuts46230 = true := by
 decide +kernel
def pointBounds46230 : List (Nat × Nat × Nat) := [(6063507456,110679782743081,110680169306497)]
theorem point_links_checked46230 : (cuts46230.take 1).map (fun c => (6063390721-1+2*2^10*c.k,110679544136135+c.lower,110679930699406+c.upper)) = pointBounds46230 := by
 decide +kernel
def cuts46231 : List PrefixCut := [⟨64,269656810,269656967⟩]
theorem checked46231 : checkPrefixCuts (2^48) 6063521793 10 Manual.Count131072.C046231.packed 64 cuts46231 = true := by
 decide +kernel
def cuts46232 : List PrefixCut := [⟨22,92932540,92932597⟩,
⟨64,270579374,270579535⟩]
theorem checked46232 : checkPrefixCuts (2^48) 6063652865 10 Manual.Count131072.C046232.packed 64 cuts46232 = true := by
 decide +kernel
def pointBounds46232 : List (Nat × Nat × Nat) := [(6063697920,110680174995501,110680561559149)]
theorem point_links_checked46232 : (cuts46232.take 1).map (fun c => (6063652865-1+2*2^10*c.k,110680082062961+c.lower,110680468626552+c.upper)) = pointBounds46232 := by
 decide +kernel
def cuts46233 : List PrefixCut := [⟨51,216171502,216171628⟩,
⟨64,272894439,272894600⟩]
theorem checked46233 : checkPrefixCuts (2^48) 6063783937 10 Manual.Count131072.C046233.packed 64 cuts46233 = true := by
 decide +kernel
def pointBounds46233 : List (Nat × Nat × Nat) := [(6063888384,110680568813837,110680955377715)]
theorem point_links_checked46233 : (cuts46233.take 1).map (fun c => (6063783937-1+2*2^10*c.k,110680352642335+c.lower,110680739206087+c.upper)) = pointBounds46233 := by
 decide +kernel
def cuts46234 : List PrefixCut := [⟨64,268014718,268014878⟩]
theorem checked46234 : checkPrefixCuts (2^48) 6063915009 10 Manual.Count131072.C046234.packed 64 cuts46234 = true := by
 decide +kernel
def cuts46235 : List PrefixCut := [⟨16,67907904,67907942⟩,
⟨64,272464884,272465036⟩]
theorem checked46235 : checkPrefixCuts (2^48) 6064046081 10 Manual.Count131072.C046235.packed 64 cuts46235 = true := by
 decide +kernel
def pointBounds46235 : List (Nat × Nat × Nat) := [(6064078848,110680961459396,110681348023507)]
theorem point_links_checked46235 : (cuts46235.take 1).map (fun c => (6064046081-1+2*2^10*c.k,110680893551492+c.lower,110681280115565+c.upper)) = pointBounds46235 := by
 decide +kernel
def cuts46236 : List PrefixCut := [⟨45,192949890,192949996⟩,
⟨64,271716404,271716559⟩]
theorem checked46236 : checkPrefixCuts (2^48) 6064177153 10 Manual.Count131072.C046236.packed 64 cuts46236 = true := by
 decide +kernel
def pointBounds46236 : List (Nat × Nat × Nat) := [(6064269312,110681358966266,110681745530597)]
theorem point_links_checked46236 : (cuts46236.take 1).map (fun c => (6064177153-1+2*2^10*c.k,110681166016376+c.lower,110681552580601+c.upper)) = pointBounds46236 := by
 decide +kernel
def cuts46237 : List PrefixCut := [⟨64,271385631,271385779⟩]
theorem checked46237 : checkPrefixCuts (2^48) 6064308225 10 Manual.Count131072.C046237.packed 64 cuts46237 = true := by
 decide +kernel
def cuts46238 : List PrefixCut := [⟨10,42561567,42561591⟩,
⟨64,272075944,272076094⟩]
theorem checked46238 : checkPrefixCuts (2^48) 6064439297 10 Manual.Count131072.C046238.packed 64 cuts46238 = true := by
 decide +kernel
def pointBounds46238 : List (Nat × Nat × Nat) := [(6064459776,110681751679978,110682138244530)]
theorem point_links_checked46238 : (cuts46238.take 1).map (fun c => (6064439297-1+2*2^10*c.k,110681709118411+c.lower,110682095682939+c.upper)) = pointBounds46238 := by
 decide +kernel
def cuts46239 : List PrefixCut := [⟨39,163836801,163836897⟩,
⟨64,269192482,269192642⟩]
theorem checked46239 : checkPrefixCuts (2^48) 6064570369 10 Manual.Count131072.C046239.packed 64 cuts46239 = true := by
 decide +kernel
def pointBounds46239 : List (Nat × Nat × Nat) := [(6064650240,110682145031156,110682531595930)]
theorem point_links_checked46239 : (cuts46239.take 1).map (fun c => (6064570369-1+2*2^10*c.k,110681981194355+c.lower,110682367759033+c.upper)) = pointBounds46239 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000194
