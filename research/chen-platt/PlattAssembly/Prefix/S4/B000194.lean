import PlattAssemblyKernel
import PlattCertificates.Count131072.C036208
import PlattCertificates.Count131072.C036209
import PlattCertificates.Count131072.C036210
import PlattCertificates.Count131072.C036211
import PlattCertificates.Count131072.C036212
import PlattCertificates.Count131072.C036213
import PlattCertificates.Count131072.C036214
import PlattCertificates.Count131072.C036215
import PlattCertificates.Count131072.C036216
import PlattCertificates.Count131072.C036217
import PlattCertificates.Count131072.C036218
import PlattCertificates.Count131072.C036219
import PlattCertificates.Count131072.C036220
import PlattCertificates.Count131072.C036221
import PlattCertificates.Count131072.C036222
import PlattCertificates.Count131072.C036223
import PlattCertificates.Count131072.C036224
import PlattCertificates.Count131072.C036225
import PlattCertificates.Count131072.C036226
import PlattCertificates.Count131072.C036227
import PlattCertificates.Count131072.C036228
import PlattCertificates.Count131072.C036229
import PlattCertificates.Count131072.C036230
import PlattCertificates.Count131072.C036231
import PlattCertificates.Count131072.C036232
import PlattCertificates.Count131072.C036233
import PlattCertificates.Count131072.C036234
import PlattCertificates.Count131072.C036235
import PlattCertificates.Count131072.C036236
import PlattCertificates.Count131072.C036237
import PlattCertificates.Count131072.C036238
import PlattCertificates.Count131072.C036239
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000194
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts36208 : List PrefixCut := [⟨64,349276674,349276889⟩]
theorem checked36208 : checkPrefixCuts (2^48) 4749787137 10 Manual.Count131072.C036208.packed 64 cuts36208 = true := by
 decide +kernel
def cuts36209 : List PrefixCut := [⟨1,5629594,5629597⟩,
⟨64,350807782,350808001⟩]
theorem checked36209 : checkPrefixCuts (2^48) 4749918209 10 Manual.Count131072.C036209.packed 64 cuts36209 = true := by
 decide +kernel
def pointBounds36209 : List (Nat × Nat × Nat) := [(4749920256,107612216034188,107612600782270)]
theorem point_links_checked36209 : (cuts36209.take 1).map (fun c => (4749918209-1+2*2^10*c.k,107612210404594+c.lower,107612595152673+c.upper)) = pointBounds36209 := by
 decide +kernel
def cuts36210 : List PrefixCut := [⟨10,54694332,54694366⟩,
⟨64,347242790,347243001⟩]
theorem checked36210 : checkPrefixCuts (2^48) 4750049281 10 Manual.Count131072.C036210.packed 64 cuts36210 = true := by
 decide +kernel
def pointBounds36210 : List (Nat × Nat × Nat) := [(4750069760,107612615906708,107613000655040)]
theorem point_links_checked36210 : (cuts36210.take 1).map (fun c => (4750049281-1+2*2^10*c.k,107612561212376+c.lower,107612945960674+c.upper)) = pointBounds36210 := by
 decide +kernel
def cuts36211 : List PrefixCut := [⟨19,100497112,100497174⟩,
⟨64,348832979,348833193⟩]
theorem checked36211 : checkPrefixCuts (2^48) 4750180353 10 Manual.Count131072.C036211.packed 64 cuts36211 = true := by
 decide +kernel
def pointBounds36211 : List (Nat × Nat × Nat) := [(4750219264,107613008952278,107613393700849)]
theorem point_links_checked36211 : (cuts36211.take 1).map (fun c => (4750180353-1+2*2^10*c.k,107612908455166+c.lower,107613293203675+c.upper)) = pointBounds36211 := by
 decide +kernel
def cuts36212 : List PrefixCut := [⟨28,154711230,154711324⟩,
⟨64,354808004,354808219⟩]
theorem checked36212 : checkPrefixCuts (2^48) 4750311425 10 Manual.Count131072.C036212.packed 64 cuts36212 = true := by
 decide +kernel
def pointBounds36212 : List (Nat × Nat × Nat) := [(4750368768,107613411999375,107613796748192)]
theorem point_links_checked36212 : (cuts36212.take 1).map (fun c => (4750311425-1+2*2^10*c.k,107613257288145+c.lower,107613642036868+c.upper)) = pointBounds36212 := by
 decide +kernel
def cuts36213 : List PrefixCut := [⟨37,200152843,200152966⟩,
⟨64,346443718,346443930⟩]
theorem checked36213 : checkPrefixCuts (2^48) 4750442497 10 Manual.Count131072.C036213.packed 64 cuts36213 = true := by
 decide +kernel
def pointBounds36213 : List (Nat × Nat × Nat) := [(4750518272,107613812248992,107614196998053)]
theorem point_links_checked36213 : (cuts36213.take 1).map (fun c => (4750442497-1+2*2^10*c.k,107613612096149+c.lower,107613996845087+c.upper)) = pointBounds36213 := by
 decide +kernel
def cuts36214 : List PrefixCut := [⟨46,250568795,250568949⟩,
⟨64,349752136,349752349⟩]
theorem checked36214 : checkPrefixCuts (2^48) 4750573569 10 Manual.Count131072.C036214.packed 64 cuts36214 = true := by
 decide +kernel
def pointBounds36214 : List (Nat × Nat × Nat) := [(4750667776,107614209108662,107614593857966)]
theorem point_links_checked36214 : (cuts36214.take 1).map (fun c => (4750573569-1+2*2^10*c.k,107613958539867+c.lower,107614343289017+c.upper)) = pointBounds36214 := by
 decide +kernel
def cuts36215 : List PrefixCut := [⟨55,297249140,297249318⟩,
⟨64,345654400,345654607⟩]
theorem checked36215 : checkPrefixCuts (2^48) 4750704641 10 Manual.Count131072.C036215.packed 64 cuts36215 = true := by
 decide +kernel
def pointBounds36215 : List (Nat × Nat × Nat) := [(4750817280,107614605541143,107614990290684)]
theorem point_links_checked36215 : (cuts36215.take 1).map (fun c => (4750704641-1+2*2^10*c.k,107614308292003+c.lower,107614693041366+c.upper)) = pointBounds36215 := by
 decide +kernel
def cuts36216 : List PrefixCut := [⟨64,351924934,351925151⟩]
theorem checked36216 : checkPrefixCuts (2^48) 4750835713 10 Manual.Count131072.C036216.packed 64 cuts36216 = true := by
 decide +kernel
def pointBounds36216 : List (Nat × Nat × Nat) := [(4750966784,107615005871337,107615390621124)]
theorem point_links_checked36216 : (cuts36216.take 1).map (fun c => (4750835713-1+2*2^10*c.k,107614653946403+c.lower,107615038695973+c.upper)) = pointBounds36216 := by
 decide +kernel
def cuts36217 : List PrefixCut := [⟨64,350967346,350967566⟩]
theorem checked36217 : checkPrefixCuts (2^48) 4750966785 10 Manual.Count131072.C036217.packed 64 cuts36217 = true := by
 decide +kernel
def cuts36218 : List PrefixCut := [⟨9,50475946,50475975⟩,
⟨64,354097595,354097805⟩]
theorem checked36218 : checkPrefixCuts (2^48) 4751097857 10 Manual.Count131072.C036218.packed 64 cuts36218 = true := by
 decide +kernel
def pointBounds36218 : List (Nat × Nat × Nat) := [(4751116288,107615407314629,107615792064665)]
theorem point_links_checked36218 : (cuts36218.take 1).map (fun c => (4751097857-1+2*2^10*c.k,107615356838683+c.lower,107615741588690+c.upper)) = pointBounds36218 := by
 decide +kernel
def cuts36219 : List PrefixCut := [⟨18,99704808,99704869⟩,
⟨64,350474063,350474274⟩]
theorem checked36219 : checkPrefixCuts (2^48) 4751228929 10 Manual.Count131072.C036219.packed 64 cuts36219 = true := by
 decide +kernel
def pointBounds36219 : List (Nat × Nat × Nat) := [(4751265792,107615810641086,107616195391364)]
theorem point_links_checked36219 : (cuts36219.take 1).map (fun c => (4751228929-1+2*2^10*c.k,107615710936278+c.lower,107616095686495+c.upper)) = pointBounds36219 := by
 decide +kernel
def cuts36220 : List PrefixCut := [⟨27,149404702,149404795⟩,
⟨64,349931231,349931448⟩]
theorem checked36220 : checkPrefixCuts (2^48) 4751360001 10 Manual.Count131072.C036220.packed 64 cuts36220 = true := by
 decide +kernel
def pointBounds36220 : List (Nat × Nat × Nat) := [(4751415296,107616210815043,107616595565564)]
theorem point_links_checked36220 : (cuts36220.take 1).map (fun c => (4751360001-1+2*2^10*c.k,107616061410341+c.lower,107616446160769+c.upper)) = pointBounds36220 := by
 decide +kernel
def cuts36221 : List PrefixCut := [⟨36,195073415,195073536⟩,
⟨64,346426496,346426709⟩]
theorem checked36221 : checkPrefixCuts (2^48) 4751491073 10 Manual.Count131072.C036221.packed 64 cuts36221 = true := by
 decide +kernel
def pointBounds36221 : List (Nat × Nat × Nat) := [(4751564800,107616606414987,107616991165753)]
theorem point_links_checked36221 : (cuts36221.take 1).map (fun c => (4751491073-1+2*2^10*c.k,107616411341572+c.lower,107616796092217+c.upper)) = pointBounds36221 := by
 decide +kernel
def cuts36222 : List PrefixCut := [⟨45,247314763,247314915⟩,
⟨64,348075619,348075837⟩]
theorem checked36222 : checkPrefixCuts (2^48) 4751622145 10 Manual.Count131072.C036222.packed 64 cuts36222 = true := by
 decide +kernel
def pointBounds36222 : List (Nat × Nat × Nat) := [(4751714304,107617005082831,107617389833841)]
theorem point_links_checked36222 : (cuts36222.take 1).map (fun c => (4751622145-1+2*2^10*c.k,107616757768068+c.lower,107617142518926+c.upper)) = pointBounds36222 := by
 decide +kernel
def cuts36223 : List PrefixCut := [⟨54,294399547,294399729⟩,
⟨64,348480649,348480864⟩]
theorem checked36223 : checkPrefixCuts (2^48) 4751753217 10 Manual.Count131072.C036223.packed 64 cuts36223 = true := by
 decide +kernel
def pointBounds36223 : List (Nat × Nat × Nat) := [(4751863808,107617400243234,107617784994492)]
theorem point_links_checked36223 : (cuts36223.take 1).map (fun c => (4751753217-1+2*2^10*c.k,107617105843687+c.lower,107617490594763+c.upper)) = pointBounds36223 := by
 decide +kernel
def cuts36224 : List PrefixCut := [⟨63,343080780,343080993⟩,
⟨64,348293262,348293478⟩]
theorem checked36224 : checkPrefixCuts (2^48) 4751884289 10 Manual.Count131072.C036224.packed 64 cuts36224 = true := by
 decide +kernel
def pointBounds36224 : List (Nat × Nat × Nat) := [(4752013312,107617797405116,107618182156620)]
theorem point_links_checked36224 : (cuts36224.take 1).map (fun c => (4751884289-1+2*2^10*c.k,107617454324336+c.lower,107617839075627+c.upper)) = pointBounds36224 := by
 decide +kernel
def cuts36225 : List PrefixCut := [⟨64,350475277,350475495⟩]
theorem checked36225 : checkPrefixCuts (2^48) 4752015361 10 Manual.Count131072.C036225.packed 64 cuts36225 = true := by
 decide +kernel
def cuts36226 : List PrefixCut := [⟨8,44482482,44482510⟩,
⟨64,349636413,349636622⟩]
theorem checked36226 : checkPrefixCuts (2^48) 4752146433 10 Manual.Count131072.C036226.packed 64 cuts36226 = true := by
 decide +kernel
def pointBounds36226 : List (Nat × Nat × Nat) := [(4752162816,107618197575357,107618582327110)]
theorem point_links_checked36226 : (cuts36226.take 1).map (fun c => (4752146433-1+2*2^10*c.k,107618153092875+c.lower,107618537844600+c.upper)) = pointBounds36226 := by
 decide +kernel
def cuts36227 : List PrefixCut := [⟨17,93108394,93108453⟩,
⟨64,351522061,351522280⟩]
theorem checked36227 : checkPrefixCuts (2^48) 4752277505 10 Manual.Count131072.C036227.packed 64 cuts36227 = true := by
 decide +kernel
def pointBounds36227 : List (Nat × Nat × Nat) := [(4752312320,107618595837682,107618980589675)]
theorem point_links_checked36227 : (cuts36227.take 1).map (fun c => (4752277505-1+2*2^10*c.k,107618502729288+c.lower,107618887481222+c.upper)) = pointBounds36227 := by
 decide +kernel
def cuts36228 : List PrefixCut := [⟨26,138770037,138770123⟩,
⟨64,345648844,345649054⟩]
theorem checked36228 : checkPrefixCuts (2^48) 4752408577 10 Manual.Count131072.C036228.packed 64 cuts36228 = true := by
 decide +kernel
def pointBounds36228 : List (Nat × Nat × Nat) := [(4752461824,107618993021386,107619377773625)]
theorem point_links_checked36228 : (cuts36228.take 1).map (fun c => (4752408577-1+2*2^10*c.k,107618854251349+c.lower,107619239003502+c.upper)) = pointBounds36228 := by
 decide +kernel
def cuts36229 : List PrefixCut := [⟨35,191180735,191180849⟩,
⟨64,349252106,349252315⟩]
theorem checked36229 : checkPrefixCuts (2^48) 4752539649 10 Manual.Count131072.C036229.packed 64 cuts36229 = true := by
 decide +kernel
def pointBounds36229 : List (Nat × Nat × Nat) := [(4752611328,107619391080928,107619775833405)]
theorem point_links_checked36229 : (cuts36229.take 1).map (fun c => (4752539649-1+2*2^10*c.k,107619199900193+c.lower,107619584652556+c.upper)) = pointBounds36229 := by
 decide +kernel
def cuts36230 : List PrefixCut := [⟨44,239028129,239028280⟩,
⟨64,345037643,345037860⟩]
theorem checked36230 : checkPrefixCuts (2^48) 4752670721 10 Manual.Count131072.C036230.packed 64 cuts36230 = true := by
 decide +kernel
def pointBounds36230 : List (Nat × Nat × Nat) := [(4752760832,107619788180428,107620172933151)]
theorem point_links_checked36230 : (cuts36230.take 1).map (fun c => (4752670721-1+2*2^10*c.k,107619549152299+c.lower,107619933904871+c.upper)) = pointBounds36230 := by
 decide +kernel
def cuts36231 : List PrefixCut := [⟨53,290722075,290722255⟩,
⟨64,350121183,350121401⟩]
theorem checked36231 : checkPrefixCuts (2^48) 4752801793 10 Manual.Count131072.C036231.packed 64 cuts36231 = true := by
 decide +kernel
def pointBounds36231 : List (Nat × Nat × Nat) := [(4752910336,107620184912017,107620569664986)]
theorem point_links_checked36231 : (cuts36231.take 1).map (fun c => (4752801793-1+2*2^10*c.k,107619894189942+c.lower,107620278942731+c.upper)) = pointBounds36231 := by
 decide +kernel
def cuts36232 : List PrefixCut := [⟨62,334714350,334714554⟩,
⟨64,345137016,345137227⟩]
theorem checked36232 : checkPrefixCuts (2^48) 4752932865 10 Manual.Count131072.C036232.packed 64 cuts36232 = true := by
 decide +kernel
def pointBounds36232 : List (Nat × Nat × Nat) := [(4753059840,107620579025475,107620963778686)]
theorem point_links_checked36232 : (cuts36232.take 1).map (fun c => (4752932865-1+2*2^10*c.k,107620244311125+c.lower,107620629064132+c.upper)) = pointBounds36232 := by
 decide +kernel
def cuts36233 : List PrefixCut := [⟨64,346311920,346312141⟩]
theorem checked36233 : checkPrefixCuts (2^48) 4753063937 10 Manual.Count131072.C036233.packed 64 cuts36233 = true := by
 decide +kernel
def cuts36234 : List PrefixCut := [⟨7,38314013,38314038⟩,
⟨64,352756971,352757191⟩]
theorem checked36234 : checkPrefixCuts (2^48) 4753195009 10 Manual.Count131072.C036234.packed 64 cuts36234 = true := by
 decide +kernel
def pointBounds36234 : List (Nat × Nat × Nat) := [(4753209344,107620974074074,107621358827538)]
theorem point_links_checked36234 : (cuts36234.take 1).map (fun c => (4753195009-1+2*2^10*c.k,107620935760061+c.lower,107621320513500+c.upper)) = pointBounds36234 := by
 decide +kernel
def cuts36235 : List PrefixCut := [⟨16,86810950,86811007⟩,
⟨64,347713946,347714165⟩]
theorem checked36235 : checkPrefixCuts (2^48) 4753326081 10 Manual.Count131072.C036235.packed 64 cuts36235 = true := by
 decide +kernel
def pointBounds36235 : List (Nat × Nat × Nat) := [(4753358848,107621375327982,107621760081698)]
theorem point_links_checked36235 : (cuts36235.take 1).map (fun c => (4753326081-1+2*2^10*c.k,107621288517032+c.lower,107621673270691+c.upper)) = pointBounds36235 := by
 decide +kernel
def cuts36236 : List PrefixCut := [⟨25,137555182,137555268⟩,
⟨64,355402162,355402381⟩]
theorem checked36236 : checkPrefixCuts (2^48) 4753457153 10 Manual.Count131072.C036236.packed 64 cuts36236 = true := by
 decide +kernel
def pointBounds36236 : List (Nat × Nat × Nat) := [(4753508352,107621773786160,107622158540124)]
theorem point_links_checked36236 : (cuts36236.take 1).map (fun c => (4753457153-1+2*2^10*c.k,107621636230978+c.lower,107622020984856+c.upper)) = pointBounds36236 := by
 decide +kernel
def cuts36237 : List PrefixCut := [⟨34,185572633,185572750⟩,
⟨64,349411941,349412154⟩]
theorem checked36237 : checkPrefixCuts (2^48) 4753588225 10 Manual.Count131072.C036237.packed 64 cuts36237 = true := by
 decide +kernel
def pointBounds36237 : List (Nat × Nat × Nat) := [(4753657856,107622177205773,107622561959987)]
theorem point_links_checked36237 : (cuts36237.take 1).map (fun c => (4753588225-1+2*2^10*c.k,107621991633140+c.lower,107622376387237+c.upper)) = pointBounds36237 := by
 decide +kernel
def cuts36238 : List PrefixCut := [⟨43,230508258,230508395⟩,
⟨64,346619349,346619558⟩]
theorem checked36238 : checkPrefixCuts (2^48) 4753719297 10 Manual.Count131072.C036238.packed 64 cuts36238 = true := by
 decide +kernel
def pointBounds36238 : List (Nat × Nat × Nat) := [(4753807360,107622571553339,107622956307786)]
theorem point_links_checked36238 : (cuts36238.take 1).map (fun c => (4753719297-1+2*2^10*c.k,107622341045081+c.lower,107622725799391+c.upper)) = pointBounds36238 := by
 decide +kernel
def cuts36239 : List PrefixCut := [⟨52,279822772,279822944⟩,
⟨64,348030844,348031059⟩]
theorem checked36239 : checkPrefixCuts (2^48) 4753850369 10 Manual.Count131072.C036239.packed 64 cuts36239 = true := by
 decide +kernel
def pointBounds36239 : List (Nat × Nat × Nat) := [(4753956864,107622967487202,107623352241893)]
theorem point_links_checked36239 : (cuts36239.take 1).map (fun c => (4753850369-1+2*2^10*c.k,107622687664430+c.lower,107623072418949+c.upper)) = pointBounds36239 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000194
