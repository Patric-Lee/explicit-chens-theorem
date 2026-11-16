import PlattAssemblyKernel
import PlattCertificates.Count131072.C042240
import PlattCertificates.Count131072.C042241
import PlattCertificates.Count131072.C042242
import PlattCertificates.Count131072.C042243
import PlattCertificates.Count131072.C042244
import PlattCertificates.Count131072.C042245
import PlattCertificates.Count131072.C042246
import PlattCertificates.Count131072.C042247
import PlattCertificates.Count131072.C042248
import PlattCertificates.Count131072.C042249
import PlattCertificates.Count131072.C042250
import PlattCertificates.Count131072.C042251
import PlattCertificates.Count131072.C042252
import PlattCertificates.Count131072.C042253
import PlattCertificates.Count131072.C042254
import PlattCertificates.Count131072.C042255
import PlattCertificates.Count131072.C042256
import PlattCertificates.Count131072.C042257
import PlattCertificates.Count131072.C042258
import PlattCertificates.Count131072.C042259
import PlattCertificates.Count131072.C042260
import PlattCertificates.Count131072.C042261
import PlattCertificates.Count131072.C042262
import PlattCertificates.Count131072.C042263
import PlattCertificates.Count131072.C042264
import PlattCertificates.Count131072.C042265
import PlattCertificates.Count131072.C042266
import PlattCertificates.Count131072.C042267
import PlattCertificates.Count131072.C042268
import PlattCertificates.Count131072.C042269
import PlattCertificates.Count131072.C042270
import PlattCertificates.Count131072.C042271
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000070
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42240 : List PrefixCut := [⟨64,292373278,292373451⟩]
theorem checked42240 : checkPrefixCuts (2^48) 5540413441 10 Manual.Count131072.C042240.packed 64 cuts42240 = true := by
 decide +kernel
def cuts42241 : List PrefixCut := [⟨13,59693084,59693120⟩,
⟨64,295566895,295567071⟩]
theorem checked42241 : checkPrefixCuts (2^48) 5540544513 10 Manual.Count131072.C042241.packed 64 cuts42241 = true := by
 decide +kernel
def pointBounds42241 : List (Nat × Nat × Nat) := [(5540571136,109550477219486,109550863128640)]
theorem point_links_checked42241 : (cuts42241.take 1).map (fun c => (5540544513-1+2*2^10*c.k,109550417526402+c.lower,109550803435520+c.upper)) = pointBounds42241 := by
 decide +kernel
def cuts42242 : List PrefixCut := [⟨34,156924984,156925074⟩,
⟨64,296169496,296169663⟩]
theorem checked42242 : checkPrefixCuts (2^48) 5540675585 10 Manual.Count131072.C042242.packed 64 cuts42242 = true := by
 decide +kernel
def pointBounds42242 : List (Nat × Nat × Nat) := [(5540745216,109550870018281,109551255927665)]
theorem point_links_checked42242 : (cuts42242.take 1).map (fun c => (5540675585-1+2*2^10*c.k,109550713093297+c.lower,109551099002591+c.upper)) = pointBounds42242 := by
 decide +kernel
def cuts42243 : List PrefixCut := [⟨55,253033950,253034099⟩,
⟨64,296467290,296467465⟩]
theorem checked42243 : checkPrefixCuts (2^48) 5540806657 10 Manual.Count131072.C042243.packed 64 cuts42243 = true := by
 decide +kernel
def pointBounds42243 : List (Nat × Nat × Nat) := [(5540919296,109551262296743,109551648206353)]
theorem point_links_checked42243 : (cuts42243.take 1).map (fun c => (5540806657-1+2*2^10*c.k,109551009262793+c.lower,109551395172254+c.upper)) = pointBounds42243 := by
 decide +kernel
def cuts42244 : List PrefixCut := [⟨64,296714287,296714464⟩]
theorem checked42244 : checkPrefixCuts (2^48) 5540937729 10 Manual.Count131072.C042244.packed 64 cuts42244 = true := by
 decide +kernel
def cuts42245 : List PrefixCut := [⟨12,55877613,55877645⟩,
⟨64,296250125,296250297⟩]
theorem checked42245 : checkPrefixCuts (2^48) 5541068801 10 Manual.Count131072.C042245.packed 64 cuts42245 = true := by
 decide +kernel
def pointBounds42245 : List (Nat × Nat × Nat) := [(5541093376,109551658321983,109552044231828)]
theorem point_links_checked42245 : (cuts42245.take 1).map (fun c => (5541068801-1+2*2^10*c.k,109551602444370+c.lower,109551988354183+c.upper)) = pointBounds42245 := by
 decide +kernel
def cuts42246 : List PrefixCut := [⟨33,150713006,150713095⟩,
⟨64,295633520,295633695⟩]
theorem checked42246 : checkPrefixCuts (2^48) 5541199873 10 Manual.Count131072.C042246.packed 64 cuts42246 = true := by
 decide +kernel
def pointBounds42246 : List (Nat × Nat × Nat) := [(5541267456,109552049407501,109552435317575)]
theorem point_links_checked42246 : (cuts42246.take 1).map (fun c => (5541199873-1+2*2^10*c.k,109551898694495+c.lower,109552284604480+c.upper)) = pointBounds42246 := by
 decide +kernel
def cuts42247 : List PrefixCut := [⟨54,245086009,245086156⟩,
⟨64,291207352,291207527⟩]
theorem checked42247 : checkPrefixCuts (2^48) 5541330945 10 Manual.Count131072.C042247.packed 64 cuts42247 = true := by
 decide +kernel
def pointBounds42247 : List (Nat × Nat × Nat) := [(5541441536,109552439414024,109552825324331)]
theorem point_links_checked42247 : (cuts42247.take 1).map (fun c => (5541330945-1+2*2^10*c.k,109552194328015+c.lower,109552580238175+c.upper)) = pointBounds42247 := by
 decide +kernel
def cuts42248 : List PrefixCut := [⟨64,302578261,302578438⟩]
theorem checked42248 : checkPrefixCuts (2^48) 5541462017 10 Manual.Count131072.C042248.packed 64 cuts42248 = true := by
 decide +kernel
def cuts42249 : List PrefixCut := [⟨11,49421622,49421652⟩,
⟨64,294952225,294952400⟩]
theorem checked42249 : checkPrefixCuts (2^48) 5541593089 10 Manual.Count131072.C042249.packed 64 cuts42249 = true := by
 decide +kernel
def pointBounds42249 : List (Nat × Nat × Nat) := [(5541615616,109552837535250,109553223445792)]
theorem point_links_checked42249 : (cuts42249.take 1).map (fun c => (5541593089-1+2*2^10*c.k,109552788113628+c.lower,109553174024140+c.upper)) = pointBounds42249 := by
 decide +kernel
def cuts42250 : List PrefixCut := [⟨32,148717906,148717995⟩,
⟨64,297180101,297180278⟩]
theorem checked42250 : checkPrefixCuts (2^48) 5541724161 10 Manual.Count131072.C042250.packed 64 cuts42250 = true := by
 decide +kernel
def pointBounds42250 : List (Nat × Nat × Nat) := [(5541789696,109553231783759,109553617694535)]
theorem point_links_checked42250 : (cuts42250.take 1).map (fun c => (5541724161-1+2*2^10*c.k,109553083065853+c.lower,109553468976540+c.upper)) = pointBounds42250 := by
 decide +kernel
def cuts42251 : List PrefixCut := [⟨53,245723161,245723299⟩,
⟨64,294785949,294786117⟩]
theorem checked42251 : checkPrefixCuts (2^48) 5541855233 10 Manual.Count131072.C042251.packed 64 cuts42251 = true := by
 decide +kernel
def pointBounds42251 : List (Nat × Nat × Nat) := [(5541963776,109553625969115,109554011880117)]
theorem point_links_checked42251 : (cuts42251.take 1).map (fun c => (5541855233-1+2*2^10*c.k,109553380245954+c.lower,109553766156818+c.upper)) = pointBounds42251 := by
 decide +kernel
def cuts42252 : List PrefixCut := [⟨64,296607368,296607539⟩]
theorem checked42252 : checkPrefixCuts (2^48) 5541986305 10 Manual.Count131072.C042252.packed 64 cuts42252 = true := by
 decide +kernel
def cuts42253 : List PrefixCut := [⟨10,46064929,46064956⟩,
⟨64,300003110,300003286⟩]
theorem checked42253 : checkPrefixCuts (2^48) 5542117377 10 Manual.Count131072.C042253.packed 64 cuts42253 = true := by
 decide +kernel
def pointBounds42253 : List (Nat × Nat × Nat) := [(5542137856,109554017704200,109554403615430)]
theorem point_links_checked42253 : (cuts42253.take 1).map (fun c => (5542117377-1+2*2^10*c.k,109553971639271+c.lower,109554357550474+c.upper)) = pointBounds42253 := by
 decide +kernel
def cuts42254 : List PrefixCut := [⟨31,145707436,145707518⟩,
⟨64,297710658,297710832⟩]
theorem checked42254 : checkPrefixCuts (2^48) 5542248449 10 Manual.Count131072.C042254.packed 64 cuts42254 = true := by
 decide +kernel
def pointBounds42254 : List (Nat × Nat × Nat) := [(5542311936,109554417349817,109554803261278)]
theorem point_links_checked42254 : (cuts42254.take 1).map (fun c => (5542248449-1+2*2^10*c.k,109554271642381+c.lower,109554657553760+c.upper)) = pointBounds42254 := by
 decide +kernel
def cuts42255 : List PrefixCut := [⟨52,242144979,242145122⟩,
⟨64,299684207,299684381⟩]
theorem checked42255 : checkPrefixCuts (2^48) 5542379521 10 Manual.Count131072.C042255.packed 64 cuts42255 = true := by
 decide +kernel
def pointBounds42255 : List (Nat × Nat × Nat) := [(5542486016,109554811498018,109555197409714)]
theorem point_links_checked42255 : (cuts42255.take 1).map (fun c => (5542379521-1+2*2^10*c.k,109554569353039+c.lower,109554955264592+c.upper)) = pointBounds42255 := by
 decide +kernel
def cuts42256 : List PrefixCut := [⟨64,296528514,296528685⟩]
theorem checked42256 : checkPrefixCuts (2^48) 5542510593 10 Manual.Count131072.C042256.packed 64 cuts42256 = true := by
 decide +kernel
def cuts42257 : List PrefixCut := [⟨9,41286940,41286963⟩,
⟨64,296521499,296521669⟩]
theorem checked42257 : checkPrefixCuts (2^48) 5542641665 10 Manual.Count131072.C042257.packed 64 cuts42257 = true := by
 decide +kernel
def pointBounds42257 : List (Nat × Nat × Nat) := [(5542660096,109555206852700,109555592764621)]
theorem point_links_checked42257 : (cuts42257.take 1).map (fun c => (5542641665-1+2*2^10*c.k,109555165565760+c.lower,109555551477658+c.upper)) = pointBounds42257 := by
 decide +kernel
def cuts42258 : List PrefixCut := [⟨30,139244369,139244447⟩,
⟨64,295143413,295143581⟩]
theorem checked42258 : checkPrefixCuts (2^48) 5542772737 10 Manual.Count131072.C042258.packed 64 cuts42258 = true := by
 decide +kernel
def pointBounds42258 : List (Nat × Nat × Nat) := [(5542834176,109555601331628,109555987243774)]
theorem point_links_checked42258 : (cuts42258.take 1).map (fun c => (5542772737-1+2*2^10*c.k,109555462087259+c.lower,109555847999327+c.upper)) = pointBounds42258 := by
 decide +kernel
def cuts42259 : List PrefixCut := [⟨51,240192470,240192607⟩,
⟨64,299960584,299960758⟩]
theorem checked42259 : checkPrefixCuts (2^48) 5542903809 10 Manual.Count131072.C042259.packed 64 cuts42259 = true := by
 decide +kernel
def pointBounds42259 : List (Nat × Nat × Nat) := [(5543008256,109555997423142,109556383335515)]
theorem point_links_checked42259 : (cuts42259.take 1).map (fun c => (5542903809-1+2*2^10*c.k,109555757230672+c.lower,109556143142908+c.upper)) = pointBounds42259 := by
 decide +kernel
def cuts42260 : List PrefixCut := [⟨64,296957472,296957644⟩]
theorem checked42260 : checkPrefixCuts (2^48) 5543034881 10 Manual.Count131072.C042260.packed 64 cuts42260 = true := by
 decide +kernel
def cuts42261 : List PrefixCut := [⟨8,38540995,38541016⟩,
⟨64,297356728,297356899⟩]
theorem checked42261 : checkPrefixCuts (2^48) 5543165953 10 Manual.Count131072.C042261.packed 64 cuts42261 = true := by
 decide +kernel
def pointBounds42261 : List (Nat × Nat × Nat) := [(5543182336,109556392689723,109556778602326)]
theorem point_links_checked42261 : (cuts42261.take 1).map (fun c => (5543165953-1+2*2^10*c.k,109556354148728+c.lower,109556740061310+c.upper)) = pointBounds42261 := by
 decide +kernel
def cuts42262 : List PrefixCut := [⟨29,135016717,135016797⟩,
⟨64,298111314,298111492⟩]
theorem checked42262 : checkPrefixCuts (2^48) 5543297025 10 Manual.Count131072.C042262.packed 64 cuts42262 = true := by
 decide +kernel
def pointBounds42262 : List (Nat × Nat × Nat) := [(5543356416,109556786522173,109557172435006)]
theorem point_links_checked42262 : (cuts42262.take 1).map (fun c => (5543297025-1+2*2^10*c.k,109556651505456+c.lower,109557037418209+c.upper)) = pointBounds42262 := by
 decide +kernel
def cuts42263 : List PrefixCut := [⟨50,231690218,231690352⟩,
⟨64,296631766,296631935⟩]
theorem checked42263 : checkPrefixCuts (2^48) 5543428097 10 Manual.Count131072.C042263.packed 64 cuts42263 = true := by
 decide +kernel
def pointBounds42263 : List (Nat × Nat × Nat) := [(5543530496,109557181306988,109557567220053)]
theorem point_links_checked42263 : (cuts42263.take 1).map (fun c => (5543428097-1+2*2^10*c.k,109556949616770+c.lower,109557335529701+c.upper)) = pointBounds42263 := by
 decide +kernel
def cuts42264 : List PrefixCut := [⟨64,291648856,291649027⟩]
theorem checked42264 : checkPrefixCuts (2^48) 5543559169 10 Manual.Count131072.C042264.packed 64 cuts42264 = true := by
 decide +kernel
def cuts42265 : List PrefixCut := [⟨7,32952232,32952252⟩,
⟨64,298902548,298902728⟩]
theorem checked42265 : checkPrefixCuts (2^48) 5543690241 10 Manual.Count131072.C042265.packed 64 cuts42265 = true := by
 decide +kernel
def pointBounds42265 : List (Nat × Nat × Nat) := [(5543704576,109557570849624,109557956762915)]
theorem point_links_checked42265 : (cuts42265.take 1).map (fun c => (5543690241-1+2*2^10*c.k,109557537897392+c.lower,109557923810663+c.upper)) = pointBounds42265 := by
 decide +kernel
def cuts42266 : List PrefixCut := [⟨28,131094491,131094567⟩,
⟨64,299403219,299403389⟩]
theorem checked42266 : checkPrefixCuts (2^48) 5543821313 10 Manual.Count131072.C042266.packed 64 cuts42266 = true := by
 decide +kernel
def pointBounds42266 : List (Nat × Nat × Nat) := [(5543878656,109557967894431,109558353807958)]
theorem point_links_checked42266 : (cuts42266.take 1).map (fun c => (5543821313-1+2*2^10*c.k,109557836799940+c.lower,109558222713391+c.upper)) = pointBounds42266 := by
 decide +kernel
def cuts42267 : List PrefixCut := [⟨49,229586732,229586866⟩,
⟨64,297466837,297467011⟩]
theorem checked42267 : checkPrefixCuts (2^48) 5543952385 10 Manual.Count131072.C042267.packed 64 cuts42267 = true := by
 decide +kernel
def pointBounds42267 : List (Nat × Nat × Nat) := [(5544052736,109558365789891,109558751703646)]
theorem point_links_checked42267 : (cuts42267.take 1).map (fun c => (5543952385-1+2*2^10*c.k,109558136203159+c.lower,109558522116780+c.upper)) = pointBounds42267 := by
 decide +kernel
def cuts42268 : List PrefixCut := [⟨64,296038243,296038417⟩]
theorem checked42268 : checkPrefixCuts (2^48) 5544083457 10 Manual.Count131072.C042268.packed 64 cuts42268 = true := by
 decide +kernel
def cuts42269 : List PrefixCut := [⟨6,27567602,27567617⟩,
⟨64,292731293,292731465⟩]
theorem checked42269 : checkPrefixCuts (2^48) 5544214529 10 Manual.Count131072.C042269.packed 64 cuts42269 = true := by
 decide +kernel
def pointBounds42269 : List (Nat × Nat × Nat) := [(5544226816,109558757275841,109559143189825)]
theorem point_links_checked42269 : (cuts42269.take 1).map (fun c => (5544214529-1+2*2^10*c.k,109558729708239+c.lower,109559115622208+c.upper)) = pointBounds42269 := by
 decide +kernel
def cuts42270 : List PrefixCut := [⟨27,128848333,128848408⟩,
⟨64,300593326,300593501⟩]
theorem checked42270 : checkPrefixCuts (2^48) 5544345601 10 Manual.Count131072.C042270.packed 64 cuts42270 = true := by
 decide +kernel
def pointBounds42270 : List (Nat × Nat × Nat) := [(5544400896,109559151287865,109559537202081)]
theorem point_links_checked42270 : (cuts42270.take 1).map (fun c => (5544345601-1+2*2^10*c.k,109559022439532+c.lower,109559408353673+c.upper)) = pointBounds42270 := by
 decide +kernel
def cuts42271 : List PrefixCut := [⟨48,220325606,220325740⟩,
⟨64,295763394,295763571⟩]
theorem checked42271 : checkPrefixCuts (2^48) 5544476673 10 Manual.Count131072.C042271.packed 64 cuts42271 = true := by
 decide +kernel
def pointBounds42271 : List (Nat × Nat × Nat) := [(5544574976,109559543358464,109559929272914)]
theorem point_links_checked42271 : (cuts42271.take 1).map (fun c => (5544476673-1+2*2^10*c.k,109559323032858+c.lower,109559708947174+c.upper)) = pointBounds42271 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000070
