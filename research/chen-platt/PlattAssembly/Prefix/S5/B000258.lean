import PlattAssemblyKernel
import PlattCertificates.Count131072.C048256
import PlattCertificates.Count131072.C048257
import PlattCertificates.Count131072.C048258
import PlattCertificates.Count131072.C048259
import PlattCertificates.Count131072.C048260
import PlattCertificates.Count131072.C048261
import PlattCertificates.Count131072.C048262
import PlattCertificates.Count131072.C048263
import PlattCertificates.Count131072.C048264
import PlattCertificates.Count131072.C048265
import PlattCertificates.Count131072.C048266
import PlattCertificates.Count131072.C048267
import PlattCertificates.Count131072.C048268
import PlattCertificates.Count131072.C048269
import PlattCertificates.Count131072.C048270
import PlattCertificates.Count131072.C048271
import PlattCertificates.Count131072.C048272
import PlattCertificates.Count131072.C048273
import PlattCertificates.Count131072.C048274
import PlattCertificates.Count131072.C048275
import PlattCertificates.Count131072.C048276
import PlattCertificates.Count131072.C048277
import PlattCertificates.Count131072.C048278
import PlattCertificates.Count131072.C048279
import PlattCertificates.Count131072.C048280
import PlattCertificates.Count131072.C048281
import PlattCertificates.Count131072.C048282
import PlattCertificates.Count131072.C048283
import PlattCertificates.Count131072.C048284
import PlattCertificates.Count131072.C048285
import PlattCertificates.Count131072.C048286
import PlattCertificates.Count131072.C048287
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000258
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48256 : List PrefixCut := [⟨12,48610248,48610276⟩,
⟨64,258303713,258303860⟩]
theorem checked48256 : checkPrefixCuts (2^48) 6328942593 10 Manual.Count131072.C048256.packed 64 cuts48256 = true := by
 decide +kernel
def pointBounds48256 : List (Nat × Nat × Nat) := [(6328967168,111214772317091,111215159186958)]
theorem point_links_checked48256 : (cuts48256.take 1).map (fun c => (6328942593-1+2*2^10*c.k,111214723706843+c.lower,111215110576682+c.upper)) = pointBounds48256 := by
 decide +kernel
def cuts48257 : List PrefixCut := [⟨45,182517176,182517278⟩,
⟨64,259098877,259099023⟩]
theorem checked48257 : checkPrefixCuts (2^48) 6329073665 10 Manual.Count131072.C048257.packed 64 cuts48257 = true := by
 decide +kernel
def pointBounds48257 : List (Nat × Nat × Nat) := [(6329165824,111215164527732,111215551397820)]
theorem point_links_checked48257 : (cuts48257.take 1).map (fun c => (6329073665-1+2*2^10*c.k,111214982010556+c.lower,111215368880542+c.upper)) = pointBounds48257 := by
 decide +kernel
def cuts48258 : List PrefixCut := [⟨64,259137940,259138089⟩]
theorem checked48258 : checkPrefixCuts (2^48) 6329204737 10 Manual.Count131072.C048258.packed 64 cuts48258 = true := by
 decide +kernel
def cuts48259 : List PrefixCut := [⟨14,56878887,56878919⟩,
⟨64,259844129,259844277⟩]
theorem checked48259 : checkPrefixCuts (2^48) 6329335809 10 Manual.Count131072.C048259.packed 64 cuts48259 = true := by
 decide +kernel
def pointBounds48259 : List (Nat × Nat × Nat) := [(6329364480,111215557126260,111215943996573)]
theorem point_links_checked48259 : (cuts48259.take 1).map (fun c => (6329335809-1+2*2^10*c.k,111215500247373+c.lower,111215887117654+c.upper)) = pointBounds48259 := by
 decide +kernel
def cuts48260 : List PrefixCut := [⟨47,187041747,187041850⟩,
⟨64,254591307,254591447⟩]
theorem checked48260 : checkPrefixCuts (2^48) 6329466881 10 Manual.Count131072.C048260.packed 64 cuts48260 = true := by
 decide +kernel
def pointBounds48260 : List (Nat × Nat × Nat) := [(6329563136,111215947133249,111216334003781)]
theorem point_links_checked48260 : (cuts48260.take 1).map (fun c => (6329466881-1+2*2^10*c.k,111215760091502+c.lower,111216146961931+c.upper)) = pointBounds48260 := by
 decide +kernel
def cuts48261 : List PrefixCut := [⟨64,258721657,258721804⟩]
theorem checked48261 : checkPrefixCuts (2^48) 6329597953 10 Manual.Count131072.C048261.packed 64 cuts48261 = true := by
 decide +kernel
def cuts48262 : List PrefixCut := [⟨16,65102026,65102062⟩,
⟨64,255736917,255737065⟩]
theorem checked48262 : checkPrefixCuts (2^48) 6329729025 10 Manual.Count131072.C048262.packed 64 cuts48262 = true := by
 decide +kernel
def pointBounds48262 : List (Nat × Nat × Nat) := [(6329761792,111216338506492,111216725377244)]
theorem point_links_checked48262 : (cuts48262.take 1).map (fun c => (6329729025-1+2*2^10*c.k,111216273404466+c.lower,111216660275182+c.upper)) = pointBounds48262 := by
 decide +kernel
def cuts48263 : List PrefixCut := [⟨49,196857346,196857456⟩,
⟨64,256354165,256354306⟩]
theorem checked48263 : checkPrefixCuts (2^48) 6329860097 10 Manual.Count131072.C048263.packed 64 cuts48263 = true := by
 decide +kernel
def pointBounds48263 : List (Nat × Nat × Nat) := [(6329960448,111216725998729,111217112869703)]
theorem point_links_checked48263 : (cuts48263.take 1).map (fun c => (6329860097-1+2*2^10*c.k,111216529141383+c.lower,111216916012247+c.upper)) = pointBounds48263 := by
 decide +kernel
def cuts48264 : List PrefixCut := [⟨64,258083039,258083186⟩]
theorem checked48264 : checkPrefixCuts (2^48) 6329991169 10 Manual.Count131072.C048264.packed 64 cuts48264 = true := by
 decide +kernel
def cuts48265 : List PrefixCut := [⟨18,71234241,71234282⟩,
⟨64,254564924,254565067⟩]
theorem checked48265 : checkPrefixCuts (2^48) 6330122241 10 Manual.Count131072.C048265.packed 64 cuts48265 = true := by
 decide +kernel
def pointBounds48265 : List (Nat × Nat × Nat) := [(6330159104,111217114812828,111217501684021)]
theorem point_links_checked48265 : (cuts48265.take 1).map (fun c => (6330122241-1+2*2^10*c.k,111217043578587+c.lower,111217430449739+c.upper)) = pointBounds48265 := by
 decide +kernel
def cuts48266 : List PrefixCut := [⟨51,203781558,203781672⟩,
⟨64,256605030,256605173⟩]
theorem checked48266 : checkPrefixCuts (2^48) 6330253313 10 Manual.Count131072.C048266.packed 64 cuts48266 = true := by
 decide +kernel
def pointBounds48266 : List (Nat × Nat × Nat) := [(6330357760,111217501925069,111217888796478)]
theorem point_links_checked48266 : (cuts48266.take 1).map (fun c => (6330253313-1+2*2^10*c.k,111217298143511+c.lower,111217685014806+c.upper)) = pointBounds48266 := by
 decide +kernel
def cuts48267 : List PrefixCut := [⟨64,259089655,259089805⟩]
theorem checked48267 : checkPrefixCuts (2^48) 6330384385 10 Manual.Count131072.C048267.packed 64 cuts48267 = true := by
 decide +kernel
def cuts48268 : List PrefixCut := [⟨20,80166869,80166914⟩,
⟨64,258017198,258017345⟩]
theorem checked48268 : checkPrefixCuts (2^48) 6330515457 10 Manual.Count131072.C048268.packed 64 cuts48268 = true := by
 decide +kernel
def pointBounds48268 : List (Nat × Nat × Nat) := [(6330556416,111217894005065,111218280876698)]
theorem point_links_checked48268 : (cuts48268.take 1).map (fun c => (6330515457-1+2*2^10*c.k,111217813838196+c.lower,111218200709784+c.upper)) = pointBounds48268 := by
 decide +kernel
def cuts48269 : List PrefixCut := [⟨53,212038735,212038856⟩,
⟨64,256500160,256500307⟩]
theorem checked48269 : checkPrefixCuts (2^48) 6330646529 10 Manual.Count131072.C048269.packed 64 cuts48269 = true := by
 decide +kernel
def pointBounds48269 : List (Nat × Nat × Nat) := [(6330755072,111218283894129,111218670765985)]
theorem point_links_checked48269 : (cuts48269.take 1).map (fun c => (6330646529-1+2*2^10*c.k,111218071855394+c.lower,111218458727129+c.upper)) = pointBounds48269 := by
 decide +kernel
def cuts48270 : List PrefixCut := [⟨64,261385546,261385692⟩]
theorem checked48270 : checkPrefixCuts (2^48) 6330777601 10 Manual.Count131072.C048270.packed 64 cuts48270 = true := by
 decide +kernel
def cuts48271 : List PrefixCut := [⟨22,89142840,89142893⟩,
⟨64,255867104,255867255⟩]
theorem checked48271 : checkPrefixCuts (2^48) 6330908673 10 Manual.Count131072.C048271.packed 64 cuts48271 = true := by
 decide +kernel
def pointBounds48271 : List (Nat × Nat × Nat) := [(6330953728,111218678883940,111219065756021)]
theorem point_links_checked48271 : (cuts48271.take 1).map (fun c => (6330908673-1+2*2^10*c.k,111218589741100+c.lower,111218976613128+c.upper)) = pointBounds48271 := by
 decide +kernel
def cuts48272 : List PrefixCut := [⟨55,225496612,225496738⟩,
⟨64,261152448,261152594⟩]
theorem checked48272 : checkPrefixCuts (2^48) 6331039745 10 Manual.Count131072.C048272.packed 64 cuts48272 = true := by
 decide +kernel
def pointBounds48272 : List (Nat × Nat × Nat) := [(6331152384,111219071104816,111219457977121)]
theorem point_links_checked48272 : (cuts48272.take 1).map (fun c => (6331039745-1+2*2^10*c.k,111218845608204+c.lower,111219232480383+c.upper)) = pointBounds48272 := by
 decide +kernel
def cuts48273 : List PrefixCut := [⟨64,259279787,259279931⟩]
theorem checked48273 : checkPrefixCuts (2^48) 6331170817 10 Manual.Count131072.C048273.packed 64 cuts48273 = true := by
 decide +kernel
def cuts48274 : List PrefixCut := [⟨24,94916749,94916804⟩,
⟨64,256962633,256962781⟩]
theorem checked48274 : checkPrefixCuts (2^48) 6331301889 10 Manual.Count131072.C048274.packed 64 cuts48274 = true := by
 decide +kernel
def pointBounds48274 : List (Nat × Nat × Nat) := [(6331351040,111219460957188,111219847829712)]
theorem point_links_checked48274 : (cuts48274.take 1).map (fun c => (6331301889-1+2*2^10*c.k,111219366040439+c.lower,111219752912908+c.upper)) = pointBounds48274 := by
 decide +kernel
def cuts48275 : List PrefixCut := [⟨57,229883714,229883844⟩,
⟨64,258379931,258380077⟩]
theorem checked48275 : checkPrefixCuts (2^48) 6331432961 10 Manual.Count131072.C048275.packed 64 cuts48275 = true := by
 decide +kernel
def pointBounds48275 : List (Nat × Nat × Nat) := [(6331549696,111219852886786,111220239759533)]
theorem point_links_checked48275 : (cuts48275.take 1).map (fun c => (6331432961-1+2*2^10*c.k,111219623003072+c.lower,111220009875689+c.upper)) = pointBounds48275 := by
 decide +kernel
def cuts48276 : List PrefixCut := [⟨64,260375053,260375199⟩]
theorem checked48276 : checkPrefixCuts (2^48) 6331564033 10 Manual.Count131072.C048276.packed 64 cuts48276 = true := by
 decide +kernel
def cuts48277 : List PrefixCut := [⟨26,103090491,103090551⟩,
⟨64,256768849,256768996⟩]
theorem checked48277 : checkPrefixCuts (2^48) 6331695105 10 Manual.Count131072.C048277.packed 64 cuts48277 = true := by
 decide +kernel
def pointBounds48277 : List (Nat × Nat × Nat) := [(6331748352,111220244848547,111220631721516)]
theorem point_links_checked48277 : (cuts48277.take 1).map (fun c => (6331695105-1+2*2^10*c.k,111220141758056+c.lower,111220528630965+c.upper)) = pointBounds48277 := by
 decide +kernel
def cuts48278 : List PrefixCut := [⟨59,240315933,240316070⟩,
⟨64,260808811,260808960⟩]
theorem checked48278 : checkPrefixCuts (2^48) 6331826177 10 Manual.Count131072.C048278.packed 64 cuts48278 = true := by
 decide +kernel
def pointBounds48278 : List (Nat × Nat × Nat) := [(6331947008,111220638842838,111221025716031)]
theorem point_links_checked48278 : (cuts48278.take 1).map (fun c => (6331826177-1+2*2^10*c.k,111220398526905+c.lower,111220785399961+c.upper)) = pointBounds48278 := by
 decide +kernel
def cuts48279 : List PrefixCut := [⟨64,256580390,256580539⟩]
theorem checked48279 : checkPrefixCuts (2^48) 6331957249 10 Manual.Count131072.C048279.packed 64 cuts48279 = true := by
 decide +kernel
def cuts48280 : List PrefixCut := [⟨28,113085740,113085803⟩,
⟨64,259820075,259820221⟩]
theorem checked48280 : checkPrefixCuts (2^48) 6332088321 10 Manual.Count131072.C048280.packed 64 cuts48280 = true := by
 decide +kernel
def pointBounds48280 : List (Nat × Nat × Nat) := [(6332145664,111221029001846,111221415875263)]
theorem point_links_checked48280 : (cuts48280.take 1).map (fun c => (6332088321-1+2*2^10*c.k,111220915916106+c.lower,111221302789460+c.upper)) = pointBounds48280 := by
 decide +kernel
def cuts48281 : List PrefixCut := [⟨61,245057150,245057292⟩,
⟨64,256969837,256969986⟩]
theorem checked48281 : checkPrefixCuts (2^48) 6332219393 10 Manual.Count131072.C048281.packed 64 cuts48281 = true := by
 decide +kernel
def pointBounds48281 : List (Nat × Nat × Nat) := [(6332344320,111221420793331,111221807666973)]
theorem point_links_checked48281 : (cuts48281.take 1).map (fun c => (6332219393-1+2*2^10*c.k,111221175736181+c.lower,111221562609681+c.upper)) = pointBounds48281 := by
 decide +kernel
def cuts48282 : List PrefixCut := [⟨64,260253844,260253995⟩]
theorem checked48282 : checkPrefixCuts (2^48) 6332350465 10 Manual.Count131072.C048282.packed 64 cuts48282 = true := by
 decide +kernel
def cuts48283 : List PrefixCut := [⟨30,120279445,120279517⟩,
⟨64,257537057,257537209⟩]
theorem checked48283 : checkPrefixCuts (2^48) 6332481537 10 Manual.Count131072.C048283.packed 64 cuts48283 = true := by
 decide +kernel
def pointBounds48283 : List (Nat × Nat × Nat) := [(6332542976,111221813239307,111222200113179)]
theorem point_links_checked48283 : (cuts48283.take 1).map (fun c => (6332481537-1+2*2^10*c.k,111221692959862+c.lower,111222079833662+c.upper)) = pointBounds48283 := by
 decide +kernel
def cuts48284 : List PrefixCut := [⟨63,254820431,254820575⟩,
⟨64,258909606,258909752⟩]
theorem checked48284 : checkPrefixCuts (2^48) 6332612609 10 Manual.Count131072.C048284.packed 64 cuts48284 = true := by
 decide +kernel
def pointBounds48284 : List (Nat × Nat × Nat) := [(6332741632,111222205317350,111222592191446)]
theorem point_links_checked48284 : (cuts48284.take 1).map (fun c => (6332612609-1+2*2^10*c.k,111221950496919+c.lower,111222337370871+c.upper)) = pointBounds48284 := by
 decide +kernel
def cuts48285 : List PrefixCut := [⟨64,257881964,257882110⟩]
theorem checked48285 : checkPrefixCuts (2^48) 6332743681 10 Manual.Count131072.C048285.packed 64 cuts48285 = true := by
 decide +kernel
def cuts48286 : List PrefixCut := [⟨32,128450075,128450151⟩,
⟨64,256098803,256098949⟩]
theorem checked48286 : checkPrefixCuts (2^48) 6332874753 10 Manual.Count131072.C048286.packed 64 cuts48286 = true := by
 decide +kernel
def pointBounds48286 : List (Nat × Nat × Nat) := [(6332940288,111222595738564,111222982612884)]
theorem point_links_checked48286 : (cuts48286.take 1).map (fun c => (6332874753-1+2*2^10*c.k,111222467288489+c.lower,111222854162733+c.upper)) = pointBounds48286 := by
 decide +kernel
def cuts48287 : List PrefixCut := [⟨64,254493478,254493621⟩]
theorem checked48287 : checkPrefixCuts (2^48) 6333005825 10 Manual.Count131072.C048287.packed 64 cuts48287 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000258
