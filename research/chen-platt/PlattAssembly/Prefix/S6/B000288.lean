import PlattAssemblyKernel
import PlattCertificates.Count131072.C059216
import PlattCertificates.Count131072.C059217
import PlattCertificates.Count131072.C059218
import PlattCertificates.Count131072.C059219
import PlattCertificates.Count131072.C059220
import PlattCertificates.Count131072.C059221
import PlattCertificates.Count131072.C059222
import PlattCertificates.Count131072.C059223
import PlattCertificates.Count131072.C059224
import PlattCertificates.Count131072.C059225
import PlattCertificates.Count131072.C059226
import PlattCertificates.Count131072.C059227
import PlattCertificates.Count131072.C059228
import PlattCertificates.Count131072.C059229
import PlattCertificates.Count131072.C059230
import PlattCertificates.Count131072.C059231
import PlattCertificates.Count131072.C059232
import PlattCertificates.Count131072.C059233
import PlattCertificates.Count131072.C059234
import PlattCertificates.Count131072.C059235
import PlattCertificates.Count131072.C059236
import PlattCertificates.Count131072.C059237
import PlattCertificates.Count131072.C059238
import PlattCertificates.Count131072.C059239
import PlattCertificates.Count131072.C059240
import PlattCertificates.Count131072.C059241
import PlattCertificates.Count131072.C059242
import PlattCertificates.Count131072.C059243
import PlattCertificates.Count131072.C059244
import PlattCertificates.Count131072.C059245
import PlattCertificates.Count131072.C059246
import PlattCertificates.Count131072.C059247
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000288
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts59216 : List PrefixCut := [⟨64,206822987,206823105⟩]
theorem checked59216 : checkPrefixCuts (2^48) 7765491713 10 Manual.Count131072.C059216.packed 64 cuts59216 = true := by
 decide +kernel
def cuts59217 : List PrefixCut := [⟨8,25771075,25771091⟩,
⟨64,209900402,209900526⟩]
theorem checked59217 : checkPrefixCuts (2^48) 7765622785 10 Manual.Count131072.C059217.packed 64 cuts59217 = true := by
 decide +kernel
def pointBounds59217 : List (Nat × Nat × Nat) := [(7765639168,113754555199403,113754943514078)]
theorem point_links_checked59217 : (cuts59217.take 1).map (fun c => (7765622785-1+2*2^10*c.k,113754529428328+c.lower,113754917742987+c.upper)) = pointBounds59217 := by
 decide +kernel
def cuts59218 : List PrefixCut := [⟨63,207939644,207939767⟩,
⟨64,211491660,211491784⟩]
theorem checked59218 : checkPrefixCuts (2^48) 7765753857 10 Manual.Count131072.C059218.packed 64 cuts59218 = true := by
 decide +kernel
def pointBounds59218 : List (Nat × Nat × Nat) := [(7765882880,113754947268374,113755335583280)]
theorem point_links_checked59218 : (cuts59218.take 1).map (fun c => (7765753857-1+2*2^10*c.k,113754739328730+c.lower,113755127643513+c.upper)) = pointBounds59218 := by
 decide +kernel
def cuts59219 : List PrefixCut := [⟨64,207102478,207102598⟩]
theorem checked59219 : checkPrefixCuts (2^48) 7765884929 10 Manual.Count131072.C059219.packed 64 cuts59219 = true := by
 decide +kernel
def cuts59220 : List PrefixCut := [⟨54,177415269,177415370⟩,
⟨64,209527343,209527461⟩]
theorem checked59220 : checkPrefixCuts (2^48) 7766016001 10 Manual.Count131072.C059220.packed 64 cuts59220 = true := by
 decide +kernel
def pointBounds59220 : List (Nat × Nat × Nat) := [(7766126592,113755335338137,113755723653265)]
theorem point_links_checked59220 : (cuts59220.take 1).map (fun c => (7766016001-1+2*2^10*c.k,113755157922868+c.lower,113755546237895+c.upper)) = pointBounds59220 := by
 decide +kernel
def cuts59221 : List PrefixCut := [⟨64,207820344,207820460⟩]
theorem checked59221 : checkPrefixCuts (2^48) 7766147073 10 Manual.Count131072.C059221.packed 64 cuts59221 = true := by
 decide +kernel
def cuts59222 : List PrefixCut := [⟨45,145044496,145044581⟩,
⟨64,207526905,207527024⟩]
theorem checked59222 : checkPrefixCuts (2^48) 7766278145 10 Manual.Count131072.C059222.packed 64 cuts59222 = true := by
 decide +kernel
def pointBounds59222 : List (Nat × Nat × Nat) := [(7766370304,113755720315051,113756108630397)]
theorem point_links_checked59222 : (cuts59222.take 1).map (fun c => (7766278145-1+2*2^10*c.k,113755575270555+c.lower,113755963585816+c.upper)) = pointBounds59222 := by
 decide +kernel
def cuts59223 : List PrefixCut := [⟨64,210350314,210350433⟩]
theorem checked59223 : checkPrefixCuts (2^48) 7766409217 10 Manual.Count131072.C059223.packed 64 cuts59223 = true := by
 decide +kernel
def cuts59224 : List PrefixCut := [⟨36,115937591,115937656⟩,
⟨64,206142722,206142842⟩]
theorem checked59224 : checkPrefixCuts (2^48) 7766540289 10 Manual.Count131072.C059224.packed 64 cuts59224 = true := by
 decide +kernel
def pointBounds59224 : List (Nat × Nat × Nat) := [(7766614016,113756109085365,113756497400929)]
theorem point_links_checked59224 : (cuts59224.take 1).map (fun c => (7766540289-1+2*2^10*c.k,113755993147774+c.lower,113756381463273+c.upper)) = pointBounds59224 := by
 decide +kernel
def cuts59225 : List PrefixCut := [⟨64,208531142,208531260⟩]
theorem checked59225 : checkPrefixCuts (2^48) 7766671361 10 Manual.Count131072.C059225.packed 64 cuts59225 = true := by
 decide +kernel
def cuts59226 : List PrefixCut := [⟨27,88173483,88173532⟩,
⟨64,210339658,210339776⟩]
theorem checked59226 : checkPrefixCuts (2^48) 7766802433 10 Manual.Count131072.C059226.packed 64 cuts59226 = true := by
 decide +kernel
def pointBounds59226 : List (Nat × Nat × Nat) := [(7766857728,113756495995121,113756884310907)]
theorem point_links_checked59226 : (cuts59226.take 1).map (fun c => (7766802433-1+2*2^10*c.k,113756407821638+c.lower,113756796137375+c.upper)) = pointBounds59226 := by
 decide +kernel
def cuts59227 : List PrefixCut := [⟨64,211568256,211568380⟩]
theorem checked59227 : checkPrefixCuts (2^48) 7766933505 10 Manual.Count131072.C059227.packed 64 cuts59227 = true := by
 decide +kernel
def cuts59228 : List PrefixCut := [⟨18,60664858,60664891⟩,
⟨64,210405045,210405167⟩]
theorem checked59228 : checkPrefixCuts (2^48) 7767064577 10 Manual.Count131072.C059228.packed 64 cuts59228 = true := by
 decide +kernel
def pointBounds59228 : List (Nat × Nat × Nat) := [(7767101440,113756890394410,113757278710422)]
theorem point_links_checked59228 : (cuts59228.take 1).map (fun c => (7767064577-1+2*2^10*c.k,113756829729552+c.lower,113757218045531+c.upper)) = pointBounds59228 := by
 decide +kernel
def cuts59229 : List PrefixCut := [⟨64,207031313,207031430⟩]
theorem checked59229 : checkPrefixCuts (2^48) 7767195649 10 Manual.Count131072.C059229.packed 64 cuts59229 = true := by
 decide +kernel
def cuts59230 : List PrefixCut := [⟨9,29534198,29534216⟩,
⟨64,210108033,210108153⟩]
theorem checked59230 : checkPrefixCuts (2^48) 7767326721 10 Manual.Count131072.C059230.packed 64 cuts59230 = true := by
 decide +kernel
def pointBounds59230 : List (Nat × Nat × Nat) := [(7767345152,113757276700108,113757665016344)]
theorem point_links_checked59230 : (cuts59230.take 1).map (fun c => (7767326721-1+2*2^10*c.k,113757247165910+c.lower,113757635482128+c.upper)) = pointBounds59230 := by
 decide +kernel
def cuts59231 : List PrefixCut := [⟨64,208111426,208111545⟩]
theorem checked59231 : checkPrefixCuts (2^48) 7767457793 10 Manual.Count131072.C059231.packed 64 cuts59231 = true := by
 decide +kernel
def pointBounds59231 : List (Nat × Nat × Nat) := [(7767588864,113757665385369,113758053701826)]
theorem point_links_checked59231 : (cuts59231.take 1).map (fun c => (7767457793-1+2*2^10*c.k,113757457273943+c.lower,113757845590281+c.upper)) = pointBounds59231 := by
 decide +kernel
def cuts59232 : List PrefixCut := [⟨64,205607577,205607693⟩]
theorem checked59232 : checkPrefixCuts (2^48) 7767588865 10 Manual.Count131072.C059232.packed 64 cuts59232 = true := by
 decide +kernel
def cuts59233 : List PrefixCut := [⟨55,181326085,181326187⟩,
⟨64,210785887,210786006⟩]
theorem checked59233 : checkPrefixCuts (2^48) 7767719937 10 Manual.Count131072.C059233.packed 64 cuts59233 = true := by
 decide +kernel
def pointBounds59233 : List (Nat × Nat × Nat) := [(7767832576,113758052319031,113758440635706)]
theorem point_links_checked59233 : (cuts59233.take 1).map (fun c => (7767719937-1+2*2^10*c.k,113757870992946+c.lower,113758259309519+c.upper)) = pointBounds59233 := by
 decide +kernel
def cuts59234 : List PrefixCut := [⟨64,208390761,208390886⟩]
theorem checked59234 : checkPrefixCuts (2^48) 7767851009 10 Manual.Count131072.C059234.packed 64 cuts59234 = true := by
 decide +kernel
def cuts59235 : List PrefixCut := [⟨46,150049330,150049411⟩,
⟨64,208677136,208677252⟩]
theorem checked59235 : checkPrefixCuts (2^48) 7767982081 10 Manual.Count131072.C059235.packed 64 cuts59235 = true := by
 decide +kernel
def pointBounds59235 : List (Nat × Nat × Nat) := [(7768076288,113758440218924,113758828535822)]
theorem point_links_checked59235 : (cuts59235.take 1).map (fun c => (7767982081-1+2*2^10*c.k,113758290169594+c.lower,113758678486411+c.upper)) = pointBounds59235 := by
 decide +kernel
def cuts59236 : List PrefixCut := [⟨64,211789780,211789897⟩]
theorem checked59236 : checkPrefixCuts (2^48) 7768113153 10 Manual.Count131072.C059236.packed 64 cuts59236 = true := by
 decide +kernel
def cuts59237 : List PrefixCut := [⟨37,121999427,121999493⟩,
⟨64,206532326,206532442⟩]
theorem checked59237 : checkPrefixCuts (2^48) 7768244225 10 Manual.Count131072.C059237.packed 64 cuts59237 = true := by
 decide +kernel
def pointBounds59237 : List (Nat × Nat × Nat) := [(7768320000,113758832635937,113759220953053)]
theorem point_links_checked59237 : (cuts59237.take 1).map (fun c => (7768244225-1+2*2^10*c.k,113758710636510+c.lower,113759098953560+c.upper)) = pointBounds59237 := by
 decide +kernel
def cuts59238 : List PrefixCut := [⟨64,209101381,209101499⟩]
theorem checked59238 : checkPrefixCuts (2^48) 7768375297 10 Manual.Count131072.C059238.packed 64 cuts59238 = true := by
 decide +kernel
def cuts59239 : List PrefixCut := [⟨28,90074456,90074508⟩,
⟨64,207576073,207576192⟩]
theorem checked59239 : checkPrefixCuts (2^48) 7768506369 10 Manual.Count131072.C059239.packed 64 cuts59239 = true := by
 decide +kernel
def pointBounds59239 : List (Nat × Nat × Nat) := [(7768563712,113759216344673,113759604662009)]
theorem point_links_checked59239 : (cuts59239.take 1).map (fun c => (7768506369-1+2*2^10*c.k,113759126270217+c.lower,113759514587501+c.upper)) = pointBounds59239 := by
 decide +kernel
def cuts59240 : List PrefixCut := [⟨64,206304451,206304573⟩]
theorem checked59240 : checkPrefixCuts (2^48) 7768637441 10 Manual.Count131072.C059240.packed 64 cuts59240 = true := by
 decide +kernel
def cuts59241 : List PrefixCut := [⟨19,62535579,62535616⟩,
⟨64,210684971,210685089⟩]
theorem checked59241 : checkPrefixCuts (2^48) 7768768513 10 Manual.Count131072.C059241.packed 64 cuts59241 = true := by
 decide +kernel
def pointBounds59241 : List (Nat × Nat × Nat) := [(7768807424,113759602686320,113759991003882)]
theorem point_links_checked59241 : (cuts59241.take 1).map (fun c => (7768768513-1+2*2^10*c.k,113759540150741+c.lower,113759928468266+c.upper)) = pointBounds59241 := by
 decide +kernel
def cuts59242 : List PrefixCut := [⟨64,207311961,207312075⟩]
theorem checked59242 : checkPrefixCuts (2^48) 7768899585 10 Manual.Count131072.C059242.packed 64 cuts59242 = true := by
 decide +kernel
def cuts59243 : List PrefixCut := [⟨10,32788446,32788464⟩,
⟨64,209409801,209409918⟩]
theorem checked59243 : checkPrefixCuts (2^48) 7769030657 10 Manual.Count131072.C059243.packed 64 cuts59243 = true := by
 decide +kernel
def pointBounds59243 : List (Nat × Nat × Nat) := [(7769051136,113759990936119,113760379253894)]
theorem point_links_checked59243 : (cuts59243.take 1).map (fun c => (7769030657-1+2*2^10*c.k,113759958147673+c.lower,113760346465430+c.upper)) = pointBounds59243 := by
 decide +kernel
def cuts59244 : List PrefixCut := [⟨64,210058408,210058528⟩]
theorem checked59244 : checkPrefixCuts (2^48) 7769161729 10 Manual.Count131072.C059244.packed 64 cuts59244 = true := by
 decide +kernel
def cuts59245 : List PrefixCut := [⟨1,3369311,3369313⟩,
⟨64,211069275,211069394⟩]
theorem checked59245 : checkPrefixCuts (2^48) 7769292801 10 Manual.Count131072.C059245.packed 64 cuts59245 = true := by
 decide +kernel
def pointBounds59245 : List (Nat × Nat × Nat) := [(7769294848,113760380985193,113760769303189)]
theorem point_links_checked59245 : (cuts59245.take 1).map (fun c => (7769292801-1+2*2^10*c.k,113760377615882+c.lower,113760765933876+c.upper)) = pointBounds59245 := by
 decide +kernel
def cuts59246 : List PrefixCut := [⟨56,183278836,183278935⟩,
⟨64,208855781,208855896⟩]
theorem checked59246 : checkPrefixCuts (2^48) 7769423873 10 Manual.Count131072.C059246.packed 64 cuts59246 = true := by
 decide +kernel
def pointBounds59246 : List (Nat × Nat × Nat) := [(7769538560,113760771963993,113761160282205)]
theorem point_links_checked59246 : (cuts59246.take 1).map (fun c => (7769423873-1+2*2^10*c.k,113760588685157+c.lower,113760977003270+c.upper)) = pointBounds59246 := by
 decide +kernel
def cuts59247 : List PrefixCut := [⟨64,207620535,207620651⟩]
theorem checked59247 : checkPrefixCuts (2^48) 7769554945 10 Manual.Count131072.C059247.packed 64 cuts59247 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000288
