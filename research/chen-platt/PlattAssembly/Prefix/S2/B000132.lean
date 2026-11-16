import PlattAssemblyKernel
import PlattCertificates.Count131072.C014224
import PlattCertificates.Count131072.C014225
import PlattCertificates.Count131072.C014226
import PlattCertificates.Count131072.C014227
import PlattCertificates.Count131072.C014228
import PlattCertificates.Count131072.C014229
import PlattCertificates.Count131072.C014230
import PlattCertificates.Count131072.C014231
import PlattCertificates.Count131072.C014232
import PlattCertificates.Count131072.C014233
import PlattCertificates.Count131072.C014234
import PlattCertificates.Count131072.C014235
import PlattCertificates.Count131072.C014236
import PlattCertificates.Count131072.C014237
import PlattCertificates.Count131072.C014238
import PlattCertificates.Count131072.C014239
import PlattCertificates.Count131072.C014240
import PlattCertificates.Count131072.C014241
import PlattCertificates.Count131072.C014242
import PlattCertificates.Count131072.C014243
import PlattCertificates.Count131072.C014244
import PlattCertificates.Count131072.C014245
import PlattCertificates.Count131072.C014246
import PlattCertificates.Count131072.C014247
import PlattCertificates.Count131072.C014248
import PlattCertificates.Count131072.C014249
import PlattCertificates.Count131072.C014250
import PlattCertificates.Count131072.C014251
import PlattCertificates.Count131072.C014252
import PlattCertificates.Count131072.C014253
import PlattCertificates.Count131072.C014254
import PlattCertificates.Count131072.C014255
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000132
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14224 : List PrefixCut := [⟨54,388541965,388542229⟩,
⟨112,812475030,812475581⟩,
⟨128,927118435,927119067⟩]
theorem checked14224 : checkPrefixCuts (2^48) 1868300289 9 Manual.Count131072.C014224.packed 128 cuts14224 = true := by
 decide +kernel
def pointBounds14224 : List (Nat × Nat × Nat) := [(1868355584,95571119021690,95571496584152),(1868414976,95571542954755,95571920517504)]
theorem point_links_checked14224 : (cuts14224.take 2).map (fun c => (1868300289-1+2*2^9*c.k,95570730479725+c.lower,95571108041923+c.upper)) = pointBounds14224 := by
 decide +kernel
def cuts14225 : List PrefixCut := [⟨42,305510035,305510243⟩,
⟨100,727759122,727759619⟩,
⟨128,928108024,928108663⟩]
theorem checked14225 : checkPrefixCuts (2^48) 1868431361 9 Manual.Count131072.C014225.packed 128 cuts14225 = true := by
 decide +kernel
def pointBounds14225 : List (Nat × Nat × Nat) := [(1868474368,95571963108195,95572340671233),(1868533760,95572385357282,95572762920609)]
theorem point_links_checked14225 : (cuts14225.take 2).map (fun c => (1868431361-1+2*2^9*c.k,95571657598160+c.lower,95572035160990+c.upper)) = pointBounds14225 := by
 decide +kernel
def cuts14226 : List PrefixCut := [⟨30,211944728,211944874⟩,
⟨88,636878287,636878730⟩,
⟨128,928795761,928796405⟩]
theorem checked14226 : checkPrefixCuts (2^48) 1868562433 9 Manual.Count131072.C014226.packed 128 cuts14226 = true := by
 decide +kernel
def pointBounds14226 : List (Nat × Nat × Nat) := [(1868593152,95572797650912,95573175214527),(1868652544,95573222584471,95573600148383)]
theorem point_links_checked14226 : (cuts14226.take 2).map (fun c => (1868562433-1+2*2^9*c.k,95572585706184+c.lower,95572963269653+c.upper)) = pointBounds14226 := by
 decide +kernel
def cuts14227 : List PrefixCut := [⟨18,127278814,127278902⟩,
⟨76,547817300,547817678⟩,
⟨128,922404608,922405241⟩]
theorem checked14227 : checkPrefixCuts (2^48) 1868693505 9 Manual.Count131072.C014227.packed 128 cuts14227 = true := by
 decide +kernel
def pointBounds14227 : List (Nat × Nat × Nat) := [(1868711936,95573641780759,95574019344960),(1868771328,95574062319245,95574439883736)]
theorem point_links_checked14227 : (cuts14227.take 2).map (fun c => (1868693505-1+2*2^9*c.k,95573514501945+c.lower,95573892066058+c.upper)) = pointBounds14227 := by
 decide +kernel
def cuts14228 : List PrefixCut := [⟨6,40666251,40666280⟩,
⟨64,470666624,470666947⟩,
⟨122,889357764,889358376⟩,
⟨128,932430989,932431631⟩]
theorem checked14228 : checkPrefixCuts (2^48) 1868824577 9 Manual.Count131072.C014228.packed 128 cuts14228 = true := by
 decide +kernel
def pointBounds14228 : List (Nat × Nat × Nat) := [(1868830720,95574477572804,95574855137579),(1868890112,95574907573177,95575285138246),(1868949504,95575326264317,95575703829675)]
theorem point_links_checked14228 : (cuts14228.take 3).map (fun c => (1868824577-1+2*2^9*c.k,95574436906553+c.lower,95574814471299+c.upper)) = pointBounds14228 := by
 decide +kernel
def cuts14229 : List PrefixCut := [⟨52,371387790,371388048⟩,
⟨110,781769406,781769949⟩,
⟨128,904806031,904806659⟩]
theorem checked14229 : checkPrefixCuts (2^48) 1868955649 9 Manual.Count131072.C014229.packed 128 cuts14229 = true := by
 decide +kernel
def pointBounds14229 : List (Nat × Nat × Nat) := [(1869008896,95575740725332,95576118290978),(1869068288,95576151106948,95576528672879)]
theorem point_links_checked14229 : (cuts14229.take 2).map (fun c => (1868955649-1+2*2^9*c.k,95575369337542+c.lower,95575746902930+c.upper)) = pointBounds14229 := by
 decide +kernel
def cuts14230 : List PrefixCut := [⟨40,290494302,290494504⟩,
⟨98,709584006,709584499⟩,
⟨128,928987130,928987774⟩]
theorem checked14230 : checkPrefixCuts (2^48) 1869086721 9 Manual.Count131072.C014230.packed 128 cuts14230 = true := by
 decide +kernel
def pointBounds14230 : List (Nat × Nat × Nat) := [(1869127680,95576564637875,95576942204093),(1869187072,95576983727579,95577361294088)]
theorem point_links_checked14230 : (cuts14230.take 2).map (fun c => (1869086721-1+2*2^9*c.k,95576274143573+c.lower,95576651709589+c.upper)) = pointBounds14230 := by
 decide +kernel
def cuts14231 : List PrefixCut := [⟨28,198318026,198318164⟩,
⟨86,621296188,621296616⟩,
⟨128,922597779,922598416⟩]
theorem checked14231 : checkPrefixCuts (2^48) 1869217793 9 Manual.Count131072.C014231.packed 128 cuts14231 = true := by
 decide +kernel
def pointBounds14231 : List (Nat × Nat × Nat) := [(1869246464,95577401448729,95577779015527),(1869305856,95577824426891,95578201993979)]
theorem point_links_checked14231 : (cuts14231.take 2).map (fun c => (1869217793-1+2*2^9*c.k,95577203130703+c.lower,95577580697363+c.upper)) = pointBounds14231 := by
 decide +kernel
def cuts14232 : List PrefixCut := [⟨16,114435559,114435638⟩,
⟨74,536634039,536634408⟩,
⟨128,924791756,924792395⟩]
theorem checked14232 : checkPrefixCuts (2^48) 1869348865 9 Manual.Count131072.C014232.packed 128 cuts14232 = true := by
 decide +kernel
def pointBounds14232 : List (Nat × Nat × Nat) := [(1869365248,95578240164041,95578617731417),(1869424640,95578662362521,95579039930187)]
theorem point_links_checked14232 : (cuts14232.take 2).map (fun c => (1869348865-1+2*2^9*c.k,95578125728482+c.lower,95578503295779+c.upper)) = pointBounds14232 := by
 decide +kernel
def cuts14233 : List PrefixCut := [⟨4,28606978,28606998⟩,
⟨62,444906666,444906969⟩,
⟨120,863150336,863150924⟩,
⟨128,923371526,923372156⟩]
theorem checked14233 : checkPrefixCuts (2^48) 1869479937 9 Manual.Count131072.C014233.packed 128 cuts14233 = true := by
 decide +kernel
def pointBounds14233 : List (Nat × Nat × Nat) := [(1869484032,95579079127216,95579456695172),(1869543424,95579495426904,95579872995143),(1869602816,95579913670574,95580291239098)]
theorem point_links_checked14233 : (cuts14233.take 3).map (fun c => (1869479937-1+2*2^9*c.k,95579050520238+c.lower,95579428088174+c.upper)) = pointBounds14233 := by
 decide +kernel
def cuts14234 : List PrefixCut := [⟨50,368246713,368246965⟩,
⟨108,790227565,790228102⟩,
⟨128,936856355,936856992⟩]
theorem checked14234 : checkPrefixCuts (2^48) 1869611009 9 Manual.Count131072.C014234.packed 128 cuts14234 = true := by
 decide +kernel
def pointBounds14234 : List (Nat × Nat × Nat) := [(1869662208,95580342138477,95580719707295),(1869721600,95580764119329,95581141688432)]
theorem point_links_checked14234 : (cuts14234.take 2).map (fun c => (1869611009-1+2*2^9*c.k,95579973891764+c.lower,95580351460330+c.upper)) = pointBounds14234 := by
 decide +kernel
def cuts14235 : List PrefixCut := [⟨38,273532096,273532282⟩,
⟨96,690518328,690518805⟩,
⟨128,919027208,919027842⟩]
theorem checked14235 : checkPrefixCuts (2^48) 1869742081 9 Manual.Count131072.C014235.packed 128 cuts14235 = true := by
 decide +kernel
def pointBounds14235 : List (Nat × Nat × Nat) := [(1869780992,95581184280215,95581561849604),(1869840384,95581601266447,95581978836127)]
theorem point_links_checked14235 : (cuts14235.take 2).map (fun c => (1869742081-1+2*2^9*c.k,95580910748119+c.lower,95581288317322+c.upper)) = pointBounds14235 := by
 decide +kernel
def cuts14236 : List PrefixCut := [⟨26,188012558,188012684⟩,
⟨84,612348129,612348545⟩,
⟨128,934466875,934467504⟩]
theorem checked14236 : checkPrefixCuts (2^48) 1869873153 9 Manual.Count131072.C014236.packed 128 cuts14236 = true := by
 decide +kernel
def pointBounds14236 : List (Nat × Nat × Nat) := [(1869899776,95582017787885,95582395357848),(1869959168,95582442123456,95582819693709)]
theorem point_links_checked14236 : (cuts14236.take 2).map (fun c => (1869873153-1+2*2^9*c.k,95581829775327+c.lower,95582207345164+c.upper)) = pointBounds14236 := by
 decide +kernel
def cuts14237 : List PrefixCut := [⟨14,100547643,100547711⟩,
⟨72,519136662,519137019⟩,
⟨128,919801517,919802149⟩]
theorem checked14237 : checkPrefixCuts (2^48) 1870004225 9 Manual.Count131072.C014237.packed 128 cuts14237 = true := by
 decide +kernel
def pointBounds14237 : List (Nat × Nat × Nat) := [(1870018560,95582864789845,95583242360379),(1870077952,95583283378864,95583660949687)]
theorem point_links_checked14237 : (cuts14237.take 2).map (fun c => (1870004225-1+2*2^9*c.k,95582764242202+c.lower,95583141812668+c.upper)) = pointBounds14237 := by
 decide +kernel
def cuts14238 : List PrefixCut := [⟨2,12943890,12943899⟩,
⟨60,438580144,438580449⟩,
⟨118,853818166,853818758⟩,
⟨128,923650303,923650943⟩]
theorem checked14238 : checkPrefixCuts (2^48) 1870135297 9 Manual.Count131072.C014238.packed 128 cuts14238 = true := by
 decide +kernel
def pointBounds14238 : List (Nat × Nat × Nat) := [(1870137344,95583696987609,95584074558716),(1870196736,95584122623863,95584500195266),(1870256128,95584537861885,95584915433575)]
theorem point_links_checked14238 : (cuts14238.take 3).map (fun c => (1870135297-1+2*2^9*c.k,95583684043719+c.lower,95584061614817+c.upper)) = pointBounds14238 := by
 decide +kernel
def cuts14239 : List PrefixCut := [⟨48,341931260,341931489⟩,
⟨106,761958670,761959186⟩,
⟨128,920876369,920876994⟩]
theorem checked14239 : checkPrefixCuts (2^48) 1870266369 9 Manual.Count131072.C014239.packed 128 cuts14239 = true := by
 decide +kernel
def pointBounds14239 : List (Nat × Nat × Nat) := [(1870315520,95584949625282,95585327197249),(1870374912,95585369652692,95585747224946)]
theorem point_links_checked14239 : (cuts14239.take 2).map (fun c => (1870266369-1+2*2^9*c.k,95584607694022+c.lower,95584985265760+c.upper)) = pointBounds14239 := by
 decide +kernel
def cuts14240 : List PrefixCut := [⟨36,258086624,258086801⟩,
⟨94,670262215,670262680⟩,
⟨128,913588704,913589341⟩]
theorem checked14240 : checkPrefixCuts (2^48) 1870397441 9 Manual.Count131072.C014240.packed 128 cuts14240 = true := by
 decide +kernel
def pointBounds14240 : List (Nat × Nat × Nat) := [(1870434304,95585786657015,95586164229555),(1870493696,95586198832606,95586576405434)]
theorem point_links_checked14240 : (cuts14240.take 2).map (fun c => (1870397441-1+2*2^9*c.k,95585528570391+c.lower,95585906142754+c.upper)) = pointBounds14240 := by
 decide +kernel
def cuts14241 : List PrefixCut := [⟨24,171996151,171996269⟩,
⟨82,584747431,584747834⟩,
⟨128,921198641,921199274⟩]
theorem checked14241 : checkPrefixCuts (2^48) 1870528513 9 Manual.Count131072.C014241.packed 128 cuts14241 = true := by
 decide +kernel
def pointBounds14241 : List (Nat × Nat × Nat) := [(1870553088,95586614155246,95586991728364),(1870612480,95587026906526,95587404479929)]
theorem point_links_checked14241 : (cuts14241.take 2).map (fun c => (1870528513-1+2*2^9*c.k,95586442159095+c.lower,95586819732095+c.upper)) = pointBounds14241 := by
 decide +kernel
def cuts14242 : List PrefixCut := [⟨12,88926442,88926502⟩,
⟨70,503908528,503908875⟩,
⟨128,920532548,920533175⟩]
theorem checked14242 : checkPrefixCuts (2^48) 1870659585 9 Manual.Count131072.C014242.packed 128 cuts14242 = true := by
 decide +kernel
def pointBounds14242 : List (Nat × Nat × Nat) := [(1870671872,95587452284178,95587829857871),(1870731264,95587867266264,95588244840244),(1870790656,95588283890284,95588661464544)]
theorem point_links_checked14242 : (cuts14242.take 3).map (fun c => (1870659585-1+2*2^9*c.k,95587363357736+c.lower,95587740931369+c.upper)) = pointBounds14242 := by
 decide +kernel
def cuts14243 : List PrefixCut := [⟨58,427293150,427293449⟩,
⟨116,846147430,846148016⟩,
⟨128,930849453,930850100⟩]
theorem checked14243 : checkPrefixCuts (2^48) 1870790657 9 Manual.Count131072.C014243.packed 128 cuts14243 = true := by
 decide +kernel
def pointBounds14243 : List (Nat × Nat × Nat) := [(1870850048,95588711183434,95589088757993),(1870909440,95589130037714,95589507612560)]
theorem point_links_checked14243 : (cuts14243.take 2).map (fun c => (1870790657-1+2*2^9*c.k,95588283890284+c.lower,95588661464544+c.upper)) = pointBounds14243 := by
 decide +kernel
def cuts14244 : List PrefixCut := [⟨46,334740724,334740954⟩,
⟨104,761391534,761392058⟩,
⟨128,934093920,934094563⟩]
theorem checked14244 : checkPrefixCuts (2^48) 1870921729 9 Manual.Count131072.C014244.packed 128 cuts14244 = true := by
 decide +kernel
def pointBounds14244 : List (Nat × Nat × Nat) := [(1870968832,95589549480461,95589927055598),(1871028224,95589976131271,95590353706702)]
theorem point_links_checked14244 : (cuts14244.take 2).map (fun c => (1870921729-1+2*2^9*c.k,95589214739737+c.lower,95589592314644+c.upper)) = pointBounds14244 := by
 decide +kernel
def cuts14245 : List PrefixCut := [⟨34,249120754,249120921⟩,
⟨92,675894773,675895233⟩,
⟨128,932524214,932524854⟩]
theorem checked14245 : checkPrefixCuts (2^48) 1871052801 9 Manual.Count131072.C014245.packed 128 cuts14245 = true := by
 decide +kernel
def pointBounds14245 : List (Nat × Nat × Nat) := [(1871087616,95590397954411,95590775530128),(1871147008,95590824728430,95591202304440)]
theorem point_links_checked14245 : (cuts14245.take 2).map (fun c => (1871052801-1+2*2^9*c.k,95590148833657+c.lower,95590526409207+c.upper)) = pointBounds14245 := by
 decide +kernel
def cuts14246 : List PrefixCut := [⟨22,161255811,161255920⟩,
⟨80,587100209,587100616⟩,
⟨128,921478395,921479029⟩]
theorem checked14246 : checkPrefixCuts (2^48) 1871183873 9 Manual.Count131072.C014246.packed 128 cuts14246 = true := by
 decide +kernel
def pointBounds14246 : List (Nat × Nat × Nat) := [(1871206400,95591242613682,95591620189981),(1871265792,95591668458080,95592046034677)]
theorem point_links_checked14246 : (cuts14246.take 2).map (fun c => (1871183873-1+2*2^9*c.k,95591081357871+c.lower,95591458934061+c.upper)) = pointBounds14246 := by
 decide +kernel
def cuts14247 : List PrefixCut := [⟨10,70544698,70544746⟩,
⟨68,478312585,478312912⟩,
⟨126,894941594,894942211⟩,
⟨128,908628459,908629085⟩]
theorem checked14247 : checkPrefixCuts (2^48) 1871314945 9 Manual.Count131072.C014247.packed 128 cuts14247 = true := by
 decide +kernel
def pointBounds14247 : List (Nat × Nat × Nat) := [(1871325184,95592073380964,95592450957836),(1871384576,95592481148851,95592858726002),(1871443968,95592897777860,95593275355301)]
theorem point_links_checked14247 : (cuts14247.take 3).map (fun c => (1871314945-1+2*2^9*c.k,95592002836266+c.lower,95592380413090+c.upper)) = pointBounds14247 := by
 decide +kernel
def cuts14248 : List PrefixCut := [⟨56,400672736,400673010⟩,
⟨114,810808131,810808684⟩,
⟨128,913076774,913077398⟩]
theorem checked14248 : checkPrefixCuts (2^48) 1871446017 9 Manual.Count131072.C014248.packed 128 cuts14248 = true := by
 decide +kernel
def pointBounds14248 : List (Nat × Nat × Nat) := [(1871503360,95593312137461,95593689715185),(1871562752,95593722272856,95594099850859)]
theorem point_links_checked14248 : (cuts14248.take 2).map (fun c => (1871446017-1+2*2^9*c.k,95592911464725+c.lower,95593289042175+c.upper)) = pointBounds14248 := by
 decide +kernel
def cuts14249 : List PrefixCut := [⟨44,317027825,317028043⟩,
⟨102,739168304,739168810⟩,
⟨128,928503069,928503705⟩]
theorem checked14249 : checkPrefixCuts (2^48) 1871577089 9 Manual.Count131072.C014249.packed 128 cuts14249 = true := by
 decide +kernel
def pointBounds14249 : List (Nat × Nat × Nat) := [(1871622144,95594141569324,95594519147616),(1871681536,95594563709803,95594941288383)]
theorem point_links_checked14249 : (cuts14249.take 2).map (fun c => (1871577089-1+2*2^9*c.k,95593824541499+c.lower,95594202119573+c.upper)) = pointBounds14249 := by
 decide +kernel
def cuts14250 : List PrefixCut := [⟨32,230536620,230536777⟩,
⟨90,645883317,645883753⟩,
⟨128,923926645,923927273⟩]
theorem checked14250 : checkPrefixCuts (2^48) 1871708161 9 Manual.Count131072.C014250.packed 128 cuts14250 = true := by
 decide +kernel
def pointBounds14250 : List (Nat × Nat × Nat) := [(1871740928,95594983581188,95595361160055),(1871800320,95595398927885,95595776507031)]
theorem point_links_checked14250 : (cuts14250.take 2).map (fun c => (1871708161-1+2*2^9*c.k,95594753044568+c.lower,95595130623278+c.upper)) = pointBounds14250 := by
 decide +kernel
def cuts14251 : List PrefixCut := [⟨20,141650974,141651072⟩,
⟨78,562234058,562234451⟩,
⟨128,918147818,918148455⟩]
theorem checked14251 : checkPrefixCuts (2^48) 1871839233 9 Manual.Count131072.C014251.packed 128 cuts14251 = true := by
 decide +kernel
def pointBounds14251 : List (Nat × Nat × Nat) := [(1871859712,95595818622187,95596196201623),(1871919104,95596239205271,95596616785002)]
theorem point_links_checked14251 : (cuts14251.take 2).map (fun c => (1871839233-1+2*2^9*c.k,95595676971213+c.lower,95596054550551+c.upper)) = pointBounds14251 := by
 decide +kernel
def cuts14252 : List PrefixCut := [⟨8,57288138,57288177⟩,
⟨66,476641795,476642121⟩,
⟨124,892072900,892073511⟩,
⟨128,919437060,919437690⟩]
theorem checked14252 : checkPrefixCuts (2^48) 1871970305 9 Manual.Count131072.C014252.packed 128 cuts14252 = true := by
 decide +kernel
def pointBounds14252 : List (Nat × Nat × Nat) := [(1871978496,95596652407169,95597029987183),(1872037888,95597071760826,95597449341127),(1872097280,95597487191931,95597864772517)]
theorem point_links_checked14252 : (cuts14252.take 3).map (fun c => (1871970305-1+2*2^9*c.k,95596595119031+c.lower,95596972699006+c.upper)) = pointBounds14252 := by
 decide +kernel
def cuts14253 : List PrefixCut := [⟨54,393466316,393466584⟩,
⟨112,808871025,808871574⟩,
⟨128,924183729,924184357⟩]
theorem checked14253 : checkPrefixCuts (2^48) 1872101377 9 Manual.Count131072.C014253.packed 128 cuts14253 = true := by
 decide +kernel
def pointBounds14253 : List (Nat × Nat × Nat) := [(1872156672,95597908022407,95598285603280),(1872216064,95598323427116,95598701008270)]
theorem point_links_checked14253 : (cuts14253.take 2).map (fun c => (1872101377-1+2*2^9*c.k,95597514556091+c.lower,95597892136696+c.upper)) = pointBounds14253 := by
 decide +kernel
def cuts14254 : List PrefixCut := [⟨42,295869391,295869596⟩,
⟨100,713202156,713202647⟩,
⟨128,918556298,918556932⟩]
theorem checked14254 : checkPrefixCuts (2^48) 1872232449 9 Manual.Count131072.C014254.packed 128 cuts14254 = true := by
 decide +kernel
def pointBounds14254 : List (Nat × Nat × Nat) := [(1872275456,95598734609211,95599112190649),(1872334848,95599151941976,95599529523700)]
theorem point_links_checked14254 : (cuts14254.take 2).map (fun c => (1872232449-1+2*2^9*c.k,95598438739820+c.lower,95598816321053+c.upper)) = pointBounds14254 := by
 decide +kernel
def cuts14255 : List PrefixCut := [⟨30,217377285,217377435⟩,
⟨88,634683618,634684056⟩,
⟨128,919544613,919545245⟩]
theorem checked14255 : checkPrefixCuts (2^48) 1872363521 9 Manual.Count131072.C014255.packed 128 cuts14255 = true := by
 decide +kernel
def pointBounds14255 : List (Nat × Nat × Nat) := [(1872394240,95599574673403,95599952255420),(1872453632,95599991979736,95600369562041)]
theorem point_links_checked14255 : (cuts14255.take 2).map (fun c => (1872363521-1+2*2^9*c.k,95599357296118+c.lower,95599734877985+c.upper)) = pointBounds14255 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000132
