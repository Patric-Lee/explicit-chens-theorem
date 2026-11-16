import PlattAssemblyKernel
import PlattCertificates.Count131072.C016208
import PlattCertificates.Count131072.C016209
import PlattCertificates.Count131072.C016210
import PlattCertificates.Count131072.C016211
import PlattCertificates.Count131072.C016212
import PlattCertificates.Count131072.C016213
import PlattCertificates.Count131072.C016214
import PlattCertificates.Count131072.C016215
import PlattCertificates.Count131072.C016216
import PlattCertificates.Count131072.C016217
import PlattCertificates.Count131072.C016218
import PlattCertificates.Count131072.C016219
import PlattCertificates.Count131072.C016220
import PlattCertificates.Count131072.C016221
import PlattCertificates.Count131072.C016222
import PlattCertificates.Count131072.C016223
import PlattCertificates.Count131072.C016224
import PlattCertificates.Count131072.C016225
import PlattCertificates.Count131072.C016226
import PlattCertificates.Count131072.C016227
import PlattCertificates.Count131072.C016228
import PlattCertificates.Count131072.C016229
import PlattCertificates.Count131072.C016230
import PlattCertificates.Count131072.C016231
import PlattCertificates.Count131072.C016232
import PlattCertificates.Count131072.C016233
import PlattCertificates.Count131072.C016234
import PlattCertificates.Count131072.C016235
import PlattCertificates.Count131072.C016236
import PlattCertificates.Count131072.C016237
import PlattCertificates.Count131072.C016238
import PlattCertificates.Count131072.C016239
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000194
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16208 : List PrefixCut := [⟨59,375850552,375850790⟩,
⟨124,792024491,792024987⟩,
⟨128,816753828,816754341⟩]
theorem checked16208 : checkPrefixCuts (2^48) 2128347137 9 Manual.Count131072.C016208.packed 128 cuts16208 = true := by
 decide +kernel
def pointBounds16208 : List (Nat × Nat × Nat) := [(2128407552,97284138341922,97284517038508),(2128474112,97284554515861,97284933212705)]
theorem point_links_checked16208 : (cuts16208.take 2).map (fun c => (2128347137-1+2*2^9*c.k,97283762491370+c.lower,97284141187718+c.upper)) = pointBounds16208 := by
 decide +kernel
def cuts16209 : List PrefixCut := [⟨61,381645773,381646016⟩,
⟨126,787082471,787082980⟩,
⟨128,799776958,799777475⟩]
theorem checked16209 : checkPrefixCuts (2^48) 2128478209 9 Manual.Count131072.C016209.packed 128 cuts16209 = true := by
 decide +kernel
def pointBounds16209 : List (Nat × Nat × Nat) := [(2128540672,97284960890971,97285339588075),(2128607232,97285366327669,97285745025039)]
theorem point_links_checked16209 : (cuts16209.take 2).map (fun c => (2128478209-1+2*2^9*c.k,97284579245198+c.lower,97284957942059+c.upper)) = pointBounds16209 := by
 decide +kernel
def cuts16210 : List PrefixCut := [⟨63,396167549,396167800⟩,
⟨128,801843292,801843798⟩]
theorem checked16210 : checkPrefixCuts (2^48) 2128609281 9 Manual.Count131072.C016210.packed 128 cuts16210 = true := by
 decide +kernel
def pointBounds16210 : List (Nat × Nat × Nat) := [(2128673792,97285775189705,97286153887334),(2128740352,97286180865448,97286559563332)]
theorem point_links_checked16210 : (cuts16210.take 2).map (fun c => (2128609281-1+2*2^9*c.k,97285379022156+c.lower,97285757719534+c.upper)) = pointBounds16210 := by
 decide +kernel
def cuts16211 : List PrefixCut := [⟨65,405795313,405795568⟩,
⟨128,796108403,796108908⟩]
theorem checked16211 : checkPrefixCuts (2^48) 2128740353 9 Manual.Count131072.C016211.packed 128 cuts16211 = true := by
 decide +kernel
def pointBounds16211 : List (Nat × Nat × Nat) := [(2128806912,97286586660761,97286965358900)]
theorem point_links_checked16211 : (cuts16211.take 1).map (fun c => (2128740353-1+2*2^9*c.k,97286180865448+c.lower,97286559563332+c.upper)) = pointBounds16211 := by
 decide +kernel
def cuts16212 : List PrefixCut := [⟨2,11238515,11238523⟩,
⟨67,415950784,415951050⟩,
⟨128,797645907,797646420⟩]
theorem checked16212 : checkPrefixCuts (2^48) 2128871425 9 Manual.Count131072.C016212.packed 128 cuts16212 = true := by
 decide +kernel
def pointBounds16212 : List (Nat × Nat × Nat) := [(2128873472,97286988212366,97287366910763),(2128940032,97287392924635,97287771623290)]
theorem point_links_checked16212 : (cuts16212.take 2).map (fun c => (2128871425-1+2*2^9*c.k,97286976973851+c.lower,97287355672240+c.upper)) = pointBounds16212 := by
 decide +kernel
def cuts16213 : List PrefixCut := [⟨4,23797732,23797747⟩,
⟨69,433376503,433376786⟩,
⟨128,805264842,805265365⟩]
theorem checked16213 : checkPrefixCuts (2^48) 2129002497 9 Manual.Count131072.C016213.packed 128 cuts16213 = true := by
 decide +kernel
def pointBounds16213 : List (Nat × Nat × Nat) := [(2129006592,97287798417490,97288177116407),(2129073152,97288207996261,97288586695446)]
theorem point_links_checked16213 : (cuts16213.take 2).map (fun c => (2129002497-1+2*2^9*c.k,97287774619758+c.lower,97288153318660+c.upper)) = pointBounds16213 := by
 decide +kernel
def cuts16214 : List PrefixCut := [⟨6,38338413,38338436⟩,
⟨71,458467341,458467628⟩,
⟨128,815394657,815395175⟩]
theorem checked16214 : checkPrefixCuts (2^48) 2129133569 9 Manual.Count131072.C016214.packed 128 cuts16214 = true := by
 decide +kernel
def pointBounds16214 : List (Nat × Nat × Nat) := [(2129139712,97288618223013,97288996922461),(2129206272,97289038351941,97289417051653)]
theorem point_links_checked16214 : (cuts16214.take 2).map (fun c => (2129133569-1+2*2^9*c.k,97288579884600+c.lower,97288958584025+c.upper)) = pointBounds16214 := by
 decide +kernel
def cuts16215 : List PrefixCut := [⟨8,49704649,49704682⟩,
⟨73,452886906,452887200⟩,
⟨128,804372423,804372940⟩]
theorem checked16215 : checkPrefixCuts (2^48) 2129264641 9 Manual.Count131072.C016215.packed 128 cuts16215 = true := by
 decide +kernel
def pointBounds16215 : List (Nat × Nat × Nat) := [(2129272832,97289444983906,97289823683882),(2129339392,97289848166163,97290226866400)]
theorem point_links_checked16215 : (cuts16215.take 2).map (fun c => (2129264641-1+2*2^9*c.k,97289395279257+c.lower,97289773979200+c.upper)) = pointBounds16215 := by
 decide +kernel
def cuts16216 : List PrefixCut := [⟨10,64770657,64770699⟩,
⟨75,471364413,471364718⟩,
⟨128,802208145,802208665⟩]
theorem checked16216 : checkPrefixCuts (2^48) 2129395713 9 Manual.Count131072.C016216.packed 128 cuts16216 = true := by
 decide +kernel
def pointBounds16216 : List (Nat × Nat × Nat) := [(2129405952,97290264422337,97290643122839),(2129472512,97290671016093,97291049716858)]
theorem point_links_checked16216 : (cuts16216.take 2).map (fun c => (2129395713-1+2*2^9*c.k,97290199651680+c.lower,97290578352140+c.upper)) = pointBounds16216 := by
 decide +kernel
def cuts16217 : List PrefixCut := [⟨12,77323443,77323491⟩,
⟨77,487460515,487460821⟩,
⟨128,808106658,808107168⟩]
theorem checked16217 : checkPrefixCuts (2^48) 2129526785 9 Manual.Count131072.C016217.packed 128 cuts16217 = true := by
 decide +kernel
def pointBounds16217 : List (Nat × Nat × Nat) := [(2129539072,97291079183268,97291457884296),(2129605632,97291489320340,97291868021626)]
theorem point_links_checked16217 : (cuts16217.take 2).map (fun c => (2129526785-1+2*2^9*c.k,97291001859825+c.lower,97291380560805+c.upper)) = pointBounds16217 := by
 decide +kernel
def cuts16218 : List PrefixCut := [⟨14,90271166,90271222⟩,
⟨79,496946335,496946655⟩,
⟨128,803563280,803563799⟩]
theorem checked16218 : checkPrefixCuts (2^48) 2129657857 9 Manual.Count131072.C016218.packed 128 cuts16218 = true := by
 decide +kernel
def pointBounds16218 : List (Nat × Nat × Nat) := [(2129672192,97291900237649,97292278939195),(2129738752,97292306912818,97292685614628)]
theorem point_links_checked16218 : (cuts16218.take 2).map (fun c => (2129657857-1+2*2^9*c.k,97291809966483+c.lower,97292188667973+c.upper)) = pointBounds16218 := by
 decide +kernel
def cuts16219 : List PrefixCut := [⟨16,97798712,97798777⟩,
⟨81,509206139,509206466⟩,
⟨128,805628205,805628719⟩]
theorem checked16219 : checkPrefixCuts (2^48) 2129788929 9 Manual.Count131072.C016219.packed 128 cuts16219 = true := by
 decide +kernel
def pointBounds16219 : List (Nat × Nat × Nat) := [(2129805312,97292711328475,97293090030549),(2129871872,97293122735902,97293501438238)]
theorem point_links_checked16219 : (cuts16219.take 2).map (fun c => (2129788929-1+2*2^9*c.k,97292613529763+c.lower,97292992231772+c.upper)) = pointBounds16219 := by
 decide +kernel
def cuts16220 : List PrefixCut := [⟨18,118936997,118937073⟩,
⟨83,521596857,521597195⟩,
⟨128,798575078,798575591⟩]
theorem checked16220 : checkPrefixCuts (2^48) 2129920001 9 Manual.Count131072.C016220.packed 128 cuts16220 = true := by
 decide +kernel
def pointBounds16220 : List (Nat × Nat × Nat) := [(2129938432,97293538094965,97293916797564),(2130004992,97293940754825,97294319457686)]
theorem point_links_checked16220 : (cuts16220.take 2).map (fun c => (2129920001-1+2*2^9*c.k,97293419157968+c.lower,97293797860491+c.upper)) = pointBounds16220 := by
 decide +kernel
def cuts16221 : List PrefixCut := [⟨21,137033316,137033402⟩,
⟨87,552485286,552485637⟩,
⟨128,802357938,802358451⟩]
theorem checked16221 : checkPrefixCuts (2^48) 2130051073 9 Manual.Count131072.C016221.packed 128 cuts16221 = true := by
 decide +kernel
def pointBounds16221 : List (Nat × Nat × Nat) := [(2130072576,97294354766362,97294733469484),(2130140160,97294770218332,97295148921719)]
theorem point_links_checked16221 : (cuts16221.take 2).map (fun c => (2130051073-1+2*2^9*c.k,97294217733046+c.lower,97294596436082+c.upper)) = pointBounds16221 := by
 decide +kernel
def cuts16222 : List PrefixCut := [⟨25,160148529,160148628⟩,
⟨91,568439000,568439363⟩,
⟨128,805215247,805215759⟩]
theorem checked16222 : checkPrefixCuts (2^48) 2130182145 9 Manual.Count131072.C016222.packed 128 cuts16222 = true := by
 decide +kernel
def pointBounds16222 : List (Nat × Nat × Nat) := [(2130207744,97295180239513,97295558943161),(2130275328,97295588529984,97295967233896)]
theorem point_links_checked16222 : (cuts16222.take 2).map (fun c => (2130182145-1+2*2^9*c.k,97295020090984+c.lower,97295398794533+c.upper)) = pointBounds16222 := by
 decide +kernel
def cuts16223 : List PrefixCut := [⟨29,185506993,185507110⟩,
⟨95,604209442,604209828⟩,
⟨128,816792617,816793138⟩]
theorem checked16223 : checkPrefixCuts (2^48) 2130313217 9 Manual.Count131072.C016223.packed 128 cuts16223 = true := by
 decide +kernel
def pointBounds16223 : List (Nat × Nat × Nat) := [(2130342912,97296010813224,97296389517402),(2130410496,97296429515673,97296808220120)]
theorem point_links_checked16223 : (cuts16223.take 2).map (fun c => (2130313217-1+2*2^9*c.k,97295825306231+c.lower,97296204010292+c.upper)) = pointBounds16223 := by
 decide +kernel
def cuts16224 : List PrefixCut := [⟨33,210465925,210466058⟩,
⟨99,627292190,627292583⟩,
⟨128,804191589,804192095⟩]
theorem checked16224 : checkPrefixCuts (2^48) 2130444289 9 Manual.Count131072.C016224.packed 128 cuts16224 = true := by
 decide +kernel
def pointBounds16224 : List (Nat × Nat × Nat) := [(2130478080,97296852564773,97297231269488),(2130545664,97297269391038,97297648096013)]
theorem point_links_checked16224 : (cuts16224.take 2).map (fun c => (2130444289-1+2*2^9*c.k,97296642098848+c.lower,97297020803430+c.upper)) = pointBounds16224 := by
 decide +kernel
def cuts16225 : List PrefixCut := [⟨37,229873095,229873241⟩,
⟨103,655259903,655260317⟩,
⟨128,816559892,816560408⟩]
theorem checked16225 : checkPrefixCuts (2^48) 2130575361 9 Manual.Count131072.C016225.packed 128 cuts16225 = true := by
 decide +kernel
def pointBounds16225 : List (Nat × Nat × Nat) := [(2130613248,97297676163532,97298054868766),(2130680832,97298101550340,97298480255842)]
theorem point_links_checked16225 : (cuts16225.take 2).map (fun c => (2130575361-1+2*2^9*c.k,97297446290437+c.lower,97297824995525+c.upper)) = pointBounds16225 := by
 decide +kernel
def cuts16226 : List PrefixCut := [⟨41,261959693,261959860⟩,
⟨107,671335429,671335868⟩,
⟨128,804885053,804885577⟩]
theorem checked16226 : checkPrefixCuts (2^48) 2130706433 9 Manual.Count131072.C016226.packed 128 cuts16226 = true := by
 decide +kernel
def pointBounds16226 : List (Nat × Nat × Nat) := [(2130748416,97298524810022,97298903515793),(2130816000,97298934185758,97299312891801)]
theorem point_links_checked16226 : (cuts16226.take 2).map (fun c => (2130706433-1+2*2^9*c.k,97298262850329+c.lower,97298641555933+c.upper)) = pointBounds16226 := by
 decide +kernel
def cuts16227 : List PrefixCut := [⟨45,278323034,278323217⟩,
⟨111,699428957,699429407⟩,
⟨128,801004864,801005380⟩]
theorem checked16227 : checkPrefixCuts (2^48) 2130837505 9 Manual.Count131072.C016227.packed 128 cuts16227 = true := by
 decide +kernel
def pointBounds16227 : List (Nat × Nat × Nat) := [(2130883584,97299346058416,97299724764727),(2130951168,97299767164339,97300145870917)]
theorem point_links_checked16227 : (cuts16227.take 2).map (fun c => (2130837505-1+2*2^9*c.k,97299067735382+c.lower,97299446441510+c.upper)) = pointBounds16227 := by
 decide +kernel
def cuts16228 : List PrefixCut := [⟨49,304326645,304326836⟩,
⟨115,709820223,709820678⟩,
⟨128,788672024,788672528⟩]
theorem checked16228 : checkPrefixCuts (2^48) 2130968577 9 Manual.Count131072.C016228.packed 128 cuts16228 = true := by
 decide +kernel
def pointBounds16228 : List (Nat × Nat × Nat) := [(2131018752,97300173066891,97300551773726),(2131086336,97300578560469,97300957267568)]
theorem point_links_checked16228 : (cuts16228.take 2).map (fun c => (2130968577-1+2*2^9*c.k,97299868740246+c.lower,97300247446890+c.upper)) = pointBounds16228 := by
 decide +kernel
def cuts16229 : List PrefixCut := [⟨53,335213870,335214082⟩,
⟨119,752832507,752832985⟩,
⟨128,806321591,806322103⟩]
theorem checked16229 : checkPrefixCuts (2^48) 2131099649 9 Manual.Count131072.C016229.packed 128 cuts16229 = true := by
 decide +kernel
def pointBounds16229 : List (Nat × Nat × Nat) := [(2131153920,97300992626140,97301371333500),(2131221504,97301410244777,97301788952403)]
theorem point_links_checked16229 : (cuts16229.take 2).map (fun c => (2131099649-1+2*2^9*c.k,97300657412270+c.lower,97301036119418+c.upper)) = pointBounds16229 := by
 decide +kernel
def cuts16230 : List PrefixCut := [⟨57,351305437,351305659⟩,
⟨123,774444283,774444770⟩,
⟨128,804950966,804951472⟩]
theorem checked16230 : checkPrefixCuts (2^48) 2131230721 9 Manual.Count131072.C016230.packed 128 cuts16230 = true := by
 decide +kernel
def pointBounds16230 : List (Nat × Nat × Nat) := [(2131289088,97301815039298,97302193747180),(2131356672,97302238178144,97302616886291)]
theorem point_links_checked16230 : (cuts16230.take 2).map (fun c => (2131230721-1+2*2^9*c.k,97301463733861+c.lower,97301842441521+c.upper)) = pointBounds16230 := by
 decide +kernel
def cuts16231 : List PrefixCut := [⟨61,379148424,379148666⟩,
⟨127,794072842,794073350⟩,
⟨128,800147386,800147898⟩]
theorem checked16231 : checkPrefixCuts (2^48) 2131361793 9 Manual.Count131072.C016231.packed 128 cuts16231 = true := by
 decide +kernel
def pointBounds16231 : List (Nat × Nat × Nat) := [(2131424256,97302647833251,97303026541659),(2131491840,97303062757669,97303441466343)]
theorem point_links_checked16231 : (cuts16231.take 2).map (fun c => (2131361793-1+2*2^9*c.k,97302268684827+c.lower,97302647392993+c.upper)) = pointBounds16231 := by
 decide +kernel
def cuts16232 : List PrefixCut := [⟨65,413326617,413326886⟩,
⟨128,805248530,805249046⟩]
theorem checked16232 : checkPrefixCuts (2^48) 2131492865 9 Manual.Count131072.C016232.packed 128 cuts16232 = true := by
 decide +kernel
def pointBounds16232 : List (Nat × Nat × Nat) := [(2131559424,97303482158830,97303860867777)]
theorem point_links_checked16232 : (cuts16232.take 1).map (fun c => (2131492865-1+2*2^9*c.k,97303068832213+c.lower,97303447540891+c.upper)) = pointBounds16232 := by
 decide +kernel
def cuts16233 : List PrefixCut := [⟨3,17562259,17562271⟩,
⟨69,430334543,430334814⟩,
⟨128,795031501,795032006⟩]
theorem checked16233 : checkPrefixCuts (2^48) 2131623937 9 Manual.Count131072.C016233.packed 128 cuts16233 = true := by
 decide +kernel
def pointBounds16233 : List (Nat × Nat × Nat) := [(2131627008,97303891643002,97304270352208),(2131694592,97304304415286,97304683124751)]
theorem point_links_checked16233 : (cuts16233.take 2).map (fun c => (2131623937-1+2*2^9*c.k,97303874080743+c.lower,97304252789937+c.upper)) = pointBounds16233 := by
 decide +kernel
def cuts16234 : List PrefixCut := [⟨7,48062129,48062161⟩,
⟨73,461204289,461204579⟩,
⟨128,803300916,803301427⟩]
theorem checked16234 : checkPrefixCuts (2^48) 2131755009 9 Manual.Count131072.C016234.packed 128 cuts16234 = true := by
 decide +kernel
def pointBounds16234 : List (Nat × Nat × Nat) := [(2131762176,97304717174373,97305095884104),(2131829760,97305130316533,97305509026522)]
theorem point_links_checked16234 : (cuts16234.take 2).map (fun c => (2131755009-1+2*2^9*c.k,97304669112244+c.lower,97305047821943+c.upper)) = pointBounds16234 := by
 decide +kernel
def cuts16235 : List PrefixCut := [⟨11,71296507,71296551⟩,
⟨77,481903920,481904225⟩,
⟨128,799686661,799687166⟩]
theorem checked16235 : checkPrefixCuts (2^48) 2131886081 9 Manual.Count131072.C016235.packed 128 cuts16235 = true := by
 decide +kernel
def pointBounds16235 : List (Nat × Nat × Nat) := [(2131897344,97305543709667,97305922419921),(2131964928,97305954317080,97306333027595)]
theorem point_links_checked16235 : (cuts16235.take 2).map (fun c => (2131886081-1+2*2^9*c.k,97305472413160+c.lower,97305851123370+c.upper)) = pointBounds16235 := by
 decide +kernel
def cuts16236 : List PrefixCut := [⟨15,98356633,98356696⟩,
⟨81,515538994,515539323⟩,
⟨128,814159556,814160076⟩]
theorem checked16236 : checkPrefixCuts (2^48) 2132017153 9 Manual.Count131072.C016236.packed 128 cuts16236 = true := by
 decide +kernel
def pointBounds16236 : List (Nat × Nat × Nat) := [(2132032512,97306370456454,97306749167232),(2132100096,97306787638815,97307166349859)]
theorem point_links_checked16236 : (cuts16236.take 2).map (fun c => (2132017153-1+2*2^9*c.k,97306272099821+c.lower,97306650810536+c.upper)) = pointBounds16236 := by
 decide +kernel
def cuts16237 : List PrefixCut := [⟨19,119208729,119208808⟩,
⟨85,536232721,536233063⟩,
⟨128,805792899,805793416⟩]
theorem checked16237 : checkPrefixCuts (2^48) 2132148225 9 Manual.Count131072.C016237.packed 128 cuts16237 = true := by
 decide +kernel
def pointBounds16237 : List (Nat × Nat × Nat) := [(2132167680,97307205468106,97307584179420),(2132235264,97307622492098,97308001203675)]
theorem point_links_checked16237 : (cuts16237.take 2).map (fun c => (2132148225-1+2*2^9*c.k,97307086259377+c.lower,97307464970612+c.upper)) = pointBounds16237 := by
 decide +kernel
def cuts16238 : List PrefixCut := [⟨23,145866464,145866554⟩,
⟨89,559827875,559828230⟩,
⟨128,805743271,805743780⟩]
theorem checked16238 : checkPrefixCuts (2^48) 2132279297 9 Manual.Count131072.C016238.packed 128 cuts16238 = true := by
 decide +kernel
def pointBounds16238 : List (Nat × Nat × Nat) := [(2132302848,97308037918740,97308416630582),(2132370432,97308451880151,97308830592258)]
theorem point_links_checked16238 : (cuts16238.take 2).map (fun c => (2132279297-1+2*2^9*c.k,97307892052276+c.lower,97308270764028+c.upper)) = pointBounds16238 := by
 decide +kernel
def cuts16239 : List PrefixCut := [⟨27,166448974,166449082⟩,
⟨93,577348309,577348677⟩,
⟨128,799093992,799094497⟩]
theorem checked16239 : checkPrefixCuts (2^48) 2132410369 9 Manual.Count131072.C016239.packed 128 cuts16239 = true := by
 decide +kernel
def pointBounds16239 : List (Nat × Nat × Nat) := [(2132438016,97308864244521,97309242956890),(2132505600,97309275143856,97309653856485)]
theorem point_links_checked16239 : (cuts16239.take 2).map (fun c => (2132410369-1+2*2^9*c.k,97308697795547+c.lower,97309076507808+c.upper)) = pointBounds16239 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000194
