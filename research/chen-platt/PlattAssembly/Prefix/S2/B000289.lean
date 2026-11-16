import PlattAssemblyKernel
import PlattCertificates.Count131072.C019248
import PlattCertificates.Count131072.C019249
import PlattCertificates.Count131072.C019250
import PlattCertificates.Count131072.C019251
import PlattCertificates.Count131072.C019252
import PlattCertificates.Count131072.C019253
import PlattCertificates.Count131072.C019254
import PlattCertificates.Count131072.C019255
import PlattCertificates.Count131072.C019256
import PlattCertificates.Count131072.C019257
import PlattCertificates.Count131072.C019258
import PlattCertificates.Count131072.C019259
import PlattCertificates.Count131072.C019260
import PlattCertificates.Count131072.C019261
import PlattCertificates.Count131072.C019262
import PlattCertificates.Count131072.C019263
import PlattCertificates.Count131072.C019264
import PlattCertificates.Count131072.C019265
import PlattCertificates.Count131072.C019266
import PlattCertificates.Count131072.C019267
import PlattCertificates.Count131072.C019268
import PlattCertificates.Count131072.C019269
import PlattCertificates.Count131072.C019270
import PlattCertificates.Count131072.C019271
import PlattCertificates.Count131072.C019272
import PlattCertificates.Count131072.C019273
import PlattCertificates.Count131072.C019274
import PlattCertificates.Count131072.C019275
import PlattCertificates.Count131072.C019276
import PlattCertificates.Count131072.C019277
import PlattCertificates.Count131072.C019278
import PlattCertificates.Count131072.C019279
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000289
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19248 : List PrefixCut := [⟨74,399569845,399570077⟩,
⟨128,685510434,685510840⟩]
theorem checked19248 : checkPrefixCuts (2^48) 2526806017 9 Manual.Count131072.C019248.packed 128 cuts19248 = true := by
 decide +kernel
def pointBounds19248 : List (Nat × Nat × Nat) := [(2526881792,99524076568983,99524456644818)]
theorem point_links_checked19248 : (cuts19248.take 1).map (fun c => (2526806017-1+2*2^9*c.k,99523676999138+c.lower,99524057074741+c.upper)) = pointBounds19248 := by
 decide +kernel
def cuts19249 : List PrefixCut := [⟨24,123642035,123642111⟩,
⟨102,533434478,533434794⟩,
⟨128,669546418,669546818⟩]
theorem checked19249 : checkPrefixCuts (2^48) 2526937089 9 Manual.Count131072.C019249.packed 128 cuts19249 = true := by
 decide +kernel
def pointBounds19249 : List (Nat × Nat × Nat) := [(2526961664,99524486151607,99524866227692),(2527041536,99524895944050,99525276020375)]
theorem point_links_checked19249 : (cuts19249.take 2).map (fun c => (2526937089-1+2*2^9*c.k,99524362509572+c.lower,99524742585581+c.upper)) = pointBounds19249 := by
 decide +kernel
def cuts19250 : List PrefixCut := [⟨52,270660207,270660365⟩,
⟨128,671182346,671182743⟩]
theorem checked19250 : checkPrefixCuts (2^48) 2527068161 9 Manual.Count131072.C019250.packed 128 cuts19250 = true := by
 decide +kernel
def pointBounds19250 : List (Nat × Nat × Nat) := [(2527121408,99525302716197,99525682792764)]
theorem point_links_checked19250 : (cuts19250.take 1).map (fun c => (2527068161-1+2*2^9*c.k,99525032055990+c.lower,99525412132399+c.upper)) = pointBounds19250 := by
 decide +kernel
def cuts19251 : List PrefixCut := [⟨2,9578521,9578526⟩,
⟨80,418663877,418664124⟩,
⟨128,669922492,669922893⟩]
theorem checked19251 : checkPrefixCuts (2^48) 2527199233 9 Manual.Count131072.C019251.packed 128 cuts19251 = true := by
 decide +kernel
def pointBounds19251 : List (Nat × Nat × Nat) := [(2527201280,99525712816857,99526092893668),(2527281152,99526121902213,99526501979266)]
theorem point_links_checked19251 : (cuts19251.take 2).map (fun c => (2527199233-1+2*2^9*c.k,99525703238336+c.lower,99526083315142+c.upper)) = pointBounds19251 := by
 decide +kernel
def cuts19252 : List PrefixCut := [⟨30,156143181,156143274⟩,
⟨108,565870842,565871173⟩,
⟨128,673674189,673674584⟩]
theorem checked19252 : checkPrefixCuts (2^48) 2527330305 9 Manual.Count131072.C019252.packed 128 cuts19252 = true := by
 decide +kernel
def pointBounds19252 : List (Nat × Nat × Nat) := [(2527361024,99526529304009,99526909381309),(2527440896,99526939031670,99527319109208)]
theorem point_links_checked19252 : (cuts19252.take 2).map (fun c => (2527330305-1+2*2^9*c.k,99526373160828+c.lower,99526753238035+c.upper)) = pointBounds19252 := by
 decide +kernel
def cuts19253 : List PrefixCut := [⟨58,302802334,302802514⟩,
⟨128,676757458,676757864⟩]
theorem checked19253 : checkPrefixCuts (2^48) 2527461377 9 Manual.Count131072.C019253.packed 128 cuts19253 = true := by
 decide +kernel
def pointBounds19253 : List (Nat × Nat × Nat) := [(2527520768,99527349637351,99527729715133)]
theorem point_links_checked19253 : (cuts19253.take 1).map (fun c => (2527461377-1+2*2^9*c.k,99527046835017+c.lower,99527426912619+c.upper)) = pointBounds19253 := by
 decide +kernel
def cuts19254 : List PrefixCut := [⟨8,41092095,41092120⟩,
⟨86,460803225,460803501⟩,
⟨128,682290373,682290777⟩]
theorem checked19254 : checkPrefixCuts (2^48) 2527592449 9 Manual.Count131072.C019254.packed 128 cuts19254 = true := by
 decide +kernel
def pointBounds19254 : List (Nat × Nat × Nat) := [(2527600640,99527764684570,99528144762603),(2527680512,99528184395700,99528564473984)]
theorem point_links_checked19254 : (cuts19254.take 2).map (fun c => (2527592449-1+2*2^9*c.k,99527723592475+c.lower,99528103670483+c.upper)) = pointBounds19254 := by
 decide +kernel
def cuts19255 : List PrefixCut := [⟨36,193311057,193311168⟩,
⟨114,602305837,602306194⟩,
⟨128,679471135,679471537⟩]
theorem checked19255 : checkPrefixCuts (2^48) 2527723521 9 Manual.Count131072.C019255.packed 128 cuts19255 = true := by
 decide +kernel
def pointBounds19255 : List (Nat × Nat × Nat) := [(2527760384,99528599193905,99528979272428),(2527840256,99529008188685,99529388267454)]
theorem point_links_checked19255 : (cuts19255.take 2).map (fun c => (2527723521-1+2*2^9*c.k,99528405882848+c.lower,99528785961260+c.upper)) = pointBounds19255 := by
 decide +kernel
def cuts19256 : List PrefixCut := [⟨64,329812435,329812633⟩,
⟨128,675650020,675650421⟩]
theorem checked19256 : checkPrefixCuts (2^48) 2527854593 9 Manual.Count131072.C019256.packed 128 cuts19256 = true := by
 decide +kernel
def pointBounds19256 : List (Nat × Nat × Nat) := [(2527920128,99529415166418,99529795245430)]
theorem point_links_checked19256 : (cuts19256.take 1).map (fun c => (2527854593-1+2*2^9*c.k,99529085353983+c.lower,99529465432797+c.upper)) = pointBounds19256 := by
 decide +kernel
def cuts19257 : List PrefixCut := [⟨14,73931904,73931950⟩,
⟨92,485226084,485226377⟩,
⟨128,667264678,667265082⟩]
theorem checked19257 : checkPrefixCuts (2^48) 2527985665 9 Manual.Count131072.C019257.packed 128 cuts19257 = true := by
 decide +kernel
def pointBounds19257 : List (Nat × Nat × Nat) := [(2528000000,99529834935907,99530215015168),(2528079872,99530246230087,99530626309595)]
theorem point_links_checked19257 : (cuts19257.take 2).map (fun c => (2527985665-1+2*2^9*c.k,99529761004003+c.lower,99530141083218+c.upper)) = pointBounds19257 := by
 decide +kernel
def cuts19258 : List PrefixCut := [⟨42,222451016,222451148⟩,
⟨120,638283984,638284367⟩,
⟨128,681369537,681369946⟩]
theorem checked19258 : checkPrefixCuts (2^48) 2528116737 9 Manual.Count131072.C019258.packed 128 cuts19258 = true := by
 decide +kernel
def pointBounds19258 : List (Nat × Nat × Nat) := [(2528159744,99530650719697,99531030799448),(2528239616,99531066552665,99531446632667)]
theorem point_links_checked19258 : (cuts19258.take 2).map (fun c => (2528116737-1+2*2^9*c.k,99530428268681+c.lower,99530808348300+c.upper)) = pointBounds19258 := by
 decide +kernel
def cuts19259 : List PrefixCut := [⟨70,370953002,370953223⟩,
⟨128,677103761,677104158⟩]
theorem checked19259 : checkPrefixCuts (2^48) 2528247809 9 Manual.Count131072.C019259.packed 128 cuts19259 = true := by
 decide +kernel
def pointBounds19259 : List (Nat × Nat × Nat) := [(2528319488,99531480591220,99531860671469)]
theorem point_links_checked19259 : (cuts19259.take 1).map (fun c => (2528247809-1+2*2^9*c.k,99531109638218+c.lower,99531489718246+c.upper)) = pointBounds19259 := by
 decide +kernel
def cuts19260 : List PrefixCut := [⟨20,108876620,108876684⟩,
⟨98,522109731,522110041⟩,
⟨128,679406483,679406886⟩]
theorem checked19260 : checkPrefixCuts (2^48) 2528378881 9 Manual.Count131072.C019260.packed 128 cuts19260 = true := by
 decide +kernel
def pointBounds19260 : List (Nat × Nat × Nat) := [(2528399360,99531895618599,99532275699088),(2528479232,99532308851710,99532688932445)]
theorem point_links_checked19260 : (cuts19260.take 2).map (fun c => (2528378881-1+2*2^9*c.k,99531786741979+c.lower,99532166822404+c.upper)) = pointBounds19260 := by
 decide +kernel
def cuts19261 : List PrefixCut := [⟨48,248353514,248353664⟩,
⟨126,658220964,658221355⟩,
⟨128,667905346,667905743⟩]
theorem checked19261 : checkPrefixCuts (2^48) 2528509953 9 Manual.Count131072.C019261.packed 128 cuts19261 = true := by
 decide +kernel
def pointBounds19261 : List (Nat × Nat × Nat) := [(2528559104,99532714501976,99533094582954),(2528638976,99533124369426,99533504450645)]
theorem point_links_checked19261 : (cuts19261.take 2).map (fun c => (2528509953-1+2*2^9*c.k,99532466148462+c.lower,99532846229290+c.upper)) = pointBounds19261 := by
 decide +kernel
def cuts19262 : List PrefixCut := [⟨76,399613558,399613793⟩,
⟨128,673325084,673325480⟩]
theorem checked19262 : checkPrefixCuts (2^48) 2528641025 9 Manual.Count131072.C019262.packed 128 cuts19262 = true := by
 decide +kernel
def pointBounds19262 : List (Nat × Nat × Nat) := [(2528718848,99533533667366,99533913748826)]
theorem point_links_checked19262 : (cuts19262.take 1).map (fun c => (2528641025-1+2*2^9*c.k,99533134053808+c.lower,99533514135033+c.upper)) = pointBounds19262 := by
 decide +kernel
def cuts19263 : List PrefixCut := [⟨26,137243175,137243259⟩,
⟨104,542842247,542842573⟩,
⟨128,670284980,670285382⟩]
theorem checked19263 : checkPrefixCuts (2^48) 2528772097 9 Manual.Count131072.C019263.packed 128 cuts19263 = true := by
 decide +kernel
def pointBounds19263 : List (Nat × Nat × Nat) := [(2528798720,99533944622067,99534324703772),(2528878592,99534350221139,99534730303086)]
theorem point_links_checked19263 : (cuts19263.take 2).map (fun c => (2528772097-1+2*2^9*c.k,99533807378892+c.lower,99534187460513+c.upper)) = pointBounds19263 := by
 decide +kernel
def cuts19264 : List PrefixCut := [⟨54,282484351,282484516⟩,
⟨128,680267153,680267552⟩]
theorem checked19264 : checkPrefixCuts (2^48) 2528903169 9 Manual.Count131072.C019264.packed 128 cuts19264 = true := by
 decide +kernel
def pointBounds19264 : List (Nat × Nat × Nat) := [(2528958464,99534760148223,99535140230411)]
theorem point_links_checked19264 : (cuts19264.take 1).map (fun c => (2528903169-1+2*2^9*c.k,99534477663872+c.lower,99534857745895+c.upper)) = pointBounds19264 := by
 decide +kernel
def cuts19265 : List PrefixCut := [⟨4,20923891,20923903⟩,
⟨82,426039306,426039555⟩,
⟨128,670994452,670994846⟩]
theorem checked19265 : checkPrefixCuts (2^48) 2529034241 9 Manual.Count131072.C019265.packed 128 cuts19265 = true := by
 decide +kernel
def pointBounds19265 : List (Nat × Nat × Nat) := [(2529038336,99535178854916,99535558937350),(2529118208,99535583970331,99535964053002)]
theorem point_links_checked19265 : (cuts19265.take 2).map (fun c => (2529034241-1+2*2^9*c.k,99535157931025+c.lower,99535538013447+c.upper)) = pointBounds19265 := by
 decide +kernel
def cuts19266 : List PrefixCut := [⟨32,169718627,169718727⟩,
⟨110,577701935,577702278⟩,
⟨128,674966130,674966527⟩]
theorem checked19266 : checkPrefixCuts (2^48) 2529165313 9 Manual.Count131072.C019266.packed 128 cuts19266 = true := by
 decide +kernel
def pointBounds19266 : List (Nat × Nat × Nat) := [(2529198080,99535998644104,99536378727020),(2529277952,99536406627412,99536786710571)]
theorem point_links_checked19266 : (cuts19266.take 2).map (fun c => (2529165313-1+2*2^9*c.k,99535828925477+c.lower,99536209008293+c.upper)) = pointBounds19266 := by
 decide +kernel
def cuts19267 : List PrefixCut := [⟨60,318384883,318385070⟩,
⟨128,675265009,675265410⟩]
theorem checked19267 : checkPrefixCuts (2^48) 2529296385 9 Manual.Count131072.C019267.packed 128 cuts19267 = true := by
 decide +kernel
def pointBounds19267 : List (Nat × Nat × Nat) := [(2529357824,99536822276490,99537202359890)]
theorem point_links_checked19267 : (cuts19267.take 1).map (fun c => (2529296385-1+2*2^9*c.k,99536503891607+c.lower,99536883974820+c.upper)) = pointBounds19267 := by
 decide +kernel
def cuts19268 : List PrefixCut := [⟨10,49296976,49297005⟩,
⟨88,462694305,462694589⟩,
⟨128,666216704,666217112⟩]
theorem checked19268 : checkPrefixCuts (2^48) 2529427457 9 Manual.Count131072.C019268.packed 128 cuts19268 = true := by
 decide +kernel
def pointBounds19268 : List (Nat × Nat × Nat) := [(2529437696,99537228453592,99537608537235),(2529517568,99537641850921,99538021934819)]
theorem point_links_checked19268 : (cuts19268.take 2).map (fun c => (2529427457-1+2*2^9*c.k,99537179156616+c.lower,99537559240230+c.upper)) = pointBounds19268 := by
 decide +kernel
def cuts19269 : List PrefixCut := [⟨38,204965694,204965814⟩,
⟨116,612662052,612662413⟩,
⟨128,677643043,677643443⟩]
theorem checked19269 : checkPrefixCuts (2^48) 2529558529 9 Manual.Count131072.C019269.packed 128 cuts19269 = true := by
 decide +kernel
def pointBounds19269 : List (Nat × Nat × Nat) := [(2529597440,99538050339014,99538430423156),(2529677312,99538458035372,99538838119755)]
theorem point_links_checked19269 : (cuts19269.take 2).map (fun c => (2529558529-1+2*2^9*c.k,99537845373320+c.lower,99538225457342+c.upper)) = pointBounds19269 := by
 decide +kernel
def cuts19270 : List PrefixCut := [⟨66,350268749,350268957⟩,
⟨128,673936273,673936680⟩]
theorem checked19270 : checkPrefixCuts (2^48) 2529689601 9 Manual.Count131072.C019270.packed 128 cuts19270 = true := by
 decide +kernel
def pointBounds19270 : List (Nat × Nat × Nat) := [(2529757184,99538873285112,99539253369742)]
theorem point_links_checked19270 : (cuts19270.take 1).map (fun c => (2529689601-1+2*2^9*c.k,99538523016363+c.lower,99538903100785+c.upper)) = pointBounds19270 := by
 decide +kernel
def cuts19271 : List PrefixCut := [⟨16,88008578,88008628⟩,
⟨94,500895562,500895855⟩,
⟨128,679353031,679353432⟩]
theorem checked19271 : checkPrefixCuts (2^48) 2529820673 9 Manual.Count131072.C019271.packed 128 cuts19271 = true := by
 decide +kernel
def pointBounds19271 : List (Nat × Nat × Nat) := [(2529837056,99539284961214,99539665046093),(2529916928,99539697848198,99540077933320)]
theorem point_links_checked19271 : (cuts19271.take 2).map (fun c => (2529820673-1+2*2^9*c.k,99539196952636+c.lower,99539577037465+c.upper)) = pointBounds19271 := by
 decide +kernel
def cuts19272 : List PrefixCut := [⟨44,232747616,232747760⟩,
⟨122,639600882,639601270⟩,
⟨128,670862524,670862930⟩]
theorem checked19272 : checkPrefixCuts (2^48) 2529951745 9 Manual.Count131072.C019272.packed 128 cuts19272 = true := by
 decide +kernel
def pointBounds19272 : List (Nat × Nat × Nat) := [(2529996800,99540109053283,99540489138657),(2530076672,99540515906549,99540895992167)]
theorem point_links_checked19272 : (cuts19272.take 2).map (fun c => (2529951745-1+2*2^9*c.k,99539876305667+c.lower,99540256390897+c.upper)) = pointBounds19272 := by
 decide +kernel
def cuts19273 : List PrefixCut := [⟨72,379472504,379472735⟩,
⟨128,676835054,676835464⟩]
theorem checked19273 : checkPrefixCuts (2^48) 2530082817 9 Manual.Count131072.C019273.packed 128 cuts19273 = true := by
 decide +kernel
def pointBounds19273 : List (Nat × Nat × Nat) := [(2530156544,99540926640695,99541306726562)]
theorem point_links_checked19273 : (cuts19273.take 1).map (fun c => (2530082817-1+2*2^9*c.k,99540547168191+c.lower,99540927253827+c.upper)) = pointBounds19273 := by
 decide +kernel
def cuts19274 : List PrefixCut := [⟨22,119588369,119588439⟩,
⟨100,532410185,532410498⟩,
⟨128,677467607,677468007⟩]
theorem checked19274 : checkPrefixCuts (2^48) 2530213889 9 Manual.Count131072.C019274.packed 128 cuts19274 = true := by
 decide +kernel
def pointBounds19274 : List (Nat × Nat × Nat) := [(2530236416,99541343591614,99541723677730),(2530316288,99541756413430,99542136499789)]
theorem point_links_checked19274 : (cuts19274.take 2).map (fun c => (2530213889-1+2*2^9*c.k,99541224003245+c.lower,99541604089291+c.upper)) = pointBounds19274 := by
 decide +kernel
def cuts19275 : List PrefixCut := [⟨50,257294921,257295072⟩,
⟨128,664417685,664418079⟩]
theorem checked19275 : checkPrefixCuts (2^48) 2530344961 9 Manual.Count131072.C019275.packed 128 cuts19275 = true := by
 decide +kernel
def pointBounds19275 : List (Nat × Nat × Nat) := [(2530396160,99542158765773,99542538852370),(2530476032,99542565888537,99542945975377)]
theorem point_links_checked19275 : (cuts19275.take 2).map (fun c => (2530344961-1+2*2^9*c.k,99541901470852+c.lower,99542281557298+c.upper)) = pointBounds19275 := by
 decide +kernel
def cuts19276 : List PrefixCut := [⟨78,411447949,411448192⟩,
⟨128,672503190,672503590⟩]
theorem checked19276 : checkPrefixCuts (2^48) 2530476033 9 Manual.Count131072.C019276.packed 128 cuts19276 = true := by
 decide +kernel
def pointBounds19276 : List (Nat × Nat × Nat) := [(2530555904,99542977336486,99543357423569)]
theorem point_links_checked19276 : (cuts19276.take 1).map (fun c => (2530476033-1+2*2^9*c.k,99542565888537+c.lower,99542945975377+c.upper)) = pointBounds19276 := by
 decide +kernel
def cuts19277 : List PrefixCut := [⟨28,143038669,143038754⟩,
⟨106,554015752,554016079⟩,
⟨128,667240693,667241088⟩]
theorem checked19277 : checkPrefixCuts (2^48) 2530607105 9 Manual.Count131072.C019277.packed 128 cuts19277 = true := by
 decide +kernel
def pointBounds19277 : List (Nat × Nat × Nat) := [(2530635776,99543381430396,99543761517721),(2530715648,99543792407479,99544172495046)]
theorem point_links_checked19277 : (cuts19277.take 2).map (fun c => (2530607105-1+2*2^9*c.k,99543238391727+c.lower,99543618478967+c.upper)) = pointBounds19277 := by
 decide +kernel
def cuts19278 : List PrefixCut := [⟨56,290954591,290954767⟩,
⟨128,666983715,666984119⟩]
theorem checked19278 : checkPrefixCuts (2^48) 2530738177 9 Manual.Count131072.C019278.packed 128 cuts19278 = true := by
 decide +kernel
def pointBounds19278 : List (Nat × Nat × Nat) := [(2530795520,99544196587011,99544576674822)]
theorem point_links_checked19278 : (cuts19278.take 1).map (fun c => (2530738177-1+2*2^9*c.k,99543905632420+c.lower,99544285720055+c.upper)) = pointBounds19278 := by
 decide +kernel
def cuts19279 : List PrefixCut := [⟨6,31474284,31474303⟩,
⟨84,444859076,444859337⟩,
⟨128,677514383,677514783⟩]
theorem checked19279 : checkPrefixCuts (2^48) 2530869249 9 Manual.Count131072.C019279.packed 128 cuts19279 = true := by
 decide +kernel
def pointBounds19279 : List (Nat × Nat × Nat) := [(2530875392,99544604090419,99544984178477),(2530955264,99545017475211,99545397563511)]
theorem point_links_checked19279 : (cuts19279.take 2).map (fun c => (2530869249-1+2*2^9*c.k,99544572616135+c.lower,99544952704174+c.upper)) = pointBounds19279 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000289
