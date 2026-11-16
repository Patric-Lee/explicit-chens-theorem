import PlattAssemblyKernel
import PlattCertificates.Count131072.C020256
import PlattCertificates.Count131072.C020257
import PlattCertificates.Count131072.C020258
import PlattCertificates.Count131072.C020259
import PlattCertificates.Count131072.C020260
import PlattCertificates.Count131072.C020261
import PlattCertificates.Count131072.C020262
import PlattCertificates.Count131072.C020263
import PlattCertificates.Count131072.C020264
import PlattCertificates.Count131072.C020265
import PlattCertificates.Count131072.C020266
import PlattCertificates.Count131072.C020267
import PlattCertificates.Count131072.C020268
import PlattCertificates.Count131072.C020269
import PlattCertificates.Count131072.C020270
import PlattCertificates.Count131072.C020271
import PlattCertificates.Count131072.C020272
import PlattCertificates.Count131072.C020273
import PlattCertificates.Count131072.C020274
import PlattCertificates.Count131072.C020275
import PlattCertificates.Count131072.C020276
import PlattCertificates.Count131072.C020277
import PlattCertificates.Count131072.C020278
import PlattCertificates.Count131072.C020279
import PlattCertificates.Count131072.C020280
import PlattCertificates.Count131072.C020281
import PlattCertificates.Count131072.C020282
import PlattCertificates.Count131072.C020283
import PlattCertificates.Count131072.C020284
import PlattCertificates.Count131072.C020285
import PlattCertificates.Count131072.C020286
import PlattCertificates.Count131072.C020287
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20256 : List PrefixCut := [⟨24,120256805,120256875⟩,
⟨106,535854056,535854373⟩,
⟨128,646684831,646685214⟩]
theorem checked20256 : checkPrefixCuts (2^48) 2658926593 9 Manual.Count131072.C020256.packed 128 cuts20256 = true := by
 decide +kernel
def pointBounds20256 : List (Nat × Nat × Nat) := [(2658951168,100185719589172,100186100055660),(2659035136,100186135186423,100186515653158)]
theorem point_links_checked20256 : (cuts20256.take 2).map (fun c => (2658926593-1+2*2^9*c.k,100185599332367+c.lower,100185979798785+c.upper)) = pointBounds20256 := by
 decide +kernel
def cuts20257 : List PrefixCut := [⟨60,303271446,303271626⟩,
⟨128,641678033,641678415⟩]
theorem checked20257 : checkPrefixCuts (2^48) 2659057665 9 Manual.Count131072.C020257.packed 128 cuts20257 = true := by
 decide +kernel
def pointBounds20257 : List (Nat × Nat × Nat) := [(2659119104,100186549288644,100186929755625)]
theorem point_links_checked20257 : (cuts20257.take 1).map (fun c => (2659057665-1+2*2^9*c.k,100186246017198+c.lower,100186626483999+c.upper)) = pointBounds20257 := by
 decide +kernel
def cuts20258 : List PrefixCut := [⟨14,66791111,66791152⟩,
⟨96,473352031,473352312⟩,
⟨128,634977897,634978275⟩]
theorem checked20258 : checkPrefixCuts (2^48) 2659188737 9 Manual.Count131072.C020258.packed 128 cuts20258 = true := by
 decide +kernel
def pointBounds20258 : List (Nat × Nat × Nat) := [(2659203072,100186954486342,100187334953566),(2659287040,100187361047262,100187741514726)]
theorem point_links_checked20258 : (cuts20258.take 2).map (fun c => (2659188737-1+2*2^9*c.k,100186887695231+c.lower,100187268162414+c.upper)) = pointBounds20258 := by
 decide +kernel
def cuts20259 : List PrefixCut := [⟨50,248732611,248732753⟩,
⟨128,634311537,634311909⟩]
theorem checked20259 : checkPrefixCuts (2^48) 2659319809 9 Manual.Count131072.C020259.packed 128 cuts20259 = true := by
 decide +kernel
def pointBounds20259 : List (Nat × Nat × Nat) := [(2659371008,100187771405739,100188151873442)]
theorem point_links_checked20259 : (cuts20259.take 1).map (fun c => (2659319809-1+2*2^9*c.k,100187522673128+c.lower,100187903140689+c.upper)) = pointBounds20259 := by
 decide +kernel
def cuts20260 : List PrefixCut := [⟨4,19262770,19262781⟩,
⟨86,431288711,431288964⟩,
⟨128,640948062,640948439⟩]
theorem checked20260 : checkPrefixCuts (2^48) 2659450881 9 Manual.Count131072.C020260.packed 128 cuts20260 = true := by
 decide +kernel
def pointBounds20260 : List (Nat × Nat × Nat) := [(2659454976,100188176247435,100188556715379),(2659538944,100188588273376,100188968741562)]
theorem point_links_checked20260 : (cuts20260.take 2).map (fun c => (2659450881-1+2*2^9*c.k,100188156984665+c.lower,100188537452598+c.upper)) = pointBounds20260 := by
 decide +kernel
def cuts20261 : List PrefixCut := [⟨40,194098549,194098664⟩,
⟨122,601759409,601759760⟩,
⟨128,632873184,632873554⟩]
theorem checked20261 : checkPrefixCuts (2^48) 2659581953 9 Manual.Count131072.C020261.packed 128 cuts20261 = true := by
 decide +kernel
def pointBounds20261 : List (Nat × Nat × Nat) := [(2659622912,100188992031276,100189372499701),(2659706880,100189399692136,100189780160797)]
theorem point_links_checked20261 : (cuts20261.take 2).map (fun c => (2659581953-1+2*2^9*c.k,100188797932727+c.lower,100189178401037+c.upper)) = pointBounds20261 := by
 decide +kernel
def cuts20262 : List PrefixCut := [⟨76,372195308,372195525⟩,
⟨128,628714879,628715243⟩]
theorem checked20262 : checkPrefixCuts (2^48) 2659713025 9 Manual.Count131072.C020262.packed 128 cuts20262 = true := by
 decide +kernel
def pointBounds20262 : List (Nat × Nat × Nat) := [(2659790848,100189803001219,100190183470116)]
theorem point_links_checked20262 : (cuts20262.take 1).map (fun c => (2659713025-1+2*2^9*c.k,100189430805911+c.lower,100189811274591+c.upper)) = pointBounds20262 := by
 decide +kernel
def cuts20263 : List PrefixCut := [⟨30,149951507,149951594⟩,
⟨112,559901851,559902184⟩,
⟨128,641488256,641488637⟩]
theorem checked20263 : checkPrefixCuts (2^48) 2659844097 9 Manual.Count131072.C020263.packed 128 cuts20263 = true := by
 decide +kernel
def pointBounds20263 : List (Nat × Nat × Nat) := [(2659874816,100190209472297,100190589941428),(2659958784,100190619422641,100190999892018)]
theorem point_links_checked20263 : (cuts20263.take 2).map (fun c => (2659844097-1+2*2^9*c.k,100190059520790+c.lower,100190439989834+c.upper)) = pointBounds20263 := by
 decide +kernel
def cuts20264 : List PrefixCut := [⟨66,330361547,330361740⟩,
⟨128,639975231,639975603⟩]
theorem checked20264 : checkPrefixCuts (2^48) 2659975169 9 Manual.Count131072.C020264.packed 128 cuts20264 = true := by
 decide +kernel
def pointBounds20264 : List (Nat × Nat × Nat) := [(2660042752,100191031370593,100191411840211)]
theorem point_links_checked20264 : (cuts20264.take 1).map (fun c => (2659975169-1+2*2^9*c.k,100190701009046+c.lower,100191081478471+c.upper)) = pointBounds20264 := by
 decide +kernel
def cuts20265 : List PrefixCut := [⟨20,100733974,100734033⟩,
⟨102,505884005,505884302⟩,
⟨128,634759026,634759396⟩]
theorem checked20265 : checkPrefixCuts (2^48) 2660106241 9 Manual.Count131072.C020265.packed 128 cuts20265 = true := by
 decide +kernel
def pointBounds20265 : List (Nat × Nat × Nat) := [(2660126720,100191441718251,100191822188107),(2660210688,100191846868282,100192227338376)]
theorem point_links_checked20265 : (cuts20265.take 2).map (fun c => (2660106241-1+2*2^9*c.k,100191340984277+c.lower,100191721454074+c.upper)) = pointBounds20265 := by
 decide +kernel
def cuts20266 : List PrefixCut := [⟨56,276579663,276579826⟩,
⟨128,639594682,639595062⟩]
theorem checked20266 : checkPrefixCuts (2^48) 2660237313 9 Manual.Count131072.C020266.packed 128 cuts20266 = true := by
 decide +kernel
def pointBounds20266 : List (Nat × Nat × Nat) := [(2660294656,100192252322966,100192632793296)]
theorem point_links_checked20266 : (cuts20266.take 1).map (fun c => (2660237313-1+2*2^9*c.k,100191975743303+c.lower,100192356213470+c.upper)) = pointBounds20266 := by
 decide +kernel
def cuts20267 : List PrefixCut := [⟨10,47611249,47611276⟩,
⟨92,457272348,457272616⟩,
⟨128,640938533,640938905⟩]
theorem checked20267 : checkPrefixCuts (2^48) 2660368385 9 Manual.Count131072.C020267.packed 128 cuts20267 = true := by
 decide +kernel
def pointBounds20267 : List (Nat × Nat × Nat) := [(2660378624,100192662949234,100193043419808),(2660462592,100193072610333,100193453081148)]
theorem point_links_checked20267 : (cuts20267.take 2).map (fun c => (2660368385-1+2*2^9*c.k,100192615337985+c.lower,100192995808532+c.upper)) = pointBounds20267 := by
 decide +kernel
def cuts20268 : List PrefixCut := [⟨46,227886365,227886501⟩,
⟨128,631385508,631385879⟩]
theorem checked20268 : checkPrefixCuts (2^48) 2660499457 9 Manual.Count131072.C020268.packed 128 cuts20268 = true := by
 decide +kernel
def pointBounds20268 : List (Nat × Nat × Nat) := [(2660546560,100193484162883,100193864633938),(2660630528,100193887662026,100194268133316)]
theorem point_links_checked20268 : (cuts20268.take 2).map (fun c => (2660499457-1+2*2^9*c.k,100193256276518+c.lower,100193636747437+c.upper)) = pointBounds20268 := by
 decide +kernel
def cuts20269 : List PrefixCut := [⟨82,408564431,408564666⟩,
⟨128,635374504,635374871⟩]
theorem checked20269 : checkPrefixCuts (2^48) 2660630529 9 Manual.Count131072.C020269.packed 128 cuts20269 = true := by
 decide +kernel
def pointBounds20269 : List (Nat × Nat × Nat) := [(2660714496,100194296226457,100194676697982)]
theorem point_links_checked20269 : (cuts20269.take 1).map (fun c => (2660630529-1+2*2^9*c.k,100193887662026+c.lower,100194268133316+c.upper)) = pointBounds20269 := by
 decide +kernel
def cuts20270 : List PrefixCut := [⟨36,174971057,174971160⟩,
⟨118,582663438,582663780⟩,
⟨128,635554605,635554978⟩]
theorem checked20270 : checkPrefixCuts (2^48) 2660761601 9 Manual.Count131072.C020270.packed 128 cuts20270 = true := by
 decide +kernel
def pointBounds20270 : List (Nat × Nat × Nat) := [(2660798464,100194698007587,100195078479347),(2660882432,100195105699968,100195486171967)]
theorem point_links_checked20270 : (cuts20270.take 2).map (fun c => (2660761601-1+2*2^9*c.k,100194523036530+c.lower,100194903508187+c.upper)) = pointBounds20270 := by
 decide +kernel
def cuts20271 : List PrefixCut := [⟨72,359760006,359760219⟩,
⟨128,636369611,636369982⟩]
theorem checked20271 : checkPrefixCuts (2^48) 2660892673 9 Manual.Count131072.C020271.packed 128 cuts20271 = true := by
 decide +kernel
def pointBounds20271 : List (Nat × Nat × Nat) := [(2660966400,100195518351141,100195898823384)]
theorem point_links_checked20271 : (cuts20271.take 1).map (fun c => (2660892673-1+2*2^9*c.k,100195158591135+c.lower,100195539063165+c.upper)) = pointBounds20271 := by
 decide +kernel
def cuts20272 : List PrefixCut := [⟨26,126191227,126191302⟩,
⟨108,542518448,542518766⟩,
⟨128,645857814,645858193⟩]
theorem checked20272 : checkPrefixCuts (2^48) 2661023745 9 Manual.Count131072.C020272.packed 128 cuts20272 = true := by
 decide +kernel
def pointBounds20272 : List (Nat × Nat × Nat) := [(2661050368,100195921151973,100196301624449),(2661134336,100196337479194,100196717951913)]
theorem point_links_checked20272 : (cuts20272.take 2).map (fun c => (2661023745-1+2*2^9*c.k,100195794960746+c.lower,100196175433147+c.upper)) = pointBounds20272 := by
 decide +kernel
def cuts20273 : List PrefixCut := [⟨62,312551674,312551852⟩,
⟨128,638739699,638740070⟩]
theorem checked20273 : checkPrefixCuts (2^48) 2661154817 9 Manual.Count131072.C020273.packed 128 cuts20273 = true := by
 decide +kernel
def pointBounds20273 : List (Nat × Nat × Nat) := [(2661218304,100196753370234,100197133843192)]
theorem point_links_checked20273 : (cuts20273.take 1).map (fun c => (2661154817-1+2*2^9*c.k,100196440818560+c.lower,100196821291340+c.upper)) = pointBounds20273 := by
 decide +kernel
def cuts20274 : List PrefixCut := [⟨16,78161203,78161249⟩,
⟨98,483978307,483978590⟩,
⟨128,636275452,636275823⟩]
theorem checked20274 : checkPrefixCuts (2^48) 2661285889 9 Manual.Count131072.C020274.packed 128 cuts20274 = true := by
 decide +kernel
def pointBounds20274 : List (Nat × Nat × Nat) := [(2661302272,100197157719462,100197538192659),(2661386240,100197563536566,100197944010000)]
theorem point_links_checked20274 : (cuts20274.take 2).map (fun c => (2661285889-1+2*2^9*c.k,100197079558259+c.lower,100197460031410+c.upper)) = pointBounds20274 := by
 decide +kernel
def cuts20275 : List PrefixCut := [⟨52,261016253,261016406⟩,
⟨128,638994000,638994378⟩]
theorem checked20275 : checkPrefixCuts (2^48) 2661416961 9 Manual.Count131072.C020275.packed 128 cuts20275 = true := by
 decide +kernel
def pointBounds20275 : List (Nat × Nat × Nat) := [(2661470208,100197976849964,100198357323639)]
theorem point_links_checked20275 : (cuts20275.take 1).map (fun c => (2661416961-1+2*2^9*c.k,100197715833711+c.lower,100198096307233+c.upper)) = pointBounds20275 := by
 decide +kernel
def cuts20276 : List PrefixCut := [⟨6,29294401,29294417⟩,
⟨88,440783847,440784102⟩,
⟨128,642981087,642981460⟩]
theorem checked20276 : checkPrefixCuts (2^48) 2661548033 9 Manual.Count131072.C020276.packed 128 cuts20276 = true := by
 decide +kernel
def pointBounds20276 : List (Nat × Nat × Nat) := [(2661554176,100198384122112,100198764596028),(2661638144,100198795611558,100199176085713)]
theorem point_links_checked20276 : (cuts20276.take 2).map (fun c => (2661548033-1+2*2^9*c.k,100198354827711+c.lower,100198735301611+c.upper)) = pointBounds20276 := by
 decide +kernel
def cuts20277 : List PrefixCut := [⟨42,213826533,213826655⟩,
⟨124,628462439,628462809⟩,
⟨128,647919657,647920039⟩]
theorem checked20277 : checkPrefixCuts (2^48) 2661679105 9 Manual.Count131072.C020277.packed 128 cuts20277 = true := by
 decide +kernel
def pointBounds20277 : List (Nat × Nat × Nat) := [(2661722112,100199211635331,100199592109726),(2661806080,100199626271237,100200006745880)]
theorem point_links_checked20277 : (cuts20277.take 2).map (fun c => (2661679105-1+2*2^9*c.k,100198997808798+c.lower,100199378283071+c.upper)) = pointBounds20277 := by
 decide +kernel
def cuts20278 : List PrefixCut := [⟨78,383110781,383111007⟩,
⟨128,629594137,629594512⟩]
theorem checked20278 : checkPrefixCuts (2^48) 2661810177 9 Manual.Count131072.C020278.packed 128 cuts20278 = true := by
 decide +kernel
def pointBounds20278 : List (Nat × Nat × Nat) := [(2661890048,100200028839236,100200409314117)]
theorem point_links_checked20278 : (cuts20278.take 1).map (fun c => (2661810177-1+2*2^9*c.k,100199645728455+c.lower,100200026203110+c.upper)) = pointBounds20278 := by
 decide +kernel
def cuts20279 : List PrefixCut := [⟨32,162733580,162733675⟩,
⟨114,571726251,571726586⟩,
⟨128,642569062,642569438⟩]
theorem checked20279 : checkPrefixCuts (2^48) 2661941249 9 Manual.Count131072.C020279.packed 128 cuts20279 = true := by
 decide +kernel
def pointBounds20279 : List (Nat × Nat × Nat) := [(2661974016,100200438056172,100200818531297),(2662057984,100200847048843,100201227524208)]
theorem point_links_checked20279 : (cuts20279.take 2).map (fun c => (2661941249-1+2*2^9*c.k,100200275322592+c.lower,100200655797622+c.upper)) = pointBounds20279 := by
 decide +kernel
def cuts20280 : List PrefixCut := [⟨68,337291007,337291200⟩,
⟨128,637462056,637462422⟩]
theorem checked20280 : checkPrefixCuts (2^48) 2662072321 9 Manual.Count131072.C020280.packed 128 cuts20280 = true := by
 decide +kernel
def pointBounds20280 : List (Nat × Nat × Nat) := [(2662141952,100201255182661,100201635658260)]
theorem point_links_checked20280 : (cuts20280.take 1).map (fun c => (2662072321-1+2*2^9*c.k,100200917891654+c.lower,100201298367060+c.upper)) = pointBounds20280 := by
 decide +kernel
def cuts20281 : List PrefixCut := [⟨22,106575429,106575494⟩,
⟨104,514683495,514683793⟩,
⟨128,636690535,636690904⟩]
theorem checked20281 : checkPrefixCuts (2^48) 2662203393 9 Manual.Count131072.C020281.packed 128 cuts20281 = true := by
 decide +kernel
def pointBounds20281 : List (Nat × Nat × Nat) := [(2662225920,100201661929139,100202042404976),(2662309888,100202070037205,100202450513275)]
theorem point_links_checked20281 : (cuts20281.take 2).map (fun c => (2662203393-1+2*2^9*c.k,100201555353710+c.lower,100201935829482+c.upper)) = pointBounds20281 := by
 decide +kernel
def cuts20282 : List PrefixCut := [⟨58,295180502,295180676⟩,
⟨128,636448068,636448444⟩]
theorem checked20282 : checkPrefixCuts (2^48) 2662334465 9 Manual.Count131072.C020282.packed 128 cuts20282 = true := by
 decide +kernel
def pointBounds20282 : List (Nat × Nat × Nat) := [(2662393856,100202487224747,100202867701062)]
theorem point_links_checked20282 : (cuts20282.take 1).map (fun c => (2662334465-1+2*2^9*c.k,100202192044245+c.lower,100202572520386+c.upper)) = pointBounds20282 := by
 decide +kernel
def cuts20283 : List PrefixCut := [⟨12,61528688,61528723⟩,
⟨94,476152676,476152953⟩,
⟨128,644662574,644662950⟩]
theorem checked20283 : checkPrefixCuts (2^48) 2662465537 9 Manual.Count131072.C020283.packed 128 cuts20283 = true := by
 decide +kernel
def pointBounds20283 : List (Nat × Nat × Nat) := [(2662477824,100202890021001,100203270497553),(2662561792,100203304644989,100203685121783)]
theorem point_links_checked20283 : (cuts20283.take 2).map (fun c => (2662465537-1+2*2^9*c.k,100202828492313+c.lower,100203208968830+c.upper)) = pointBounds20283 := by
 decide +kernel
def cuts20284 : List PrefixCut := [⟨48,231723900,231724036⟩,
⟨128,626131136,626131500⟩]
theorem checked20284 : checkPrefixCuts (2^48) 2662596609 9 Manual.Count131072.C020284.packed 128 cuts20284 = true := by
 decide +kernel
def pointBounds20284 : List (Nat × Nat × Nat) := [(2662645760,100203704878787,100204085355816)]
theorem point_links_checked20284 : (cuts20284.take 1).map (fun c => (2662596609-1+2*2^9*c.k,100203473154887+c.lower,100203853631780+c.upper)) = pointBounds20284 := by
 decide +kernel
def cuts20285 : List PrefixCut := [⟨2,9513828,9513833⟩,
⟨84,423147274,423147522⟩,
⟨128,644176284,644176662⟩]
theorem checked20285 : checkPrefixCuts (2^48) 2662727681 9 Manual.Count131072.C020285.packed 128 cuts20285 = true := by
 decide +kernel
def pointBounds20285 : List (Nat × Nat × Nat) := [(2662729728,100204108799851,100204489277113),(2662813696,100204522433297,100204902910802)]
theorem point_links_checked20285 : (cuts20285.take 2).map (fun c => (2662727681-1+2*2^9*c.k,100204099286023+c.lower,100204479763280+c.upper)) = pointBounds20285 := by
 decide +kernel
def cuts20286 : List PrefixCut := [⟨38,189631632,189631740⟩,
⟨120,595945568,595945908⟩,
⟨128,635159893,635160255⟩]
theorem checked20286 : checkPrefixCuts (2^48) 2662858753 9 Manual.Count131072.C020286.packed 128 cuts20286 = true := by
 decide +kernel
def pointBounds20286 : List (Nat × Nat × Nat) := [(2662897664,100204933093939,100205313571682),(2662981632,100205339407875,100205719885850)]
theorem point_links_checked20286 : (cuts20286.take 2).map (fun c => (2662858753-1+2*2^9*c.k,100204743462307+c.lower,100205123939942+c.upper)) = pointBounds20286 := by
 decide +kernel
def cuts20287 : List PrefixCut := [⟨74,367720944,367721159⟩,
⟨128,638933592,638933967⟩]
theorem checked20287 : checkPrefixCuts (2^48) 2662989825 9 Manual.Count131072.C020287.packed 128 cuts20287 = true := by
 decide +kernel
def pointBounds20287 : List (Nat × Nat × Nat) := [(2663065600,100205746343144,100206126821356)]
theorem point_links_checked20287 : (cuts20287.take 1).map (fun c => (2662989825-1+2*2^9*c.k,100205378622200+c.lower,100205759100197+c.upper)) = pointBounds20287 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000008
