import PlattAssemblyKernel
import PlattCertificates.Count131072.C023264
import PlattCertificates.Count131072.C023265
import PlattCertificates.Count131072.C023266
import PlattCertificates.Count131072.C023267
import PlattCertificates.Count131072.C023268
import PlattCertificates.Count131072.C023269
import PlattCertificates.Count131072.C023270
import PlattCertificates.Count131072.C023271
import PlattCertificates.Count131072.C023272
import PlattCertificates.Count131072.C023273
import PlattCertificates.Count131072.C023274
import PlattCertificates.Count131072.C023275
import PlattCertificates.Count131072.C023276
import PlattCertificates.Count131072.C023277
import PlattCertificates.Count131072.C023278
import PlattCertificates.Count131072.C023279
import PlattCertificates.Count131072.C023280
import PlattCertificates.Count131072.C023281
import PlattCertificates.Count131072.C023282
import PlattCertificates.Count131072.C023283
import PlattCertificates.Count131072.C023284
import PlattCertificates.Count131072.C023285
import PlattCertificates.Count131072.C023286
import PlattCertificates.Count131072.C023287
import PlattCertificates.Count131072.C023288
import PlattCertificates.Count131072.C023289
import PlattCertificates.Count131072.C023290
import PlattCertificates.Count131072.C023291
import PlattCertificates.Count131072.C023292
import PlattCertificates.Count131072.C023293
import PlattCertificates.Count131072.C023294
import PlattCertificates.Count131072.C023295
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000102
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23264 : List PrefixCut := [⟨2,9772178,9772184⟩,
⟨96,419828389,419828624⟩,
⟨128,558385351,558385665⟩]
theorem checked23264 : checkPrefixCuts (2^48) 3053191169 9 Manual.Count131072.C023264.packed 128 cuts23264 = true := by
 decide +kernel
def pointBounds23264 : List (Nat × Nat × Nat) := [(3053193216,101973163542416,101973545037174),(3053289472,101973573598627,101973955093614)]
theorem point_links_checked23264 : (cuts23264.take 2).map (fun c => (3053191169-1+2*2^9*c.k,101973153770238+c.lower,101973535264990+c.upper)) = pointBounds23264 := by
 decide +kernel
def cuts23265 : List PrefixCut := [⟨62,270748769,270748919⟩,
⟨128,554489552,554489863⟩]
theorem checked23265 : checkPrefixCuts (2^48) 3053322241 9 Manual.Count131072.C023265.packed 128 cuts23265 = true := by
 decide +kernel
def pointBounds23265 : List (Nat × Nat × Nat) := [(3053385728,101973982904358,101974364399574)]
theorem point_links_checked23265 : (cuts23265.take 1).map (fun c => (3053322241-1+2*2^9*c.k,101973712155589+c.lower,101974093650655+c.upper)) = pointBounds23265 := by
 decide +kernel
def cuts23266 : List PrefixCut := [⟨28,121495943,121496012⟩,
⟨122,529669749,529670047⟩,
⟨128,554926690,554927002⟩]
theorem checked23266 : checkPrefixCuts (2^48) 3053453313 9 Manual.Count131072.C023266.packed 128 cuts23266 = true := by
 decide +kernel
def pointBounds23266 : List (Nat × Nat × Nat) := [(3053481984,101974388141084,101974769636530),(3053578240,101974796314890,101975177810565)]
theorem point_links_checked23266 : (cuts23266.take 2).map (fun c => (3053453313-1+2*2^9*c.k,101974266645141+c.lower,101974648140518+c.upper)) = pointBounds23266 := by
 decide +kernel
def cuts23267 : List PrefixCut := [⟨88,376543704,376543922⟩,
⟨128,548911298,548911613⟩]
theorem checked23267 : checkPrefixCuts (2^48) 3053584385 9 Manual.Count131072.C023267.packed 128 cuts23267 = true := by
 decide +kernel
def pointBounds23267 : List (Nat × Nat × Nat) := [(3053674496,101975198115535,101975579611442)]
theorem point_links_checked23267 : (cuts23267.take 1).map (fun c => (3053584385-1+2*2^9*c.k,101974821571831+c.lower,101975203067520+c.upper)) = pointBounds23267 := by
 decide +kernel
def cuts23268 : List PrefixCut := [⟨54,234950824,234950958⟩,
⟨128,555800692,555801007⟩]
theorem checked23268 : checkPrefixCuts (2^48) 3053715457 9 Manual.Count131072.C023268.packed 128 cuts23268 = true := by
 decide +kernel
def pointBounds23268 : List (Nat × Nat × Nat) := [(3053770752,101975605433953,101975986930091)]
theorem point_links_checked23268 : (cuts23268.take 1).map (fun c => (3053715457-1+2*2^9*c.k,101975370483129+c.lower,101975751979133+c.upper)) = pointBounds23268 := by
 decide +kernel
def cuts23269 : List PrefixCut := [⟨20,83690641,83690687⟩,
⟨114,486098511,486098796⟩,
⟨128,549232817,549233137⟩]
theorem checked23269 : checkPrefixCuts (2^48) 3053846529 9 Manual.Count131072.C023269.packed 128 cuts23269 = true := by
 decide +kernel
def pointBounds23269 : List (Nat × Nat × Nat) := [(3053867008,101976009974462,101976391470827),(3053963264,101976412382332,101976793878936)]
theorem point_links_checked23269 : (cuts23269.take 2).map (fun c => (3053846529-1+2*2^9*c.k,101975926283821+c.lower,101976307780140+c.upper)) = pointBounds23269 := by
 decide +kernel
def cuts23270 : List PrefixCut := [⟨80,354652508,354652700⟩,
⟨128,558057214,558057525⟩]
theorem checked23270 : checkPrefixCuts (2^48) 3053977601 9 Manual.Count131072.C023270.packed 128 cuts23270 = true := by
 decide +kernel
def pointBounds23270 : List (Nat × Nat × Nat) := [(3054059520,101976830169146,101977211665977)]
theorem point_links_checked23270 : (cuts23270.take 1).map (fun c => (3053977601-1+2*2^9*c.k,101976475516638+c.lower,101976857013277+c.upper)) = pointBounds23270 := by
 decide +kernel
def cuts23271 : List PrefixCut := [⟨46,199530718,199530826⟩,
⟨128,554807580,554807889⟩]
theorem checked23271 : checkPrefixCuts (2^48) 3054108673 9 Manual.Count131072.C023271.packed 128 cuts23271 = true := by
 decide +kernel
def pointBounds23271 : List (Nat × Nat × Nat) := [(3054155776,101977233104570,101977614601628)]
theorem point_links_checked23271 : (cuts23271.take 1).map (fun c => (3054108673-1+2*2^9*c.k,101977033573852+c.lower,101977415070802+c.upper)) = pointBounds23271 := by
 decide +kernel
def cuts23272 : List PrefixCut := [⟨12,55018659,55018688⟩,
⟨106,457191465,457191721⟩,
⟨128,550360303,550360612⟩]
theorem checked23272 : checkPrefixCuts (2^48) 3054239745 9 Manual.Count131072.C023272.packed 128 cuts23272 = true := by
 decide +kernel
def pointBounds23272 : List (Nat × Nat × Nat) := [(3054252032,101977643400091,101978024897379),(3054348288,101978045572897,101978427070412)]
theorem point_links_checked23272 : (cuts23272.take 2).map (fun c => (3054239745-1+2*2^9*c.k,101977588381432+c.lower,101977969878691+c.upper)) = pointBounds23272 := by
 decide +kernel
def cuts23273 : List PrefixCut := [⟨72,312308854,312309033⟩,
⟨128,550889617,550889930⟩]
theorem checked23273 : checkPrefixCuts (2^48) 3054370817 9 Manual.Count131072.C023273.packed 128 cuts23273 = true := by
 decide +kernel
def pointBounds23273 : List (Nat × Nat × Nat) := [(3054444544,101978451050589,101978832548336)]
theorem point_links_checked23273 : (cuts23273.take 1).map (fun c => (3054370817-1+2*2^9*c.k,101978138741735+c.lower,101978520239303+c.upper)) = pointBounds23273 := by
 decide +kernel
def cuts23274 : List PrefixCut := [⟨38,164856796,164856888⟩,
⟨128,555749729,555750037⟩]
theorem checked23274 : checkPrefixCuts (2^48) 3054501889 9 Manual.Count131072.C023274.packed 128 cuts23274 = true := by
 decide +kernel
def pointBounds23274 : List (Nat × Nat × Nat) := [(3054540800,101978854488148,101979235986121)]
theorem point_links_checked23274 : (cuts23274.take 1).map (fun c => (3054501889-1+2*2^9*c.k,101978689631352+c.lower,101979071129233+c.upper)) = pointBounds23274 := by
 decide +kernel
def cuts23275 : List PrefixCut := [⟨4,17323601,17323613⟩,
⟨98,419814292,419814535⟩,
⟨128,549183597,549183917⟩]
theorem checked23275 : checkPrefixCuts (2^48) 3054632961 9 Manual.Count131072.C023275.packed 128 cuts23275 = true := by
 decide +kernel
def pointBounds23275 : List (Nat × Nat × Nat) := [(3054637056,101979262704682,101979644202883),(3054733312,101979665195373,101980046693805)]
theorem point_links_checked23275 : (cuts23275.take 2).map (fun c => (3054632961-1+2*2^9*c.k,101979245381081+c.lower,101979626879270+c.upper)) = pointBounds23275 := by
 decide +kernel
def cuts23276 : List PrefixCut := [⟨64,275135820,275135976⟩,
⟨128,555702018,555702332⟩]
theorem checked23276 : checkPrefixCuts (2^48) 3054764033 9 Manual.Count131072.C023276.packed 128 cuts23276 = true := by
 decide +kernel
def pointBounds23276 : List (Nat × Nat × Nat) := [(3054829568,101980069700498,101980451199163)]
theorem point_links_checked23276 : (cuts23276.take 1).map (fun c => (3054764033-1+2*2^9*c.k,101979794564678+c.lower,101980176063187+c.upper)) = pointBounds23276 := by
 decide +kernel
def cuts23277 : List PrefixCut := [⟨30,130191717,130191792⟩,
⟨124,534394942,534395246⟩,
⟨128,550426446,550426759⟩]
theorem checked23277 : checkPrefixCuts (2^48) 3054895105 9 Manual.Count131072.C023277.packed 128 cuts23277 = true := by
 decide +kernel
def pointBounds23277 : List (Nat × Nat × Nat) := [(3054925824,101980480458413,101980861957311),(3055022080,101980884661638,101981266160765)]
theorem point_links_checked23277 : (cuts23277.take 2).map (fun c => (3054895105-1+2*2^9*c.k,101980350266696+c.lower,101980731765519+c.upper)) = pointBounds23277 := by
 decide +kernel
def cuts23278 : List PrefixCut := [⟨90,388435435,388435657⟩,
⟨128,551139937,551140249⟩]
theorem checked23278 : checkPrefixCuts (2^48) 3055026177 9 Manual.Count131072.C023278.packed 128 cuts23278 = true := by
 decide +kernel
def pointBounds23278 : List (Nat × Nat × Nat) := [(3055118336,101981289128577,101981670627935)]
theorem point_links_checked23278 : (cuts23278.take 1).map (fun c => (3055026177-1+2*2^9*c.k,101980900693142+c.lower,101981282192278+c.upper)) = pointBounds23278 := by
 decide +kernel
def cuts23279 : List PrefixCut := [⟨56,241933916,241934051⟩,
⟨128,549457946,549458255⟩]
theorem checked23279 : checkPrefixCuts (2^48) 3055157249 9 Manual.Count131072.C023279.packed 128 cuts23279 = true := by
 decide +kernel
def pointBounds23279 : List (Nat × Nat × Nat) := [(3055214592,101981693766995,101982075266578)]
theorem point_links_checked23279 : (cuts23279.take 1).map (fun c => (3055157249-1+2*2^9*c.k,101981451833079+c.lower,101981833332527+c.upper)) = pointBounds23279 := by
 decide +kernel
def cuts23280 : List PrefixCut := [⟨22,101063074,101063129⟩,
⟨116,505860241,505860522⟩,
⟨128,561042125,561042437⟩]
theorem checked23280 : checkPrefixCuts (2^48) 3055288321 9 Manual.Count131072.C023280.packed 128 cuts23280 = true := by
 decide +kernel
def pointBounds23280 : List (Nat × Nat × Nat) := [(3055310848,101982102354099,101982483853911),(3055407104,101982507151266,101982888651304)]
theorem point_links_checked23280 : (cuts23280.take 2).map (fun c => (3055288321-1+2*2^9*c.k,101982001291025+c.lower,101982382790782+c.upper)) = pointBounds23280 := by
 decide +kernel
def cuts23281 : List PrefixCut := [⟨82,351997782,351997984⟩,
⟨128,548950192,548950502⟩]
theorem checked23281 : checkPrefixCuts (2^48) 3055419393 9 Manual.Count131072.C023281.packed 128 cuts23281 = true := by
 decide +kernel
def pointBounds23281 : List (Nat × Nat × Nat) := [(3055503360,101982914330932,101983295831203)]
theorem point_links_checked23281 : (cuts23281.take 1).map (fun c => (3055419393-1+2*2^9*c.k,101982562333150+c.lower,101982943833219+c.upper)) = pointBounds23281 := by
 decide +kernel
def cuts23282 : List PrefixCut := [⟨48,201923660,201923781⟩,
⟨128,551782100,551782408⟩]
theorem checked23282 : checkPrefixCuts (2^48) 3055550465 9 Manual.Count131072.C023282.packed 128 cuts23282 = true := by
 decide +kernel
def pointBounds23282 : List (Nat × Nat × Nat) := [(3055599616,101983313207002,101983694707502)]
theorem point_links_checked23282 : (cuts23282.take 1).map (fun c => (3055550465-1+2*2^9*c.k,101983111283342+c.lower,101983492783721+c.upper)) = pointBounds23282 := by
 decide +kernel
def cuts23283 : List PrefixCut := [⟨14,59506322,59506353⟩,
⟨108,464805202,464805463⟩,
⟨128,554706133,554706448⟩]
theorem checked23283 : checkPrefixCuts (2^48) 3055681537 9 Manual.Count131072.C023283.packed 128 cuts23283 = true := by
 decide +kernel
def pointBounds23283 : List (Nat × Nat × Nat) := [(3055695872,101983722571764,101984104072482),(3055792128,101984127870644,101984509371592)]
theorem point_links_checked23283 : (cuts23283.take 2).map (fun c => (3055681537-1+2*2^9*c.k,101983663065442+c.lower,101984044566129+c.upper)) = pointBounds23283 := by
 decide +kernel
def cuts23284 : List PrefixCut := [⟨74,316306297,316306480⟩,
⟨128,549063699,549064011⟩]
theorem checked23284 : checkPrefixCuts (2^48) 3055812609 9 Manual.Count131072.C023284.packed 128 cuts23284 = true := by
 decide +kernel
def pointBounds23284 : List (Nat × Nat × Nat) := [(3055888384,101984534077872,101984915579057)]
theorem point_links_checked23284 : (cuts23284.take 1).map (fun c => (3055812609-1+2*2^9*c.k,101984217771575+c.lower,101984599272577+c.upper)) = pointBounds23284 := by
 decide +kernel
def cuts23285 : List PrefixCut := [⟨40,173621205,173621303⟩,
⟨128,555211267,555211582⟩]
theorem checked23285 : checkPrefixCuts (2^48) 3055943681 9 Manual.Count131072.C023285.packed 128 cuts23285 = true := by
 decide +kernel
def pointBounds23285 : List (Nat × Nat × Nat) := [(3055984640,101984940456479,101985321957891)]
theorem point_links_checked23285 : (cuts23285.take 1).map (fun c => (3055943681-1+2*2^9*c.k,101984766835274+c.lower,101985148336588+c.upper)) = pointBounds23285 := by
 decide +kernel
def cuts23286 : List PrefixCut := [⟨6,26433653,26433666⟩,
⟨100,435457578,435457821⟩,
⟨128,557950429,557950741⟩]
theorem checked23286 : checkPrefixCuts (2^48) 3056074753 9 Manual.Count131072.C023286.packed 128 cuts23286 = true := by
 decide +kernel
def pointBounds23286 : List (Nat × Nat × Nat) := [(3056080896,101985348480194,101985729981836),(3056177152,101985757504119,101986139005991)]
theorem point_links_checked23286 : (cuts23286.take 2).map (fun c => (3056074753-1+2*2^9*c.k,101985322046541+c.lower,101985703548170+c.upper)) = pointBounds23286 := by
 decide +kernel
def cuts23287 : List PrefixCut := [⟨66,286886576,286886741⟩,
⟨128,557742287,557742601⟩]
theorem checked23287 : checkPrefixCuts (2^48) 3056205825 9 Manual.Count131072.C023287.packed 128 cuts23287 = true := by
 decide +kernel
def pointBounds23287 : List (Nat × Nat × Nat) := [(3056273408,101986166883546,101986548385652)]
theorem point_links_checked23287 : (cuts23287.take 1).map (fun c => (3056205825-1+2*2^9*c.k,101985879996970+c.lower,101986261498911+c.upper)) = pointBounds23287 := by
 decide +kernel
def cuts23288 : List PrefixCut := [⟨32,136761093,136761167⟩,
⟨126,545193824,545194133⟩,
⟨128,553574158,553574472⟩]
theorem checked23288 : checkPrefixCuts (2^48) 3056336897 9 Manual.Count131072.C023288.packed 128 cuts23288 = true := by
 decide +kernel
def pointBounds23288 : List (Nat × Nat × Nat) := [(3056369664,101986574500350,101986956002679),(3056465920,101986982933081,101987364435645)]
theorem point_links_checked23288 : (cuts23288.take 2).map (fun c => (3056336897-1+2*2^9*c.k,101986437739257+c.lower,101986819241512+c.upper)) = pointBounds23288 := by
 decide +kernel
def cuts23289 : List PrefixCut := [⟨92,399487038,399487263⟩,
⟨128,556865709,556866023⟩]
theorem checked23289 : checkPrefixCuts (2^48) 3056467969 9 Manual.Count131072.C023289.packed 128 cuts23289 = true := by
 decide +kernel
def pointBounds23289 : List (Nat × Nat × Nat) := [(3056562176,101987390800453,101987772303247)]
theorem point_links_checked23289 : (cuts23289.take 1).map (fun c => (3056467969-1+2*2^9*c.k,101986991313415+c.lower,101987372815984+c.upper)) = pointBounds23289 := by
 decide +kernel
def cuts23290 : List PrefixCut := [⟨58,253790977,253791118⟩,
⟨128,558683583,558683892⟩]
theorem checked23290 : checkPrefixCuts (2^48) 3056599041 9 Manual.Count131072.C023290.packed 128 cuts23290 = true := by
 decide +kernel
def pointBounds23290 : List (Nat × Nat × Nat) := [(3056658432,101987801970101,101988183473125)]
theorem point_links_checked23290 : (cuts23290.take 1).map (fun c => (3056599041-1+2*2^9*c.k,101987548179124+c.lower,101987929682007+c.upper)) = pointBounds23290 := by
 decide +kernel
def cuts23291 : List PrefixCut := [⟨24,108382033,108382096⟩,
⟨118,510501767,510502070⟩,
⟨128,554055543,554055871⟩]
theorem checked23291 : checkPrefixCuts (2^48) 3056730113 9 Manual.Count131072.C023291.packed 128 cuts23291 = true := by
 decide +kernel
def pointBounds23291 : List (Nat × Nat × Nat) := [(3056754688,101988215244740,101988596747995),(3056850944,101988617364474,101988998867969)]
theorem point_links_checked23291 : (cuts23291.take 2).map (fun c => (3056730113-1+2*2^9*c.k,101988106862707+c.lower,101988488365899+c.upper)) = pointBounds23291 := by
 decide +kernel
def cuts23292 : List PrefixCut := [⟨84,363157277,363157489⟩,
⟨128,555597028,555597351⟩]
theorem checked23292 : checkPrefixCuts (2^48) 3056861185 9 Manual.Count131072.C023292.packed 128 cuts23292 = true := by
 decide +kernel
def pointBounds23292 : List (Nat × Nat × Nat) := [(3056947200,101989024075527,101989405579259)]
theorem point_links_checked23292 : (cuts23292.take 1).map (fun c => (3056861185-1+2*2^9*c.k,101988660918250+c.lower,101989042421770+c.upper)) = pointBounds23292 := by
 decide +kernel
def cuts23293 : List PrefixCut := [⟨50,214258481,214258603⟩,
⟨128,547562869,547563182⟩]
theorem checked23293 : checkPrefixCuts (2^48) 3056992257 9 Manual.Count131072.C023293.packed 128 cuts23293 = true := by
 decide +kernel
def pointBounds23293 : List (Nat × Nat × Nat) := [(3057043456,101989430773759,101989812277724)]
theorem point_links_checked23293 : (cuts23293.take 1).map (fun c => (3056992257-1+2*2^9*c.k,101989216515278+c.lower,101989598019121+c.upper)) = pointBounds23293 := by
 decide +kernel
def cuts23294 : List PrefixCut := [⟨16,69237820,69237856⟩,
⟨110,478028128,478028390⟩,
⟨128,557206729,557207038⟩]
theorem checked23294 : checkPrefixCuts (2^48) 3057123329 9 Manual.Count131072.C023294.packed 128 cuts23294 = true := by
 decide +kernel
def pointBounds23294 : List (Nat × Nat × Nat) := [(3057139712,101989833315967,101990214820159),(3057235968,101990242106275,101990623610693)]
theorem point_links_checked23294 : (cuts23294.take 2).map (fun c => (3057123329-1+2*2^9*c.k,101989764078147+c.lower,101990145582303+c.upper)) = pointBounds23294 := by
 decide +kernel
def cuts23295 : List PrefixCut := [⟨76,327573280,327573470⟩,
⟨128,550738170,550738488⟩]
theorem checked23295 : checkPrefixCuts (2^48) 3057254401 9 Manual.Count131072.C023295.packed 128 cuts23295 = true := by
 decide +kernel
def pointBounds23295 : List (Nat × Nat × Nat) := [(3057332224,101990648858156,101991030362811)]
theorem point_links_checked23295 : (cuts23295.take 1).map (fun c => (3057254401-1+2*2^9*c.k,101990321284876+c.lower,101990702789341+c.upper)) = pointBounds23295 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000102
