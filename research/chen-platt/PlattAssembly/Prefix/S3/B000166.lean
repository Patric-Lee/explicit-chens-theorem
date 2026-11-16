import PlattAssemblyKernel
import PlattCertificates.Count131072.C025312
import PlattCertificates.Count131072.C025313
import PlattCertificates.Count131072.C025314
import PlattCertificates.Count131072.C025315
import PlattCertificates.Count131072.C025316
import PlattCertificates.Count131072.C025317
import PlattCertificates.Count131072.C025318
import PlattCertificates.Count131072.C025319
import PlattCertificates.Count131072.C025320
import PlattCertificates.Count131072.C025321
import PlattCertificates.Count131072.C025322
import PlattCertificates.Count131072.C025323
import PlattCertificates.Count131072.C025324
import PlattCertificates.Count131072.C025325
import PlattCertificates.Count131072.C025326
import PlattCertificates.Count131072.C025327
import PlattCertificates.Count131072.C025328
import PlattCertificates.Count131072.C025329
import PlattCertificates.Count131072.C025330
import PlattCertificates.Count131072.C025331
import PlattCertificates.Count131072.C025332
import PlattCertificates.Count131072.C025333
import PlattCertificates.Count131072.C025334
import PlattCertificates.Count131072.C025335
import PlattCertificates.Count131072.C025336
import PlattCertificates.Count131072.C025337
import PlattCertificates.Count131072.C025338
import PlattCertificates.Count131072.C025339
import PlattCertificates.Count131072.C025340
import PlattCertificates.Count131072.C025341
import PlattCertificates.Count131072.C025342
import PlattCertificates.Count131072.C025343
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000166
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25312 : List PrefixCut := [⟨34,133041221,133041292⟩,
⟨128,505803517,505803792⟩]
theorem checked25312 : checkPrefixCuts (2^48) 3321626625 9 Manual.Count131072.C025312.packed 128 cuts25312 = true := by
 decide +kernel
def pointBounds25312 : List (Nat × Nat × Nat) := [(3321661440,103057242595882,103057624701752)]
theorem point_links_checked25312 : (cuts25312.take 1).map (fun c => (3321626625-1+2*2^9*c.k,103057109554661+c.lower,103057491660460+c.upper)) = pointBounds25312 := by
 decide +kernel
def cuts25313 : List PrefixCut := [⟨8,31267815,31267834⟩,
⟨110,432488965,432489210⟩,
⟨128,504173610,504173896⟩]
theorem checked25313 : checkPrefixCuts (2^48) 3321757697 9 Manual.Count131072.C025313.packed 128 cuts25313 = true := by
 decide +kernel
def pointBounds25313 : List (Nat × Nat × Nat) := [(3321765888,103057646625993,103058028732086),(3321870336,103058047847143,103058429953462)]
theorem point_links_checked25313 : (cuts25313.take 2).map (fun c => (3321757697-1+2*2^9*c.k,103057615358178+c.lower,103057997464252+c.upper)) = pointBounds25313 := by
 decide +kernel
def cuts25314 : List PrefixCut := [⟨84,333929960,333930147⟩,
⟨128,509322339,509322627⟩]
theorem checked25314 : checkPrefixCuts (2^48) 3321888769 9 Manual.Count131072.C025314.packed 128 cuts25314 = true := by
 decide +kernel
def pointBounds25314 : List (Nat × Nat × Nat) := [(3321974784,103058453461748,103058835568295)]
theorem point_links_checked25314 : (cuts25314.take 1).map (fun c => (3321888769-1+2*2^9*c.k,103058119531788+c.lower,103058501638148+c.upper)) = pointBounds25314 := by
 decide +kernel
def cuts25315 : List PrefixCut := [⟨58,230294211,230294337⟩,
⟨128,511505157,511505434⟩]
theorem checked25315 : checkPrefixCuts (2^48) 3322019841 9 Manual.Count131072.C025315.packed 128 cuts25315 = true := by
 decide +kernel
def pointBounds25315 : List (Nat × Nat × Nat) := [(3322079232,103058859148338,103059241255112)]
theorem point_links_checked25315 : (cuts25315.take 1).map (fun c => (3322019841-1+2*2^9*c.k,103058628854127+c.lower,103059010960775+c.upper)) = pointBounds25315 := by
 decide +kernel
def cuts25316 : List PrefixCut := [⟨32,123530922,123530991⟩,
⟨128,499538740,499539021⟩]
theorem checked25316 : checkPrefixCuts (2^48) 3322150913 9 Manual.Count131072.C025316.packed 128 cuts25316 = true := by
 decide +kernel
def pointBounds25316 : List (Nat × Nat × Nat) := [(3322183680,103059263890206,103059645997200)]
theorem point_links_checked25316 : (cuts25316.take 1).map (fun c => (3322150913-1+2*2^9*c.k,103059140359284+c.lower,103059522466209+c.upper)) = pointBounds25316 := by
 decide +kernel
def cuts25317 : List PrefixCut := [⟨6,23468351,23468363⟩,
⟨108,430387482,430387723⟩,
⟨128,508584298,508584588⟩]
theorem checked25317 : checkPrefixCuts (2^48) 3322281985 9 Manual.Count131072.C025317.packed 128 cuts25317 = true := by
 decide +kernel
def pointBounds25317 : List (Nat × Nat × Nat) := [(3322288128,103059663366375,103060045473593),(3322392576,103060070285506,103060452392953)]
theorem point_links_checked25317 : (cuts25317.take 2).map (fun c => (3322281985-1+2*2^9*c.k,103059639898024+c.lower,103060022005230+c.upper)) = pointBounds25317 := by
 decide +kernel
def cuts25318 : List PrefixCut := [⟨82,327523463,327523644⟩,
⟨128,514663943,514664227⟩]
theorem checked25318 : checkPrefixCuts (2^48) 3322413057 9 Manual.Count131072.C025318.packed 128 cuts25318 = true := by
 decide +kernel
def pointBounds25318 : List (Nat × Nat × Nat) := [(3322497024,103060476005785,103060858113462)]
theorem point_links_checked25318 : (cuts25318.take 1).map (fun c => (3322413057-1+2*2^9*c.k,103060148482322+c.lower,103060530589818+c.upper)) = pointBounds25318 := by
 decide +kernel
def cuts25319 : List PrefixCut := [⟨56,221023909,221024034⟩,
⟨128,510831461,510831746⟩]
theorem checked25319 : checkPrefixCuts (2^48) 3322544129 9 Manual.Count131072.C025319.packed 128 cuts25319 = true := by
 decide +kernel
def pointBounds25319 : List (Nat × Nat × Nat) := [(3322601472,103060884170174,103061266278079)]
theorem point_links_checked25319 : (cuts25319.take 1).map (fun c => (3322544129-1+2*2^9*c.k,103060663146265+c.lower,103061045254045+c.upper)) = pointBounds25319 := by
 decide +kernel
def cuts25320 : List PrefixCut := [⟨30,121732507,121732574⟩,
⟨128,515301033,515301318⟩]
theorem checked25320 : checkPrefixCuts (2^48) 3322675201 9 Manual.Count131072.C025320.packed 128 cuts25320 = true := by
 decide +kernel
def pointBounds25320 : List (Nat × Nat × Nat) := [(3322705920,103061295710233,103061677818365)]
theorem point_links_checked25320 : (cuts25320.take 1).map (fun c => (3322675201-1+2*2^9*c.k,103061173977726+c.lower,103061556085791+c.upper)) = pointBounds25320 := by
 decide +kernel
def cuts25321 : List PrefixCut := [⟨4,14824240,14824248⟩,
⟨106,415919209,415919443⟩,
⟨128,501642630,501642915⟩]
theorem checked25321 : checkPrefixCuts (2^48) 3322806273 9 Manual.Count131072.C025321.packed 128 cuts25321 = true := by
 decide +kernel
def pointBounds25321 : List (Nat × Nat × Nat) := [(3322810368,103061704102999,103062086211357),(3322914816,103062105197968,103062487306552)]
theorem point_links_checked25321 : (cuts25321.take 2).map (fun c => (3322806273-1+2*2^9*c.k,103061689278759+c.lower,103062071387109+c.upper)) = pointBounds25321 := by
 decide +kernel
def cuts25322 : List PrefixCut := [⟨80,312055446,312055623⟩,
⟨128,501622859,501623143⟩]
theorem checked25322 : checkPrefixCuts (2^48) 3322937345 9 Manual.Count131072.C025322.packed 128 cuts25322 = true := by
 decide +kernel
def pointBounds25322 : List (Nat × Nat × Nat) := [(3323019264,103062502976835,103062885085647)]
theorem point_links_checked25322 : (cuts25322.take 1).map (fun c => (3322937345-1+2*2^9*c.k,103062190921389+c.lower,103062573030024+c.upper)) = pointBounds25322 := by
 decide +kernel
def cuts25323 : List PrefixCut := [⟨54,211502417,211502544⟩,
⟨128,511428441,511428738⟩]
theorem checked25323 : checkPrefixCuts (2^48) 3323068417 9 Manual.Count131072.C025323.packed 128 cuts25323 = true := by
 decide +kernel
def pointBounds25323 : List (Nat × Nat × Nat) := [(3323123712,103062904046665,103063286155711)]
theorem point_links_checked25323 : (cuts25323.take 1).map (fun c => (3323068417-1+2*2^9*c.k,103062692544248+c.lower,103063074653167+c.upper)) = pointBounds25323 := by
 decide +kernel
def cuts25324 : List PrefixCut := [⟨28,110871781,110871839⟩,
⟨128,505140697,505140973⟩]
theorem checked25324 : checkPrefixCuts (2^48) 3323199489 9 Manual.Count131072.C025324.packed 128 cuts25324 = true := by
 decide +kernel
def pointBounds25324 : List (Nat × Nat × Nat) := [(3323228160,103063314844470,103063696953744)]
theorem point_links_checked25324 : (cuts25324.take 1).map (fun c => (3323199489-1+2*2^9*c.k,103063203972689+c.lower,103063586081905+c.upper)) = pointBounds25324 := by
 decide +kernel
def cuts25325 : List PrefixCut := [⟨2,8130874,8130879⟩,
⟨104,414498689,414498927⟩,
⟨128,506984100,506984387⟩]
theorem checked25325 : checkPrefixCuts (2^48) 3323330561 9 Manual.Count131072.C025325.packed 128 cuts25325 = true := by
 decide +kernel
def pointBounds25325 : List (Nat × Nat × Nat) := [(3323332608,103063717244260,103064099353757),(3323437056,103064123612075,103064505721805)]
theorem point_links_checked25325 : (cuts25325.take 2).map (fun c => (3323330561-1+2*2^9*c.k,103063709113386+c.lower,103064091222878+c.upper)) = pointBounds25325 := by
 decide +kernel
def cuts25326 : List PrefixCut := [⟨78,309380899,309381070⟩,
⟨128,502136706,502136992⟩]
theorem checked25326 : checkPrefixCuts (2^48) 3323461633 9 Manual.Count131072.C025326.packed 128 cuts25326 = true := by
 decide +kernel
def pointBounds25326 : List (Nat × Nat × Nat) := [(3323541504,103064525478385,103064907588335)]
theorem point_links_checked25326 : (cuts25326.take 1).map (fun c => (3323461633-1+2*2^9*c.k,103064216097486+c.lower,103064598207265+c.upper)) = pointBounds25326 := by
 decide +kernel
def cuts25327 : List PrefixCut := [⟨52,209097813,209097928⟩,
⟨128,509400044,509400333⟩]
theorem checked25327 : checkPrefixCuts (2^48) 3323592705 9 Manual.Count131072.C025327.packed 128 cuts25327 = true := by
 decide +kernel
def pointBounds25327 : List (Nat × Nat × Nat) := [(3323645952,103064927332005,103065309442185)]
theorem point_links_checked25327 : (cuts25327.take 1).map (fun c => (3323592705-1+2*2^9*c.k,103064718234192+c.lower,103065100344257+c.upper)) = pointBounds25327 := by
 decide +kernel
def cuts25328 : List PrefixCut := [⟨26,102470385,102470445⟩,
⟨128,505230332,505230618⟩]
theorem checked25328 : checkPrefixCuts (2^48) 3323723777 9 Manual.Count131072.C025328.packed 128 cuts25328 = true := by
 decide +kernel
def pointBounds25328 : List (Nat × Nat × Nat) := [(3323750400,103065330104621,103065712215035),(3323854848,103065732864568,103066114975208)]
theorem point_links_checked25328 : (cuts25328.take 2).map (fun c => (3323723777-1+2*2^9*c.k,103065227634236+c.lower,103065609744590+c.upper)) = pointBounds25328 := by
 decide +kernel
def cuts25329 : List PrefixCut := [⟨102,406557979,406558212⟩,
⟨128,507920261,507920552⟩]
theorem checked25329 : checkPrefixCuts (2^48) 3323854849 9 Manual.Count131072.C025329.packed 128 cuts25329 = true := by
 decide +kernel
def pointBounds25329 : List (Nat × Nat × Nat) := [(3323959296,103066139422547,103066521533420)]
theorem point_links_checked25329 : (cuts25329.take 1).map (fun c => (3323854849-1+2*2^9*c.k,103065732864568+c.lower,103066114975208+c.upper)) = pointBounds25329 := by
 decide +kernel
def cuts25330 : List PrefixCut := [⟨76,304590139,304590312⟩,
⟨128,508916372,508916657⟩]
theorem checked25330 : checkPrefixCuts (2^48) 3323985921 9 Manual.Count131072.C025330.packed 128 cuts25330 = true := by
 decide +kernel
def pointBounds25330 : List (Nat × Nat × Nat) := [(3324063744,103066545374968,103066927486072)]
theorem point_links_checked25330 : (cuts25330.take 1).map (fun c => (3323985921-1+2*2^9*c.k,103066240784829+c.lower,103066622895760+c.upper)) = pointBounds25330 := by
 decide +kernel
def cuts25331 : List PrefixCut := [⟨50,200173929,200174041⟩,
⟨128,505001317,505001598⟩]
theorem checked25331 : checkPrefixCuts (2^48) 3324116993 9 Manual.Count131072.C025331.packed 128 cuts25331 = true := by
 decide +kernel
def pointBounds25331 : List (Nat × Nat × Nat) := [(3324168192,103066949875130,103067331986458)]
theorem point_links_checked25331 : (cuts25331.take 1).map (fun c => (3324116993-1+2*2^9*c.k,103066749701201+c.lower,103067131812417+c.upper)) = pointBounds25331 := by
 decide +kernel
def cuts25332 : List PrefixCut := [⟨24,95680430,95680483⟩,
⟨126,498377070,498377344⟩,
⟨128,505828025,505828303⟩]
theorem checked25332 : checkPrefixCuts (2^48) 3324248065 9 Manual.Count131072.C025332.packed 128 cuts25332 = true := by
 decide +kernel
def pointBounds25332 : List (Nat × Nat × Nat) := [(3324272640,103067350382948,103067732494498),(3324377088,103067753079588,103068135191359)]
theorem point_links_checked25332 : (cuts25332.take 2).map (fun c => (3324248065-1+2*2^9*c.k,103067254702518+c.lower,103067636814015+c.upper)) = pointBounds25332 := by
 decide +kernel
def cuts25333 : List PrefixCut := [⟨100,396079753,396079974⟩,
⟨128,502844761,502845042⟩]
theorem checked25333 : checkPrefixCuts (2^48) 3324379137 9 Manual.Count131072.C025333.packed 128 cuts25333 = true := by
 decide +kernel
def pointBounds25333 : List (Nat × Nat × Nat) := [(3324481536,103068156610296,103068538722292)]
theorem point_links_checked25333 : (cuts25333.take 1).map (fun c => (3324379137-1+2*2^9*c.k,103067760530543+c.lower,103068142642318+c.upper)) = pointBounds25333 := by
 decide +kernel
def cuts25334 : List PrefixCut := [⟨74,293112314,293112483⟩,
⟨128,506804108,506804397⟩]
theorem checked25334 : checkPrefixCuts (2^48) 3324510209 9 Manual.Count131072.C025334.packed 128 cuts25334 = true := by
 decide +kernel
def pointBounds25334 : List (Nat × Nat × Nat) := [(3324585984,103068556487618,103068938599843)]
theorem point_links_checked25334 : (cuts25334.take 1).map (fun c => (3324510209-1+2*2^9*c.k,103068263375304+c.lower,103068645487360+c.upper)) = pointBounds25334 := by
 decide +kernel
def cuts25335 : List PrefixCut := [⟨48,189898247,189898357⟩,
⟨128,501027231,501027524⟩]
theorem checked25335 : checkPrefixCuts (2^48) 3324641281 9 Manual.Count131072.C025335.packed 128 cuts25335 = true := by
 decide +kernel
def pointBounds25335 : List (Nat × Nat × Nat) := [(3324690432,103068960077659,103069342190114)]
theorem point_links_checked25335 : (cuts25335.take 1).map (fun c => (3324641281-1+2*2^9*c.k,103068770179412+c.lower,103069152291757+c.upper)) = pointBounds25335 := by
 decide +kernel
def cuts25336 : List PrefixCut := [⟨22,86945419,86945471⟩,
⟨124,492033925,492034201⟩,
⟨128,507949368,507949654⟩]
theorem checked25336 : checkPrefixCuts (2^48) 3324772353 9 Manual.Count131072.C025336.packed 128 cuts25336 = true := by
 decide +kernel
def pointBounds25336 : List (Nat × Nat × Nat) := [(3324794880,103069358152062,103069740264752),(3324899328,103069763240568,103070145353482)]
theorem point_links_checked25336 : (cuts25336.take 2).map (fun c => (3324772353-1+2*2^9*c.k,103069271206643+c.lower,103069653319281+c.upper)) = pointBounds25336 := by
 decide +kernel
def cuts25337 : List PrefixCut := [⟨98,388398430,388398641⟩,
⟨128,506744188,506744469⟩]
theorem checked25337 : checkPrefixCuts (2^48) 3324903425 9 Manual.Count131072.C025337.packed 128 cuts25337 = true := by
 decide +kernel
def pointBounds25337 : List (Nat × Nat × Nat) := [(3325003776,103070167554441,103070549667576)]
theorem point_links_checked25337 : (cuts25337.take 1).map (fun c => (3324903425-1+2*2^9*c.k,103069779156011+c.lower,103070161268935+c.upper)) = pointBounds25337 := by
 decide +kernel
def cuts25338 : List PrefixCut := [⟨72,284685645,284685808⟩,
⟨128,505369812,505370094⟩]
theorem checked25338 : checkPrefixCuts (2^48) 3325034497 9 Manual.Count131072.C025338.packed 128 cuts25338 = true := by
 decide +kernel
def pointBounds25338 : List (Nat × Nat × Nat) := [(3325108224,103070570585844,103070952699212)]
theorem point_links_checked25338 : (cuts25338.take 1).map (fun c => (3325034497-1+2*2^9*c.k,103070285900199+c.lower,103070668013404+c.upper)) = pointBounds25338 := by
 decide +kernel
def cuts25339 : List PrefixCut := [⟨46,179710446,179710547⟩,
⟨128,506111684,506111970⟩]
theorem checked25339 : checkPrefixCuts (2^48) 3325165569 9 Manual.Count131072.C025339.packed 128 cuts25339 = true := by
 decide +kernel
def pointBounds25339 : List (Nat × Nat × Nat) := [(3325212672,103070970980457,103071353094045)]
theorem point_links_checked25339 : (cuts25339.take 1).map (fun c => (3325165569-1+2*2^9*c.k,103070791270011+c.lower,103071173383498+c.upper)) = pointBounds25339 := by
 decide +kernel
def cuts25340 : List PrefixCut := [⟨20,79652162,79652204⟩,
⟨122,487470329,487470592⟩,
⟨128,508715797,508716072⟩]
theorem checked25340 : checkPrefixCuts (2^48) 3325296641 9 Manual.Count131072.C025340.packed 128 cuts25340 = true := by
 decide +kernel
def pointBounds25340 : List (Nat × Nat × Nat) := [(3325317120,103071377033857,103071759147672),(3325421568,103071784852024,103072166966060)]
theorem point_links_checked25340 : (cuts25340.take 2).map (fun c => (3325296641-1+2*2^9*c.k,103071297381695+c.lower,103071679495468+c.upper)) = pointBounds25340 := by
 decide +kernel
def cuts25341 : List PrefixCut := [⟨96,378942051,378942265⟩,
⟨128,509372753,509373042⟩]
theorem checked25341 : checkPrefixCuts (2^48) 3325427713 9 Manual.Count131072.C025341.packed 128 cuts25341 = true := by
 decide +kernel
def pointBounds25341 : List (Nat × Nat × Nat) := [(3325526016,103072185039543,103072567153805)]
theorem point_links_checked25341 : (cuts25341.take 1).map (fun c => (3325427713-1+2*2^9*c.k,103071806097492+c.lower,103072188211540+c.upper)) = pointBounds25341 := by
 decide +kernel
def cuts25342 : List PrefixCut := [⟨70,278377570,278377721⟩,
⟨128,508929558,508929841⟩]
theorem checked25342 : checkPrefixCuts (2^48) 3325558785 9 Manual.Count131072.C025342.packed 128 cuts25342 = true := by
 decide +kernel
def pointBounds25342 : List (Nat × Nat × Nat) := [(3325630464,103072593847815,103072975962303)]
theorem point_links_checked25342 : (cuts25342.take 1).map (fun c => (3325558785-1+2*2^9*c.k,103072315470245+c.lower,103072697584582+c.upper)) = pointBounds25342 := by
 decide +kernel
def cuts25343 : List PrefixCut := [⟨44,176381353,176381448⟩,
⟨128,506455172,506455451⟩]
theorem checked25343 : checkPrefixCuts (2^48) 3325689857 9 Manual.Count131072.C025343.packed 128 cuts25343 = true := by
 decide +kernel
def pointBounds25343 : List (Nat × Nat × Nat) := [(3325734912,103073000781156,103073382895871)]
theorem point_links_checked25343 : (cuts25343.take 1).map (fun c => (3325689857-1+2*2^9*c.k,103072824399803+c.lower,103073206514423+c.upper)) = pointBounds25343 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000166
