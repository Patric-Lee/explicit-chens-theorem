import PlattAssemblyKernel
import PlattCertificates.Count131072.C025184
import PlattCertificates.Count131072.C025185
import PlattCertificates.Count131072.C025186
import PlattCertificates.Count131072.C025187
import PlattCertificates.Count131072.C025188
import PlattCertificates.Count131072.C025189
import PlattCertificates.Count131072.C025190
import PlattCertificates.Count131072.C025191
import PlattCertificates.Count131072.C025192
import PlattCertificates.Count131072.C025193
import PlattCertificates.Count131072.C025194
import PlattCertificates.Count131072.C025195
import PlattCertificates.Count131072.C025196
import PlattCertificates.Count131072.C025197
import PlattCertificates.Count131072.C025198
import PlattCertificates.Count131072.C025199
import PlattCertificates.Count131072.C025200
import PlattCertificates.Count131072.C025201
import PlattCertificates.Count131072.C025202
import PlattCertificates.Count131072.C025203
import PlattCertificates.Count131072.C025204
import PlattCertificates.Count131072.C025205
import PlattCertificates.Count131072.C025206
import PlattCertificates.Count131072.C025207
import PlattCertificates.Count131072.C025208
import PlattCertificates.Count131072.C025209
import PlattCertificates.Count131072.C025210
import PlattCertificates.Count131072.C025211
import PlattCertificates.Count131072.C025212
import PlattCertificates.Count131072.C025213
import PlattCertificates.Count131072.C025214
import PlattCertificates.Count131072.C025215
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000162
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25184 : List PrefixCut := [⟨42,165399576,165399674⟩,
⟨128,507519518,507519811⟩]
theorem checked25184 : checkPrefixCuts (2^48) 3304849409 9 Manual.Count131072.C025184.packed 128 cuts25184 = true := by
 decide +kernel
def pointBounds25184 : List (Nat × Nat × Nat) := [(3304892416,102992246786225,102992628855657)]
theorem point_links_checked25184 : (cuts25184.take 1).map (fun c => (3304849409-1+2*2^9*c.k,102992081386649+c.lower,102992463455983+c.upper)) = pointBounds25184 := by
 decide +kernel
def cuts25185 : List PrefixCut := [⟨15,57657848,57657879⟩,
⟨116,457848848,457849106⟩,
⟨128,506051483,506051768⟩]
theorem checked25185 : checkPrefixCuts (2^48) 3304980481 9 Manual.Count131072.C025185.packed 128 cuts25185 = true := by
 decide +kernel
def pointBounds25185 : List (Nat × Nat × Nat) := [(3304995840,102992646564015,102993028633673),(3305099264,102993046755015,102993428824900)]
theorem point_links_checked25185 : (cuts25185.take 2).map (fun c => (3304980481-1+2*2^9*c.k,102992588906167+c.lower,102992970975794+c.upper)) = pointBounds25185 := by
 decide +kernel
def cuts25186 : List PrefixCut := [⟨89,348399064,348399261⟩,
⟨128,499133407,499133691⟩]
theorem checked25186 : checkPrefixCuts (2^48) 3305111553 9 Manual.Count131072.C025186.packed 128 cuts25186 = true := by
 decide +kernel
def pointBounds25186 : List (Nat × Nat × Nat) := [(3305202688,102993443356714,102993825426823)]
theorem point_links_checked25186 : (cuts25186.take 1).map (fun c => (3305111553-1+2*2^9*c.k,102993094957650+c.lower,102993477027562+c.upper)) = pointBounds25186 := by
 decide +kernel
def cuts25187 : List PrefixCut := [⟨62,248324527,248324660⟩,
⟨128,518955438,518955718⟩]
theorem checked25187 : checkPrefixCuts (2^48) 3305242625 9 Manual.Count131072.C025187.packed 128 cuts25187 = true := by
 decide +kernel
def pointBounds25187 : List (Nat × Nat × Nat) := [(3305306112,102993842415584,102994224485913)]
theorem point_links_checked25187 : (cuts25187.take 1).map (fun c => (3305242625-1+2*2^9*c.k,102993594091057+c.lower,102993976161253+c.upper)) = pointBounds25187 := by
 decide +kernel
def cuts25188 : List PrefixCut := [⟨35,137527404,137527480⟩,
⟨128,506417145,506417427⟩]
theorem checked25188 : checkPrefixCuts (2^48) 3305373697 9 Manual.Count131072.C025188.packed 128 cuts25188 = true := by
 decide +kernel
def pointBounds25188 : List (Nat × Nat × Nat) := [(3305409536,102994250573899,102994632644451)]
theorem point_links_checked25188 : (cuts25188.take 1).map (fun c => (3305373697-1+2*2^9*c.k,102994113046495+c.lower,102994495116971+c.upper)) = pointBounds25188 := by
 decide +kernel
def cuts25189 : List PrefixCut := [⟨8,31762174,31762191⟩,
⟨109,433508531,433508769⟩,
⟨128,510654663,510654941⟩]
theorem checked25189 : checkPrefixCuts (2^48) 3305504769 9 Manual.Count131072.C025189.packed 128 cuts25189 = true := by
 decide +kernel
def pointBounds25189 : List (Nat × Nat × Nat) := [(3305512960,102994651225814,102995033296589),(3305616384,102995052972171,102995435043167)]
theorem point_links_checked25189 : (cuts25189.take 2).map (fun c => (3305504769-1+2*2^9*c.k,102994619463640+c.lower,102995001534398+c.upper)) = pointBounds25189 := by
 decide +kernel
def cuts25190 : List PrefixCut := [⟨82,319223345,319223522⟩,
⟨128,503311657,503311936⟩]
theorem checked25190 : checkPrefixCuts (2^48) 3305635841 9 Manual.Count131072.C025190.packed 128 cuts25190 = true := by
 decide +kernel
def pointBounds25190 : List (Nat × Nat × Nat) := [(3305719808,102995449341648,102995831412861)]
theorem point_links_checked25190 : (cuts25190.take 1).map (fun c => (3305635841-1+2*2^9*c.k,102995130118303+c.lower,102995512189339+c.upper)) = pointBounds25190 := by
 decide +kernel
def cuts25191 : List PrefixCut := [⟨55,221890243,221890363⟩,
⟨128,514020075,514020358⟩]
theorem checked25191 : checkPrefixCuts (2^48) 3305766913 9 Manual.Count131072.C025191.packed 128 cuts25191 = true := by
 decide +kernel
def pointBounds25191 : List (Nat × Nat × Nat) := [(3305823232,102995855320203,102996237391638)]
theorem point_links_checked25191 : (cuts25191.take 1).map (fun c => (3305766913-1+2*2^9*c.k,102995633429960+c.lower,102996015501275+c.upper)) = pointBounds25191 := by
 decide +kernel
def cuts25192 : List PrefixCut := [⟨28,115283465,115283527⟩,
⟨128,510338597,510338880⟩]
theorem checked25192 : checkPrefixCuts (2^48) 3305897985 9 Manual.Count131072.C025192.packed 128 cuts25192 = true := by
 decide +kernel
def pointBounds25192 : List (Nat × Nat × Nat) := [(3305926656,102996262733500,102996644805160)]
theorem point_links_checked25192 : (cuts25192.take 1).map (fun c => (3305897985-1+2*2^9*c.k,102996147450035+c.lower,102996529521633+c.upper)) = pointBounds25192 := by
 decide +kernel
def cuts25193 : List PrefixCut := [⟨1,4427273,4427275⟩,
⟨102,403726896,403727123⟩,
⟨128,503592413,503592695⟩]
theorem checked25193 : checkPrefixCuts (2^48) 3306029057 9 Manual.Count131072.C025193.packed 128 cuts25193 = true := by
 decide +kernel
def pointBounds25193 : List (Nat × Nat × Nat) := [(3306030080,102996662215905,102997044287788),(3306133504,102997061515528,102997443587636)]
theorem point_links_checked25193 : (cuts25193.take 2).map (fun c => (3306029057-1+2*2^9*c.k,102996657788632+c.lower,102997039860513+c.upper)) = pointBounds25193 := by
 decide +kernel
def cuts25194 : List PrefixCut := [⟨75,299336472,299336637⟩,
⟨128,510553492,510553774⟩]
theorem checked25194 : checkPrefixCuts (2^48) 3306160129 9 Manual.Count131072.C025194.packed 128 cuts25194 = true := by
 decide +kernel
def pointBounds25194 : List (Nat × Nat × Nat) := [(3306236928,102997460717517,102997842789845)]
theorem point_links_checked25194 : (cuts25194.take 1).map (fun c => (3306160129-1+2*2^9*c.k,102997161381045+c.lower,102997543453208+c.upper)) = pointBounds25194 := by
 decide +kernel
def cuts25195 : List PrefixCut := [⟨48,191377823,191377935⟩,
⟨128,511725041,511725332⟩]
theorem checked25195 : checkPrefixCuts (2^48) 3306291201 9 Manual.Count131072.C025195.packed 128 cuts25195 = true := by
 decide +kernel
def pointBounds25195 : List (Nat × Nat × Nat) := [(3306340352,102997863312360,102998245384917)]
theorem point_links_checked25195 : (cuts25195.take 1).map (fun c => (3306291201-1+2*2^9*c.k,102997671934537+c.lower,102998054006982+c.upper)) = pointBounds25195 := by
 decide +kernel
def cuts25196 : List PrefixCut := [⟨21,87342831,87342881⟩,
⟨122,495956621,495956907⟩,
⟨128,517834120,517834419⟩]
theorem checked25196 : checkPrefixCuts (2^48) 3306422273 9 Manual.Count131072.C025196.packed 128 cuts25196 = true := by
 decide +kernel
def pointBounds25196 : List (Nat × Nat × Nat) := [(3306443776,102998271002409,102998653075195),(3306547200,102998679616199,102999061689221)]
theorem point_links_checked25196 : (cuts25196.take 2).map (fun c => (3306422273-1+2*2^9*c.k,102998183659578+c.lower,102998565732314+c.upper)) = pointBounds25196 := by
 decide +kernel
def cuts25197 : List PrefixCut := [⟨95,372848006,372848213⟩,
⟨128,506151314,506151596⟩]
theorem checked25197 : checkPrefixCuts (2^48) 3306553345 9 Manual.Count131072.C025197.packed 128 cuts25197 = true := by
 decide +kernel
def pointBounds25197 : List (Nat × Nat × Nat) := [(3306650624,102999074341704,102999456414946)]
theorem point_links_checked25197 : (cuts25197.take 1).map (fun c => (3306553345-1+2*2^9*c.k,102998701493698+c.lower,102999083566733+c.upper)) = pointBounds25197 := by
 decide +kernel
def cuts25198 : List PrefixCut := [⟨68,271794844,271794995⟩,
⟨128,509536162,509536445⟩]
theorem checked25198 : checkPrefixCuts (2^48) 3306684417 9 Manual.Count131072.C025198.packed 128 cuts25198 = true := by
 decide +kernel
def pointBounds25198 : List (Nat × Nat × Nat) := [(3306754048,102999479439856,102999861513324)]
theorem point_links_checked25198 : (cuts25198.take 1).map (fun c => (3306684417-1+2*2^9*c.k,102999207645012+c.lower,102999589718329+c.upper)) = pointBounds25198 := by
 decide +kernel
def cuts25199 : List PrefixCut := [⟨41,160789954,160790044⟩,
⟨128,508239171,508239462⟩]
theorem checked25199 : checkPrefixCuts (2^48) 3306815489 9 Manual.Count131072.C025199.packed 128 cuts25199 = true := by
 decide +kernel
def pointBounds25199 : List (Nat × Nat × Nat) := [(3306857472,102999877971128,103000260044818)]
theorem point_links_checked25199 : (cuts25199.take 1).map (fun c => (3306815489-1+2*2^9*c.k,102999717181174+c.lower,103000099254774+c.upper)) = pointBounds25199 := by
 decide +kernel
def cuts25200 : List PrefixCut := [⟨14,57793812,57793844⟩,
⟨115,458428012,458428265⟩,
⟨128,509155388,509155667⟩]
theorem checked25200 : checkPrefixCuts (2^48) 3306946561 9 Manual.Count131072.C025200.packed 128 cuts25200 = true := by
 decide +kernel
def pointBounds25200 : List (Nat × Nat × Nat) := [(3306960896,103000283214157,103000665288080),(3307064320,103000683848357,103001065922501)]
theorem point_links_checked25200 : (cuts25200.take 2).map (fun c => (3306946561-1+2*2^9*c.k,103000225420345+c.lower,103000607494236+c.upper)) = pointBounds25200 := by
 decide +kernel
def cuts25201 : List PrefixCut := [⟨88,357554376,357554573⟩,
⟨128,515007949,515008234⟩]
theorem checked25201 : checkPrefixCuts (2^48) 3307077633 9 Manual.Count131072.C025201.packed 128 cuts25201 = true := by
 decide +kernel
def pointBounds25201 : List (Nat × Nat × Nat) := [(3307167744,103001092130109,103001474204476)]
theorem point_links_checked25201 : (cuts25201.take 1).map (fun c => (3307077633-1+2*2^9*c.k,103000734575733+c.lower,103001116649903+c.upper)) = pointBounds25201 := by
 decide +kernel
def cuts25202 : List PrefixCut := [⟨61,245113057,245113194⟩,
⟨128,512434194,512434477⟩]
theorem checked25202 : checkPrefixCuts (2^48) 3307208705 9 Manual.Count131072.C025202.packed 128 cuts25202 = true := by
 decide +kernel
def pointBounds25202 : List (Nat × Nat × Nat) := [(3307271168,103001494696739,103001876771331)]
theorem point_links_checked25202 : (cuts25202.take 1).map (fun c => (3307208705-1+2*2^9*c.k,103001249583682+c.lower,103001631658137+c.upper)) = pointBounds25202 := by
 decide +kernel
def cuts25203 : List PrefixCut := [⟨34,133020195,133020273⟩,
⟨128,511052190,511052483⟩]
theorem checked25203 : checkPrefixCuts (2^48) 3307339777 9 Manual.Count131072.C025203.packed 128 cuts25203 = true := by
 decide +kernel
def pointBounds25203 : List (Nat × Nat × Nat) := [(3307374592,103001895038071,103002277112887)]
theorem point_links_checked25203 : (cuts25203.take 1).map (fun c => (3307339777-1+2*2^9*c.k,103001762017876+c.lower,103002144092614+c.upper)) = pointBounds25203 := by
 decide +kernel
def cuts25204 : List PrefixCut := [⟨7,27317956,27317971⟩,
⟨108,426953366,426953599⟩,
⟨128,504138743,504139020⟩]
theorem checked25204 : checkPrefixCuts (2^48) 3307470849 9 Manual.Count131072.C025204.packed 128 cuts25204 = true := by
 decide +kernel
def pointBounds25204 : List (Nat × Nat × Nat) := [(3307478016,103002300388022,103002682463068),(3307581440,103002700023432,103003082098696)]
theorem point_links_checked25204 : (cuts25204.take 2).map (fun c => (3307470849-1+2*2^9*c.k,103002273070066+c.lower,103002655145097+c.upper)) = pointBounds25204 := by
 decide +kernel
def cuts25205 : List PrefixCut := [⟨81,322863050,322863226⟩,
⟨128,512117970,512118253⟩]
theorem checked25205 : checkPrefixCuts (2^48) 3307601921 9 Manual.Count131072.C025205.packed 128 cuts25205 = true := by
 decide +kernel
def pointBounds25205 : List (Nat × Nat × Nat) := [(3307684864,103003100071859,103003482147343)]
theorem point_links_checked25205 : (cuts25205.take 1).map (fun c => (3307601921-1+2*2^9*c.k,103002777208809+c.lower,103003159284117+c.upper)) = pointBounds25205 := by
 decide +kernel
def cuts25206 : List PrefixCut := [⟨54,213248826,213248943⟩,
⟨128,506396340,506396624⟩]
theorem checked25206 : checkPrefixCuts (2^48) 3307732993 9 Manual.Count131072.C025206.packed 128 cuts25206 = true := by
 decide +kernel
def pointBounds25206 : List (Nat × Nat × Nat) := [(3307788288,103003502575605,103003884651313)]
theorem point_links_checked25206 : (cuts25206.take 1).map (fun c => (3307732993-1+2*2^9*c.k,103003289326779+c.lower,103003671402370+c.upper)) = pointBounds25206 := by
 decide +kernel
def cuts25207 : List PrefixCut := [⟨27,107556645,107556704⟩,
⟨128,510971151,510971436⟩]
theorem checked25207 : checkPrefixCuts (2^48) 3307864065 9 Manual.Count131072.C025207.packed 128 cuts25207 = true := by
 decide +kernel
def pointBounds25207 : List (Nat × Nat × Nat) := [(3307891712,103003903279764,103004285355698),(3307995136,103004306694270,103004688770430)]
theorem point_links_checked25207 : (cuts25207.take 2).map (fun c => (3307864065-1+2*2^9*c.k,103003795723119+c.lower,103004177798994+c.upper)) = pointBounds25207 := by
 decide +kernel
def cuts25208 : List PrefixCut := [⟨101,402380867,402381095⟩,
⟨128,512227223,512227513⟩]
theorem checked25208 : checkPrefixCuts (2^48) 3307995137 9 Manual.Count131072.C025208.packed 128 cuts25208 = true := by
 decide +kernel
def pointBounds25208 : List (Nat × Nat × Nat) := [(3308098560,103004709075137,103005091151525)]
theorem point_links_checked25208 : (cuts25208.take 1).map (fun c => (3307995137-1+2*2^9*c.k,103004306694270+c.lower,103004688770430+c.upper)) = pointBounds25208 := by
 decide +kernel
def cuts25209 : List PrefixCut := [⟨74,289799222,289799384⟩,
⟨128,500975787,500976067⟩]
theorem checked25209 : checkPrefixCuts (2^48) 3308126209 9 Manual.Count131072.C025209.packed 128 cuts25209 = true := by
 decide +kernel
def pointBounds25209 : List (Nat × Nat × Nat) := [(3308201984,103005108720715,103005490797327)]
theorem point_links_checked25209 : (cuts25209.take 1).map (fun c => (3308126209-1+2*2^9*c.k,103004818921493+c.lower,103005200997943+c.upper)) = pointBounds25209 := by
 decide +kernel
def cuts25210 : List PrefixCut := [⟨47,186839879,186839984⟩,
⟨128,510825403,510825687⟩]
theorem checked25210 : checkPrefixCuts (2^48) 3308257281 9 Manual.Count131072.C025210.packed 128 cuts25210 = true := by
 decide +kernel
def pointBounds25210 : List (Nat × Nat × Nat) := [(3308305408,103005506737159,103005888813994)]
theorem point_links_checked25210 : (cuts25210.take 1).map (fun c => (3308257281-1+2*2^9*c.k,103005319897280+c.lower,103005701974010+c.upper)) = pointBounds25210 := by
 decide +kernel
def cuts25211 : List PrefixCut := [⟨20,78612899,78612943⟩,
⟨121,477370186,477370452⟩,
⟨128,504339239,504339521⟩]
theorem checked25211 : checkPrefixCuts (2^48) 3308388353 9 Manual.Count131072.C025211.packed 128 cuts25211 = true := by
 decide +kernel
def pointBounds25211 : List (Nat × Nat × Nat) := [(3308408832,103005909335582,103006291412640),(3308512256,103006308092869,103006690170149)]
theorem point_links_checked25211 : (cuts25211.take 2).map (fun c => (3308388353-1+2*2^9*c.k,103005830722683+c.lower,103006212799697+c.upper)) = pointBounds25211 := by
 decide +kernel
def cuts25212 : List PrefixCut := [⟨94,376114618,376114828⟩,
⟨128,511465547,511465833⟩]
theorem checked25212 : checkPrefixCuts (2^48) 3308519425 9 Manual.Count131072.C025212.packed 128 cuts25212 = true := by
 decide +kernel
def pointBounds25212 : List (Nat × Nat × Nat) := [(3308615680,103006711176540,103007093254046)]
theorem point_links_checked25212 : (cuts25212.take 1).map (fun c => (3308519425-1+2*2^9*c.k,103006335061922+c.lower,103006717139218+c.upper)) = pointBounds25212 := by
 decide +kernel
def cuts25213 : List PrefixCut := [⟨67,265848573,265848719⟩,
⟨128,505235141,505235421⟩]
theorem checked25213 : checkPrefixCuts (2^48) 3308650497 9 Manual.Count131072.C025213.packed 128 cuts25213 = true := by
 decide +kernel
def pointBounds25213 : List (Nat × Nat × Nat) := [(3308719104,103007112376042,103007494453770)]
theorem point_links_checked25213 : (cuts25213.take 1).map (fun c => (3308650497-1+2*2^9*c.k,103006846527469+c.lower,103007228605051+c.upper)) = pointBounds25213 := by
 decide +kernel
def cuts25214 : List PrefixCut := [⟨40,155930583,155930674⟩,
⟨128,505640361,505640650⟩]
theorem checked25214 : checkPrefixCuts (2^48) 3308781569 9 Manual.Count131072.C025214.packed 128 cuts25214 = true := by
 decide +kernel
def pointBounds25214 : List (Nat × Nat × Nat) := [(3308822528,103007507693193,103007889771146)]
theorem point_links_checked25214 : (cuts25214.take 1).map (fun c => (3308781569-1+2*2^9*c.k,103007351762610+c.lower,103007733840472+c.upper)) = pointBounds25214 := by
 decide +kernel
def cuts25215 : List PrefixCut := [⟨13,52230219,52230251⟩,
⟨114,450499875,450500129⟩,
⟨128,506470994,506471280⟩]
theorem checked25215 : checkPrefixCuts (2^48) 3308912641 9 Manual.Count131072.C025215.packed 128 cuts25215 = true := by
 decide +kernel
def pointBounds25215 : List (Nat × Nat × Nat) := [(3308925952,103007909633190,103008291711373),(3309029376,103008307902846,103008689981251)]
theorem point_links_checked25215 : (cuts25215.take 2).map (fun c => (3308912641-1+2*2^9*c.k,103007857402971+c.lower,103008239481122+c.upper)) = pointBounds25215 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000162
