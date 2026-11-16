import PlattAssemblyKernel
import PlattCertificates.Count131072.C022208
import PlattCertificates.Count131072.C022209
import PlattCertificates.Count131072.C022210
import PlattCertificates.Count131072.C022211
import PlattCertificates.Count131072.C022212
import PlattCertificates.Count131072.C022213
import PlattCertificates.Count131072.C022214
import PlattCertificates.Count131072.C022215
import PlattCertificates.Count131072.C022216
import PlattCertificates.Count131072.C022217
import PlattCertificates.Count131072.C022218
import PlattCertificates.Count131072.C022219
import PlattCertificates.Count131072.C022220
import PlattCertificates.Count131072.C022221
import PlattCertificates.Count131072.C022222
import PlattCertificates.Count131072.C022223
import PlattCertificates.Count131072.C022224
import PlattCertificates.Count131072.C022225
import PlattCertificates.Count131072.C022226
import PlattCertificates.Count131072.C022227
import PlattCertificates.Count131072.C022228
import PlattCertificates.Count131072.C022229
import PlattCertificates.Count131072.C022230
import PlattCertificates.Count131072.C022231
import PlattCertificates.Count131072.C022232
import PlattCertificates.Count131072.C022233
import PlattCertificates.Count131072.C022234
import PlattCertificates.Count131072.C022235
import PlattCertificates.Count131072.C022236
import PlattCertificates.Count131072.C022237
import PlattCertificates.Count131072.C022238
import PlattCertificates.Count131072.C022239
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000069
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22208 : List PrefixCut := [⟨32,143402943,143403023⟩,
⟨121,557283016,557283324⟩,
⟨128,586252199,586252524⟩]
theorem checked22208 : checkPrefixCuts (2^48) 2914779137 9 Manual.Count131072.C022208.packed 128 cuts22208 = true := by
 decide +kernel
def pointBounds22208 : List (Nat × Nat × Nat) := [(2914811904,101374801849513,101375183003279),(2914903040,101375215729586,101375596883580)]
theorem point_links_checked22208 : (cuts22208.take 2).map (fun c => (2914779137-1+2*2^9*c.k,101374658446570+c.lower,101375039600256+c.upper)) = pointBounds22208 := by
 decide +kernel
def cuts22209 : List PrefixCut := [⟨82,372924162,372924384⟩,
⟨128,579563116,579563458⟩]
theorem checked22209 : checkPrefixCuts (2^48) 2914910209 9 Manual.Count131072.C022209.packed 128 cuts22209 = true := by
 decide +kernel
def pointBounds22209 : List (Nat × Nat × Nat) := [(2914994176,101375617622931,101375998777164)]
theorem point_links_checked22209 : (cuts22209.take 1).map (fun c => (2914910209-1+2*2^9*c.k,101375244698769+c.lower,101375625852780+c.upper)) = pointBounds22209 := by
 decide +kernel
def cuts22210 : List PrefixCut := [⟨43,198814497,198814613⟩,
⟨128,581854438,581854777⟩]
theorem checked22210 : checkPrefixCuts (2^48) 2915041281 9 Manual.Count131072.C022210.packed 128 cuts22210 = true := by
 decide +kernel
def pointBounds22210 : List (Nat × Nat × Nat) := [(2915085312,101376023076382,101376404230851)]
theorem point_links_checked22210 : (cuts22210.take 1).map (fun c => (2915041281-1+2*2^9*c.k,101375824261885+c.lower,101376205416238+c.upper)) = pointBounds22210 := by
 decide +kernel
def cuts22211 : List PrefixCut := [⟨4,18635130,18635141⟩,
⟨93,413152730,413152968⟩,
⟨128,579221136,579221465⟩]
theorem checked22211 : checkPrefixCuts (2^48) 2915172353 9 Manual.Count131072.C022211.packed 128 cuts22211 = true := by
 decide +kernel
def pointBounds22211 : List (Nat × Nat × Nat) := [(2915176448,101376424751453,101376805906156),(2915267584,101376819269053,101377200423983)]
theorem point_links_checked22211 : (cuts22211.take 2).map (fun c => (2915172353-1+2*2^9*c.k,101376406116323+c.lower,101376787271015+c.upper)) = pointBounds22211 := by
 decide +kernel
def cuts22212 : List PrefixCut := [⟨54,246298781,246298918⟩,
⟨128,582574499,582574832⟩]
theorem checked22212 : checkPrefixCuts (2^48) 2915303425 9 Manual.Count131072.C022212.packed 128 cuts22212 = true := by
 decide +kernel
def pointBounds22212 : List (Nat × Nat × Nat) := [(2915358720,101377231636240,101377612791398)]
theorem point_links_checked22212 : (cuts22212.take 1).map (fun c => (2915303425-1+2*2^9*c.k,101376985337459+c.lower,101377366492480+c.upper)) = pointBounds22212 := by
 decide +kernel
def cuts22213 : List PrefixCut := [⟨15,67968531,67968569⟩,
⟨104,462931854,462932116⟩,
⟨128,572121460,572121784⟩]
theorem checked22213 : checkPrefixCuts (2^48) 2915434497 9 Manual.Count131072.C022213.packed 128 cuts22213 = true := by
 decide +kernel
def pointBounds22213 : List (Nat × Nat × Nat) := [(2915449856,101377635880489,101378017035881),(2915540992,101378030843812,101378411999428)]
theorem point_links_checked22213 : (cuts22213.take 2).map (fun c => (2915434497-1+2*2^9*c.k,101377567911958+c.lower,101377949067312+c.upper)) = pointBounds22213 := by
 decide +kernel
def cuts22214 : List PrefixCut := [⟨65,294063972,294064140⟩,
⟨128,574509342,574509669⟩]
theorem checked22214 : checkPrefixCuts (2^48) 2915565569 9 Manual.Count131072.C022214.packed 128 cuts22214 = true := by
 decide +kernel
def pointBounds22214 : List (Nat × Nat × Nat) := [(2915632128,101378434097390,101378815253236)]
theorem point_links_checked22214 : (cuts22214.take 1).map (fun c => (2915565569-1+2*2^9*c.k,101378140033418+c.lower,101378521189096+c.upper)) = pointBounds22214 := by
 decide +kernel
def cuts22215 : List PrefixCut := [⟨26,118354789,118354856⟩,
⟨115,521486641,521486946⟩,
⟨128,579889507,579889846⟩]
theorem checked22215 : checkPrefixCuts (2^48) 2915696641 9 Manual.Count131072.C022215.packed 128 cuts22215 = true := by
 decide +kernel
def pointBounds22215 : List (Nat × Nat × Nat) := [(2915723264,101378832897549,101379214053621),(2915814400,101379236029401,101379617185711)]
theorem point_links_checked22215 : (cuts22215.take 2).map (fun c => (2915696641-1+2*2^9*c.k,101378714542760+c.lower,101379095698765+c.upper)) = pointBounds22215 := by
 decide +kernel
def cuts22216 : List PrefixCut := [⟨76,354659120,354659323⟩,
⟨128,587296379,587296719⟩]
theorem checked22216 : checkPrefixCuts (2^48) 2915827713 9 Manual.Count131072.C022216.packed 128 cuts22216 = true := by
 decide +kernel
def pointBounds22216 : List (Nat × Nat × Nat) := [(2915905536,101379649091387,101380030247934)]
theorem point_links_checked22216 : (cuts22216.take 1).map (fun c => (2915827713-1+2*2^9*c.k,101379294432267+c.lower,101379675588611+c.upper)) = pointBounds22216 := by
 decide +kernel
def cuts22217 : List PrefixCut := [⟨37,173558206,173558304⟩,
⟨126,570667633,570667962⟩,
⟨128,580609688,580610022⟩]
theorem checked22217 : checkPrefixCuts (2^48) 2915958785 9 Manual.Count131072.C022217.packed 128 cuts22217 = true := by
 decide +kernel
def pointBounds22217 : List (Nat × Nat × Nat) := [(2915996672,101380055286852,101380436443634),(2916087808,101380452396279,101380833553292)]
theorem point_links_checked22217 : (cuts22217.take 2).map (fun c => (2915958785-1+2*2^9*c.k,101379881728646+c.lower,101380262885330+c.upper)) = pointBounds22217 := by
 decide +kernel
def cuts22218 : List PrefixCut := [⟨87,401633403,401633631⟩,
⟨128,593131335,593131668⟩]
theorem checked22218 : checkPrefixCuts (2^48) 2916089857 9 Manual.Count131072.C022218.packed 128 cuts22218 = true := by
 decide +kernel
def pointBounds22218 : List (Nat × Nat × Nat) := [(2916178944,101380863971737,101381245128983)]
theorem point_links_checked22218 : (cuts22218.take 1).map (fun c => (2916089857-1+2*2^9*c.k,101380462338334+c.lower,101380843495352+c.upper)) = pointBounds22218 := by
 decide +kernel
def cuts22219 : List PrefixCut := [⟨48,214177011,214177130⟩,
⟨128,573801018,573801339⟩]
theorem checked22219 : checkPrefixCuts (2^48) 2916220929 9 Manual.Count131072.C022219.packed 128 cuts22219 = true := by
 decide +kernel
def pointBounds22219 : List (Nat × Nat × Nat) := [(2916270080,101381269646680,101381650804150)]
theorem point_links_checked22219 : (cuts22219.take 1).map (fun c => (2916220929-1+2*2^9*c.k,101381055469669+c.lower,101381436627020+c.upper)) = pointBounds22219 := by
 decide +kernel
def cuts22220 : List PrefixCut := [⟨9,41887917,41887942⟩,
⟨98,446861866,446862125⟩,
⟨128,586901159,586901499⟩]
theorem checked22220 : checkPrefixCuts (2^48) 2916352001 9 Manual.Count131072.C022220.packed 128 cuts22220 = true := by
 decide +kernel
def pointBounds22220 : List (Nat × Nat × Nat) := [(2916361216,101381671158604,101382052316301),(2916452352,101382076132553,101382457290484)]
theorem point_links_checked22220 : (cuts22220.take 2).map (fun c => (2916352001-1+2*2^9*c.k,101381629270687+c.lower,101382010428359+c.upper)) = pointBounds22220 := by
 decide +kernel
def cuts22221 : List PrefixCut := [⟨60,268492885,268493042⟩,
⟨128,570275182,570275511⟩]
theorem checked22221 : checkPrefixCuts (2^48) 2916483073 9 Manual.Count131072.C022221.packed 128 cuts22221 = true := by
 decide +kernel
def pointBounds22221 : List (Nat × Nat × Nat) := [(2916544512,101382484664731,101382865822900)]
theorem point_links_checked22221 : (cuts22221.take 1).map (fun c => (2916483073-1+2*2^9*c.k,101382216171846+c.lower,101382597329858+c.upper)) = pointBounds22221 := by
 decide +kernel
def cuts22222 : List PrefixCut := [⟨22,103841583,103841641⟩,
⟨112,510900250,510900538⟩,
⟨128,583374266,583374595⟩]
theorem checked22222 : checkPrefixCuts (2^48) 2916614145 9 Manual.Count131072.C022222.packed 128 cuts22222 = true := by
 decide +kernel
def pointBounds22222 : List (Nat × Nat × Nat) := [(2916636672,101382890288611,101383271447010),(2916728832,101383297347278,101383678505907)]
theorem point_links_checked22222 : (cuts22222.take 2).map (fun c => (2916614145-1+2*2^9*c.k,101382786447028+c.lower,101383167605369+c.upper)) = pointBounds22222 := by
 decide +kernel
def cuts22223 : List PrefixCut := [⟨74,337852848,337853038⟩,
⟨128,582093455,582093782⟩]
theorem checked22223 : checkPrefixCuts (2^48) 2916745217 9 Manual.Count131072.C022223.packed 128 cuts22223 = true := by
 decide +kernel
def pointBounds22223 : List (Nat × Nat × Nat) := [(2916820992,101383707674142,101384088833002)]
theorem point_links_checked22223 : (cuts22223.take 1).map (fun c => (2916745217-1+2*2^9*c.k,101383369821294+c.lower,101383750979964+c.upper)) = pointBounds22223 := by
 decide +kernel
def cuts22224 : List PrefixCut := [⟨36,162309844,162309941⟩,
⟨126,565566647,565566979⟩,
⟨128,574637124,574637462⟩]
theorem checked22224 : checkPrefixCuts (2^48) 2916876289 9 Manual.Count131072.C022224.packed 128 cuts22224 = true := by
 decide +kernel
def pointBounds22224 : List (Nat × Nat × Nat) := [(2916913152,101384114224593,101384495383687),(2917005312,101384517481396,101384898640725)]
theorem point_links_checked22224 : (cuts22224.take 2).map (fun c => (2916876289-1+2*2^9*c.k,101383951914749+c.lower,101384333073746+c.upper)) = pointBounds22224 := by
 decide +kernel
def cuts22225 : List PrefixCut := [⟨88,393208737,393208967⟩,
⟨128,575576240,575576574⟩]
theorem checked22225 : checkPrefixCuts (2^48) 2917007361 9 Manual.Count131072.C022225.packed 128 cuts22225 = true := by
 decide +kernel
def pointBounds22225 : List (Nat × Nat × Nat) := [(2917097472,101384919760610,101385300920175)]
theorem point_links_checked22225 : (cuts22225.take 1).map (fun c => (2917007361-1+2*2^9*c.k,101384526551873+c.lower,101384907711208+c.upper)) = pointBounds22225 := by
 decide +kernel
def cuts22226 : List PrefixCut := [⟨50,226267200,226267333⟩,
⟨128,582883363,582883701⟩]
theorem checked22226 : checkPrefixCuts (2^48) 2917138433 9 Manual.Count131072.C022226.packed 128 cuts22226 = true := by
 decide +kernel
def pointBounds22226 : List (Nat × Nat × Nat) := [(2917189632,101385328395313,101385709555115)]
theorem point_links_checked22226 : (cuts22226.take 1).map (fun c => (2917138433-1+2*2^9*c.k,101385102128113+c.lower,101385483287782+c.upper)) = pointBounds22226 := by
 decide +kernel
def cuts22227 : List PrefixCut := [⟨12,56058092,56058121⟩,
⟨102,462447864,462448128⟩,
⟨128,581602929,581603259⟩]
theorem checked22227 : checkPrefixCuts (2^48) 2917269505 9 Manual.Count131072.C022227.packed 128 cuts22227 = true := by
 decide +kernel
def pointBounds22227 : List (Nat × Nat × Nat) := [(2917281792,101385741069568,101386122229604),(2917373952,101386147459340,101386528619611)]
theorem point_links_checked22227 : (cuts22227.take 2).map (fun c => (2917269505-1+2*2^9*c.k,101385685011476+c.lower,101386066171483+c.upper)) = pointBounds22227 := by
 decide +kernel
def cuts22228 : List PrefixCut := [⟨64,289826885,289827058⟩,
⟨128,580226121,580226460⟩]
theorem checked22228 : checkPrefixCuts (2^48) 2917400577 9 Manual.Count131072.C022228.packed 128 cuts22228 = true := by
 decide +kernel
def pointBounds22228 : List (Nat × Nat × Nat) := [(2917466112,101386556441290,101386937601800)]
theorem point_links_checked22228 : (cuts22228.take 1).map (fun c => (2917400577-1+2*2^9*c.k,101386266614405+c.lower,101386647774742+c.upper)) = pointBounds22228 := by
 decide +kernel
def cuts22229 : List PrefixCut := [⟨26,119341588,119341657⟩,
⟨116,531288459,531288759⟩,
⟨128,585699197,585699526⟩]
theorem checked22229 : checkPrefixCuts (2^48) 2917531649 9 Manual.Count131072.C022229.packed 128 cuts22229 = true := by
 decide +kernel
def pointBounds22229 : List (Nat × Nat × Nat) := [(2917558272,101386966182114,101387347342859),(2917650432,101387378128985,101387759289961)]
theorem point_links_checked22229 : (cuts22229.take 2).map (fun c => (2917531649-1+2*2^9*c.k,101386846840526+c.lower,101387228001202+c.upper)) = pointBounds22229 := by
 decide +kernel
def cuts22230 : List PrefixCut := [⟨78,351445375,351445576⟩,
⟨128,575350481,575350812⟩]
theorem checked22230 : checkPrefixCuts (2^48) 2917662721 9 Manual.Count131072.C022230.packed 128 cuts22230 = true := by
 decide +kernel
def pointBounds22230 : List (Nat × Nat × Nat) := [(2917742592,101387783985098,101388165146304)]
theorem point_links_checked22230 : (cuts22230.take 1).map (fun c => (2917662721-1+2*2^9*c.k,101387432539723+c.lower,101387813700728+c.upper)) = pointBounds22230 := by
 decide +kernel
def cuts22231 : List PrefixCut := [⟨40,182806336,182806441⟩,
⟨128,584681849,584682188⟩]
theorem checked22231 : checkPrefixCuts (2^48) 2917793793 9 Manual.Count131072.C022231.packed 128 cuts22231 = true := by
 decide +kernel
def pointBounds22231 : List (Nat × Nat × Nat) := [(2917834752,101388190696540,101388571857981)]
theorem point_links_checked22231 : (cuts22231.take 1).map (fun c => (2917793793-1+2*2^9*c.k,101388007890204+c.lower,101388389051540+c.upper)) = pointBounds22231 := by
 decide +kernel
def cuts22232 : List PrefixCut := [⟨2,9453475,9453481⟩,
⟨92,414692360,414692596⟩,
⟨128,579832471,579832798⟩]
theorem checked22232 : checkPrefixCuts (2^48) 2917924865 9 Manual.Count131072.C022232.packed 128 cuts22232 = true := by
 decide +kernel
def pointBounds22232 : List (Nat × Nat × Nat) := [(2917926912,101388602025528,101388983187209),(2918019072,101389007264413,101389388426324)]
theorem point_links_checked22232 : (cuts22232.take 2).map (fun c => (2917924865-1+2*2^9*c.k,101388592572053+c.lower,101388973733728+c.upper)) = pointBounds22232 := by
 decide +kernel
def cuts22233 : List PrefixCut := [⟨54,251082301,251082446⟩,
⟨128,584243586,584243921⟩]
theorem checked22233 : checkPrefixCuts (2^48) 2918055937 9 Manual.Count131072.C022233.packed 128 cuts22233 = true := by
 decide +kernel
def pointBounds22233 : List (Nat × Nat × Nat) := [(2918111232,101389423486825,101389804648972)]
theorem point_links_checked22233 : (cuts22233.take 1).map (fun c => (2918055937-1+2*2^9*c.k,101389172404524+c.lower,101389553566526+c.upper)) = pointBounds22233 := by
 decide +kernel
def cuts22234 : List PrefixCut := [⟨16,70894518,70894561⟩,
⟨106,467992892,467993163⟩,
⟨128,571003029,571003360⟩]
theorem checked22234 : checkPrefixCuts (2^48) 2918187009 9 Manual.Count131072.C022234.packed 128 cuts22234 = true := by
 decide +kernel
def pointBounds22234 : List (Nat × Nat × Nat) := [(2918203392,101389827542628,101390208705008),(2918295552,101390224641002,101390605803610)]
theorem point_links_checked22234 : (cuts22234.take 2).map (fun c => (2918187009-1+2*2^9*c.k,101389756648110+c.lower,101390137810447+c.upper)) = pointBounds22234 := by
 decide +kernel
def cuts22235 : List PrefixCut := [⟨68,305649747,305649929⟩,
⟨128,569723711,569724044⟩]
theorem checked22235 : checkPrefixCuts (2^48) 2918318081 9 Manual.Count131072.C022235.packed 128 cuts22235 = true := by
 decide +kernel
def pointBounds22235 : List (Nat × Nat × Nat) := [(2918387712,101390633300886,101391014463736)]
theorem point_links_checked22235 : (cuts22235.take 1).map (fun c => (2918318081-1+2*2^9*c.k,101390327651139+c.lower,101390708813807+c.upper)) = pointBounds22235 := by
 decide +kernel
def cuts22236 : List PrefixCut := [⟨30,138882566,138882644⟩,
⟨120,546841580,546841892⟩,
⟨128,584357728,584358062⟩]
theorem checked22236 : checkPrefixCuts (2^48) 2918449153 9 Manual.Count131072.C022236.packed 128 cuts22236 = true := by
 decide +kernel
def pointBounds22236 : List (Nat × Nat × Nat) := [(2918479872,101391036257416,101391417420495),(2918572032,101391444216430,101391825379743)]
theorem point_links_checked22236 : (cuts22236.take 2).map (fun c => (2918449153-1+2*2^9*c.k,101390897374850+c.lower,101391278537851+c.upper)) = pointBounds22236 := by
 decide +kernel
def cuts22237 : List PrefixCut := [⟨82,370815783,370815993⟩,
⟨128,577773565,577773893⟩]
theorem checked22237 : checkPrefixCuts (2^48) 2918580225 9 Manual.Count131072.C022237.packed 128 cuts22237 = true := by
 decide +kernel
def pointBounds22237 : List (Nat × Nat × Nat) := [(2918664192,101391852548361,101392233711906)]
theorem point_links_checked22237 : (cuts22237.take 1).map (fun c => (2918580225-1+2*2^9*c.k,101391481732578+c.lower,101391862895913+c.upper)) = pointBounds22237 := by
 decide +kernel
def cuts22238 : List PrefixCut := [⟨44,197889405,197889517⟩,
⟨128,583919341,583919677⟩]
theorem checked22238 : checkPrefixCuts (2^48) 2918711297 9 Manual.Count131072.C022238.packed 128 cuts22238 = true := by
 decide +kernel
def pointBounds22238 : List (Nat × Nat × Nat) := [(2918756352,101392257395548,101392638559323)]
theorem point_links_checked22238 : (cuts22238.take 1).map (fun c => (2918711297-1+2*2^9*c.k,101392059506143+c.lower,101392440669806+c.upper)) = pointBounds22238 := by
 decide +kernel
def cuts22239 : List PrefixCut := [⟨6,27676454,27676471⟩,
⟨96,445612803,445613055⟩,
⟨128,586400531,586400863⟩]
theorem checked22239 : checkPrefixCuts (2^48) 2918842369 9 Manual.Count131072.C022239.packed 128 cuts22239 = true := by
 decide +kernel
def pointBounds22239 : List (Nat × Nat × Nat) := [(2918848512,101392671101938,101393052265954),(2918940672,101393089038287,101393470202538)]
theorem point_links_checked22239 : (cuts22239.take 2).map (fun c => (2918842369-1+2*2^9*c.k,101392643425484+c.lower,101393024589483+c.upper)) = pointBounds22239 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000069
