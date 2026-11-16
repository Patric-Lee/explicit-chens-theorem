import PlattAssemblyKernel
import PlattCertificates.Count131072.C025248
import PlattCertificates.Count131072.C025249
import PlattCertificates.Count131072.C025250
import PlattCertificates.Count131072.C025251
import PlattCertificates.Count131072.C025252
import PlattCertificates.Count131072.C025253
import PlattCertificates.Count131072.C025254
import PlattCertificates.Count131072.C025255
import PlattCertificates.Count131072.C025256
import PlattCertificates.Count131072.C025257
import PlattCertificates.Count131072.C025258
import PlattCertificates.Count131072.C025259
import PlattCertificates.Count131072.C025260
import PlattCertificates.Count131072.C025261
import PlattCertificates.Count131072.C025262
import PlattCertificates.Count131072.C025263
import PlattCertificates.Count131072.C025264
import PlattCertificates.Count131072.C025265
import PlattCertificates.Count131072.C025266
import PlattCertificates.Count131072.C025267
import PlattCertificates.Count131072.C025268
import PlattCertificates.Count131072.C025269
import PlattCertificates.Count131072.C025270
import PlattCertificates.Count131072.C025271
import PlattCertificates.Count131072.C025272
import PlattCertificates.Count131072.C025273
import PlattCertificates.Count131072.C025274
import PlattCertificates.Count131072.C025275
import PlattCertificates.Count131072.C025276
import PlattCertificates.Count131072.C025277
import PlattCertificates.Count131072.C025278
import PlattCertificates.Count131072.C025279
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000164
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25248 : List PrefixCut := [⟨66,262846924,262847071⟩,
⟨128,499523434,499523716⟩]
theorem checked25248 : checkPrefixCuts (2^48) 3313238017 9 Manual.Count131072.C025248.packed 128 cuts25248 = true := by
 decide +kernel
def pointBounds25248 : List (Nat × Nat × Nat) := [(3313305600,103024882113370,103025264201093)]
theorem point_links_checked25248 : (cuts25248.take 1).map (fun c => (3313238017-1+2*2^9*c.k,103024619266446+c.lower,103025001354022+c.upper)) = pointBounds25248 := by
 decide +kernel
def cuts25249 : List PrefixCut := [⟨40,158942831,158942923⟩,
⟨128,509697492,509697783⟩]
theorem checked25249 : checkPrefixCuts (2^48) 3313369089 9 Manual.Count131072.C025249.packed 128 cuts25249 = true := by
 decide +kernel
def pointBounds25249 : List (Nat × Nat × Nat) := [(3313410048,103025277732711,103025659820661)]
theorem point_links_checked25249 : (cuts25249.take 1).map (fun c => (3313369089-1+2*2^9*c.k,103025118789880+c.lower,103025500877738+c.upper)) = pointBounds25249 := by
 decide +kernel
def cuts25250 : List PrefixCut := [⟨14,56660129,56660162⟩,
⟨116,465251308,465251570⟩,
⟨128,511461225,511461513⟩]
theorem checked25250 : checkPrefixCuts (2^48) 3313500161 9 Manual.Count131072.C025250.packed 128 cuts25250 = true := by
 decide +kernel
def pointBounds25250 : List (Nat × Nat × Nat) := [(3313514496,103025685147501,103026067235683),(3313618944,103026093738680,103026475827091)]
theorem point_links_checked25250 : (cuts25250.take 2).map (fun c => (3313500161-1+2*2^9*c.k,103025628487372+c.lower,103026010575521+c.upper)) = pointBounds25250 := by
 decide +kernel
def cuts25251 : List PrefixCut := [⟨90,353704174,353704377⟩,
⟨128,504900380,504900667⟩]
theorem checked25251 : checkPrefixCuts (2^48) 3313631233 9 Manual.Count131072.C025251.packed 128 cuts25251 = true := by
 decide +kernel
def pointBounds25251 : List (Nat × Nat × Nat) := [(3313723392,103026493652771,103026875741411)]
theorem point_links_checked25251 : (cuts25251.take 1).map (fun c => (3313631233-1+2*2^9*c.k,103026139948597+c.lower,103026522037034+c.upper)) = pointBounds25251 := by
 decide +kernel
def cuts25252 : List PrefixCut := [⟨64,257878897,257879039⟩,
⟨128,505644990,505645275⟩]
theorem checked25252 : checkPrefixCuts (2^48) 3313762305 9 Manual.Count131072.C025252.packed 128 cuts25252 = true := by
 decide +kernel
def pointBounds25252 : List (Nat × Nat × Nat) := [(3313827840,103026902727874,103027284816740)]
theorem point_links_checked25252 : (cuts25252.take 1).map (fun c => (3313762305-1+2*2^9*c.k,103026644848977+c.lower,103027026937701+c.upper)) = pointBounds25252 := by
 decide +kernel
def cuts25253 : List PrefixCut := [⟨38,150593871,150593956⟩,
⟨128,505115265,505115552⟩]
theorem checked25253 : checkPrefixCuts (2^48) 3313893377 9 Manual.Count131072.C025253.packed 128 cuts25253 = true := by
 decide +kernel
def pointBounds25253 : List (Nat × Nat × Nat) := [(3313932288,103027301087838,103027683176932)]
theorem point_links_checked25253 : (cuts25253.take 1).map (fun c => (3313893377-1+2*2^9*c.k,103027150493967+c.lower,103027532582976+c.upper)) = pointBounds25253 := by
 decide +kernel
def cuts25254 : List PrefixCut := [⟨12,47138539,47138567⟩,
⟨114,451588579,451588836⟩,
⟨128,507728164,507728453⟩]
theorem checked25254 : checkPrefixCuts (2^48) 3314024449 9 Manual.Count131072.C025254.packed 128 cuts25254 = true := by
 decide +kernel
def pointBounds25254 : List (Nat × Nat × Nat) := [(3314036736,103027702747771,103028084837095),(3314141184,103028107197811,103028489287364)]
theorem point_links_checked25254 : (cuts25254.take 2).map (fun c => (3314024449-1+2*2^9*c.k,103027655609232+c.lower,103028037698528+c.upper)) = pointBounds25254 := by
 decide +kernel
def cuts25255 : List PrefixCut := [⟨88,344815616,344815807⟩,
⟨128,504565696,504565975⟩]
theorem checked25255 : checkPrefixCuts (2^48) 3314155521 9 Manual.Count131072.C025255.packed 128 cuts25255 = true := by
 decide +kernel
def pointBounds25255 : List (Nat × Nat × Nat) := [(3314245632,103028508153012,103028890242788)]
theorem point_links_checked25255 : (cuts25255.take 1).map (fun c => (3314155521-1+2*2^9*c.k,103028163337396+c.lower,103028545426981+c.upper)) = pointBounds25255 := by
 decide +kernel
def cuts25256 : List PrefixCut := [⟨62,244419754,244419889⟩,
⟨128,507008626,507008904⟩]
theorem checked25256 : checkPrefixCuts (2^48) 3314286593 9 Manual.Count131072.C025256.packed 128 cuts25256 = true := by
 decide +kernel
def pointBounds25256 : List (Nat × Nat × Nat) := [(3314350080,103028912322846,103029294412845)]
theorem point_links_checked25256 : (cuts25256.take 1).map (fun c => (3314286593-1+2*2^9*c.k,103028667903092+c.lower,103029049992956+c.upper)) = pointBounds25256 := by
 decide +kernel
def cuts25257 : List PrefixCut := [⟨36,142417403,142417483⟩,
⟨128,512678371,512678659⟩]
theorem checked25257 : checkPrefixCuts (2^48) 3314417665 9 Manual.Count131072.C025257.packed 128 cuts25257 = true := by
 decide +kernel
def pointBounds25257 : List (Nat × Nat × Nat) := [(3314454528,103029317329121,103029699419343)]
theorem point_links_checked25257 : (cuts25257.take 1).map (fun c => (3314417665-1+2*2^9*c.k,103029174911718+c.lower,103029557001860+c.upper)) = pointBounds25257 := by
 decide +kernel
def cuts25258 : List PrefixCut := [⟨10,41526319,41526343⟩,
⟨112,445063425,445063679⟩,
⟨128,509091512,509091799⟩]
theorem checked25258 : checkPrefixCuts (2^48) 3314548737 9 Manual.Count131072.C025258.packed 128 cuts25258 = true := by
 decide +kernel
def pointBounds25258 : List (Nat × Nat × Nat) := [(3314558976,103029729116408,103030111206862),(3314663424,103030132653514,103030514744198)]
theorem point_links_checked25258 : (cuts25258.take 2).map (fun c => (3314548737-1+2*2^9*c.k,103029687590089+c.lower,103030069680519+c.upper)) = pointBounds25258 := by
 decide +kernel
def cuts25259 : List PrefixCut := [⟨86,339751078,339751272⟩,
⟨128,501938485,501938771⟩]
theorem checked25259 : checkPrefixCuts (2^48) 3314679809 9 Manual.Count131072.C025259.packed 128 cuts25259 = true := by
 decide +kernel
def pointBounds25259 : List (Nat × Nat × Nat) := [(3314767872,103030536432679,103030918523590)]
theorem point_links_checked25259 : (cuts25259.take 1).map (fun c => (3314679809-1+2*2^9*c.k,103030196681601+c.lower,103030578772318+c.upper)) = pointBounds25259 := by
 decide +kernel
def cuts25260 : List PrefixCut := [⟨60,241579004,241579135⟩,
⟨128,508881476,508881759⟩]
theorem checked25260 : checkPrefixCuts (2^48) 3314810881 9 Manual.Count131072.C025260.packed 128 cuts25260 = true := by
 decide +kernel
def pointBounds25260 : List (Nat × Nat × Nat) := [(3314872320,103030940199090,103031322290224)]
theorem point_links_checked25260 : (cuts25260.take 1).map (fun c => (3314810881-1+2*2^9*c.k,103030698620086+c.lower,103031080711089+c.upper)) = pointBounds25260 := by
 decide +kernel
def cuts25261 : List PrefixCut := [⟨34,136705914,136705989⟩,
⟨128,509031093,509031376⟩]
theorem checked25261 : checkPrefixCuts (2^48) 3314941953 9 Manual.Count131072.C025261.packed 128 cuts25261 = true := by
 decide +kernel
def pointBounds25261 : List (Nat × Nat × Nat) := [(3314976768,103031344207476,103031726298837)]
theorem point_links_checked25261 : (cuts25261.take 1).map (fun c => (3314941953-1+2*2^9*c.k,103031207501562+c.lower,103031589592848+c.upper)) = pointBounds25261 := by
 decide +kernel
def cuts25262 : List PrefixCut := [⟨8,31161050,31161067⟩,
⟨110,432342202,432342447⟩,
⟨128,508076999,508077286⟩]
theorem checked25262 : checkPrefixCuts (2^48) 3315073025 9 Manual.Count131072.C025262.packed 128 cuts25262 = true := by
 decide +kernel
def pointBounds25262 : List (Nat × Nat × Nat) := [(3315081216,103031747693705,103032129785291),(3315185664,103032148874857,103032530966671)]
theorem point_links_checked25262 : (cuts25262.take 2).map (fun c => (3315073025-1+2*2^9*c.k,103031716532655+c.lower,103032098624224+c.upper)) = pointBounds25262 := by
 decide +kernel
def cuts25263 : List PrefixCut := [⟨84,331631699,331631883⟩,
⟨128,504745763,504746043⟩]
theorem checked25263 : checkPrefixCuts (2^48) 3315204097 9 Manual.Count131072.C025263.packed 128 cuts25263 = true := by
 decide +kernel
def pointBounds25263 : List (Nat × Nat × Nat) := [(3315290112,103032556241353,103032938333393)]
theorem point_links_checked25263 : (cuts25263.take 1).map (fun c => (3315204097-1+2*2^9*c.k,103032224609654+c.lower,103032606701510+c.upper)) = pointBounds25263 := by
 decide +kernel
def cuts25264 : List PrefixCut := [⟨58,231352816,231352944⟩,
⟨128,507697247,507697529⟩]
theorem checked25264 : checkPrefixCuts (2^48) 3315335169 9 Manual.Count131072.C025264.packed 128 cuts25264 = true := by
 decide +kernel
def pointBounds25264 : List (Nat × Nat × Nat) := [(3315394560,103032960708233,103033342800497)]
theorem point_links_checked25264 : (cuts25264.take 1).map (fun c => (3315335169-1+2*2^9*c.k,103032729355417+c.lower,103033111447553+c.upper)) = pointBounds25264 := by
 decide +kernel
def cuts25265 : List PrefixCut := [⟨32,126326890,126326963⟩,
⟨128,504366238,504366523⟩]
theorem checked25265 : checkPrefixCuts (2^48) 3315466241 9 Manual.Count131072.C025265.packed 128 cuts25265 = true := by
 decide +kernel
def pointBounds25265 : List (Nat × Nat × Nat) := [(3315499008,103033363379554,103033745472045)]
theorem point_links_checked25265 : (cuts25265.take 1).map (fun c => (3315466241-1+2*2^9*c.k,103033237052664+c.lower,103033619145082+c.upper)) = pointBounds25265 := by
 decide +kernel
def cuts25266 : List PrefixCut := [⟨6,22412042,22412054⟩,
⟨108,432783248,432783482⟩,
⟨128,512920427,512920706⟩]
theorem checked25266 : checkPrefixCuts (2^48) 3315597313 9 Manual.Count131072.C025266.packed 128 cuts25266 = true := by
 decide +kernel
def pointBounds25266 : List (Nat × Nat × Nat) := [(3315603456,103033763830944,103034145923659),(3315707904,103034174202150,103034556295087)]
theorem point_links_checked25266 : (cuts25266.take 2).map (fun c => (3315597313-1+2*2^9*c.k,103033741418902+c.lower,103034123511605+c.upper)) = pointBounds25266 := by
 decide +kernel
def cuts25267 : List PrefixCut := [⟨82,326910440,326910621⟩,
⟨128,510693108,510693392⟩]
theorem checked25267 : checkPrefixCuts (2^48) 3315728385 9 Manual.Count131072.C025267.packed 128 cuts25267 = true := by
 decide +kernel
def pointBounds25267 : List (Nat × Nat × Nat) := [(3315812352,103034581249769,103034963342932)]
theorem point_links_checked25267 : (cuts25267.take 1).map (fun c => (3315728385-1+2*2^9*c.k,103034254339329+c.lower,103034636432311+c.upper)) = pointBounds25267 := by
 decide +kernel
def cuts25268 : List PrefixCut := [⟨56,223167207,223167336⟩,
⟨128,507192606,507192893⟩]
theorem checked25268 : checkPrefixCuts (2^48) 3315859457 9 Manual.Count131072.C025268.packed 128 cuts25268 = true := by
 decide +kernel
def pointBounds25268 : List (Nat × Nat × Nat) := [(3315916800,103034988199644,103035370293039)]
theorem point_links_checked25268 : (cuts25268.take 1).map (fun c => (3315859457-1+2*2^9*c.k,103034765032437+c.lower,103035147125703+c.upper)) = pointBounds25268 := by
 decide +kernel
def cuts25269 : List PrefixCut := [⟨30,120195341,120195407⟩,
⟨128,510567867,510568146⟩]
theorem checked25269 : checkPrefixCuts (2^48) 3315990529 9 Manual.Count131072.C025269.packed 128 cuts25269 = true := by
 decide +kernel
def pointBounds25269 : List (Nat × Nat × Nat) := [(3316021248,103035392420384,103035774514003)]
theorem point_links_checked25269 : (cuts25269.take 1).map (fun c => (3315990529-1+2*2^9*c.k,103035272225043+c.lower,103035654318596+c.upper)) = pointBounds25269 := by
 decide +kernel
def cuts25270 : List PrefixCut := [⟨4,15533168,15533177⟩,
⟨106,427537348,427537584⟩,
⟨128,516404286,516404571⟩]
theorem checked25270 : checkPrefixCuts (2^48) 3316121601 9 Manual.Count131072.C025270.packed 128 cuts25270 = true := by
 decide +kernel
def pointBounds25270 : List (Nat × Nat × Nat) := [(3316125696,103035798326078,103036180419919),(3316230144,103036210330258,103036592424326)]
theorem point_links_checked25270 : (cuts25270.take 2).map (fun c => (3316121601-1+2*2^9*c.k,103035782792910+c.lower,103036164886742+c.upper)) = pointBounds25270 := by
 decide +kernel
def cuts25271 : List PrefixCut := [⟨80,315994682,315994862⟩,
⟨128,504076953,504077239⟩]
theorem checked25271 : checkPrefixCuts (2^48) 3316252673 9 Manual.Count131072.C025271.packed 128 cuts25271 = true := by
 decide +kernel
def pointBounds25271 : List (Nat × Nat × Nat) := [(3316334592,103036615191878,103036997286175)]
theorem point_links_checked25271 : (cuts25271.take 1).map (fun c => (3316252673-1+2*2^9*c.k,103036299197196+c.lower,103036681291313+c.upper)) = pointBounds25271 := by
 decide +kernel
def cuts25272 : List PrefixCut := [⟨54,214390051,214390172⟩,
⟨128,508470379,508470662⟩]
theorem checked25272 : checkPrefixCuts (2^48) 3316383745 9 Manual.Count131072.C025272.packed 128 cuts25272 = true := by
 decide +kernel
def pointBounds25272 : List (Nat × Nat × Nat) := [(3316439040,103037017664200,103037399758724)]
theorem point_links_checked25272 : (cuts25272.take 1).map (fun c => (3316383745-1+2*2^9*c.k,103036803274149+c.lower,103037185368552+c.upper)) = pointBounds25272 := by
 decide +kernel
def cuts25273 : List PrefixCut := [⟨28,112198565,112198627⟩,
⟨128,510571985,510572270⟩]
theorem checked25273 : checkPrefixCuts (2^48) 3316514817 9 Manual.Count131072.C025273.packed 128 cuts25273 = true := by
 decide +kernel
def pointBounds25273 : List (Nat × Nat × Nat) := [(3316543488,103037423943093,103037806037841)]
theorem point_links_checked25273 : (cuts25273.take 1).map (fun c => (3316514817-1+2*2^9*c.k,103037311744528+c.lower,103037693839214+c.upper)) = pointBounds25273 := by
 decide +kernel
def cuts25274 : List PrefixCut := [⟨2,8316996,8317001⟩,
⟨104,410666480,410666709⟩,
⟨128,505799357,505799641⟩]
theorem checked25274 : checkPrefixCuts (2^48) 3316645889 9 Manual.Count131072.C025274.packed 128 cuts25274 = true := by
 decide +kernel
def pointBounds25274 : List (Nat × Nat × Nat) := [(3316647936,103037830633509,103038212728485),(3316752384,103038232982993,103038615078193)]
theorem point_links_checked25274 : (cuts25274.take 2).map (fun c => (3316645889-1+2*2^9*c.k,103037822316513+c.lower,103038204411484+c.upper)) = pointBounds25274 := by
 decide +kernel
def cuts25275 : List PrefixCut := [⟨78,307288773,307288944⟩,
⟨128,507137077,507137360⟩]
theorem checked25275 : checkPrefixCuts (2^48) 3316776961 9 Manual.Count131072.C025275.packed 128 cuts25275 = true := by
 decide +kernel
def pointBounds25275 : List (Nat × Nat × Nat) := [(3316856832,103038635404643,103039017500069)]
theorem point_links_checked25275 : (cuts25275.take 1).map (fun c => (3316776961-1+2*2^9*c.k,103038328115870+c.lower,103038710211125+c.upper)) = pointBounds25275 := by
 decide +kernel
def cuts25276 : List PrefixCut := [⟨52,205106470,205106587⟩,
⟨128,507032200,507032492⟩]
theorem checked25276 : checkPrefixCuts (2^48) 3316908033 9 Manual.Count131072.C025276.packed 128 cuts25276 = true := by
 decide +kernel
def pointBounds25276 : List (Nat × Nat × Nat) := [(3316961280,103039040359417,103039422455072)]
theorem point_links_checked25276 : (cuts25276.take 1).map (fun c => (3316908033-1+2*2^9*c.k,103038835252947+c.lower,103039217348485+c.upper)) = pointBounds25276 := by
 decide +kernel
def cuts25277 : List PrefixCut := [⟨26,102337463,102337519⟩,
⟨128,512358067,512358357⟩]
theorem checked25277 : checkPrefixCuts (2^48) 3317039105 9 Manual.Count131072.C025277.packed 128 cuts25277 = true := by
 decide +kernel
def pointBounds25277 : List (Nat × Nat × Nat) := [(3317065728,103039444622610,103039826718496),(3317170176,103039854643214,103040236739334)]
theorem point_links_checked25277 : (cuts25277.take 2).map (fun c => (3317039105-1+2*2^9*c.k,103039342285147+c.lower,103039724380977+c.upper)) = pointBounds25277 := by
 decide +kernel
def cuts25278 : List PrefixCut := [⟨102,407971196,407971431⟩,
⟨128,510046844,510047137⟩]
theorem checked25278 : checkPrefixCuts (2^48) 3317170177 9 Manual.Count131072.C025278.packed 128 cuts25278 = true := by
 decide +kernel
def pointBounds25278 : List (Nat × Nat × Nat) := [(3317274624,103040262614410,103040644710765)]
theorem point_links_checked25278 : (cuts25278.take 1).map (fun c => (3317170177-1+2*2^9*c.k,103039854643214+c.lower,103040236739334+c.upper)) = pointBounds25278 := by
 decide +kernel
def cuts25279 : List PrefixCut := [⟨76,298246248,298246422⟩,
⟨128,500099384,500099669⟩]
theorem checked25279 : checkPrefixCuts (2^48) 3317301249 9 Manual.Count131072.C025279.packed 128 cuts25279 = true := by
 decide +kernel
def pointBounds25279 : List (Nat × Nat × Nat) := [(3317379072,103040662936306,103041045032893)]
theorem point_links_checked25279 : (cuts25279.take 1).map (fun c => (3317301249-1+2*2^9*c.k,103040364690058+c.lower,103040746786471+c.upper)) = pointBounds25279 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000164
