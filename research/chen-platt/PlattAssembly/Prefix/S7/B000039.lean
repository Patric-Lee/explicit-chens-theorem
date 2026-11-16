import PlattAssemblyKernel
import PlattCertificates.Count131072.C061248
import PlattCertificates.Count131072.C061249
import PlattCertificates.Count131072.C061250
import PlattCertificates.Count131072.C061251
import PlattCertificates.Count131072.C061252
import PlattCertificates.Count131072.C061253
import PlattCertificates.Count131072.C061254
import PlattCertificates.Count131072.C061255
import PlattCertificates.Count131072.C061256
import PlattCertificates.Count131072.C061257
import PlattCertificates.Count131072.C061258
import PlattCertificates.Count131072.C061259
import PlattCertificates.Count131072.C061260
import PlattCertificates.Count131072.C061261
import PlattCertificates.Count131072.C061262
import PlattCertificates.Count131072.C061263
import PlattCertificates.Count131072.C061264
import PlattCertificates.Count131072.C061265
import PlattCertificates.Count131072.C061266
import PlattCertificates.Count131072.C061267
import PlattCertificates.Count131072.C061268
import PlattCertificates.Count131072.C061269
import PlattCertificates.Count131072.C061270
import PlattCertificates.Count131072.C061271
import PlattCertificates.Count131072.C061272
import PlattCertificates.Count131072.C061273
import PlattCertificates.Count131072.C061274
import PlattCertificates.Count131072.C061275
import PlattCertificates.Count131072.C061276
import PlattCertificates.Count131072.C061277
import PlattCertificates.Count131072.C061278
import PlattCertificates.Count131072.C061279
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000039
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61248 : List PrefixCut := [⟨64,200840843,200840957⟩]
theorem checked61248 : checkPrefixCuts (2^48) 8031830017 10 Manual.Count131072.C061248.packed 64 cuts61248 = true := by
 decide +kernel
def cuts61249 : List PrefixCut := [⟨47,146764876,146764959⟩,
⟨64,200872596,200872712⟩]
theorem checked61249 : checkPrefixCuts (2^48) 8031961089 10 Manual.Count131072.C061249.packed 64 cuts61249 = true := by
 decide +kernel
def pointBounds61249 : List (Nat × Nat × Nat) := [(8032057344,114171248883139,114171637435831)]
theorem point_links_checked61249 : (cuts61249.take 1).map (fun c => (8031961089-1+2*2^10*c.k,114171102118263+c.lower,114171490670872+c.upper)) = pointBounds61249 := by
 decide +kernel
def cuts61250 : List PrefixCut := [⟨64,200904373,200904482⟩]
theorem checked61250 : checkPrefixCuts (2^48) 8032092161 10 Manual.Count131072.C061250.packed 64 cuts61250 = true := by
 decide +kernel
def cuts61251 : List PrefixCut := [⟨42,130009623,130009698⟩,
⟨64,198553221,198553336⟩]
theorem checked61251 : checkPrefixCuts (2^48) 8032223233 10 Manual.Count131072.C061251.packed 64 cuts61251 = true := by
 decide +kernel
def pointBounds61251 : List (Nat × Nat × Nat) := [(8032309248,114171633904855,114172022457764)]
theorem point_links_checked61251 : (cuts61251.take 1).map (fun c => (8032223233-1+2*2^10*c.k,114171503895232+c.lower,114171892448066+c.upper)) = pointBounds61251 := by
 decide +kernel
def cuts61252 : List PrefixCut := [⟨64,202509765,202509879⟩]
theorem checked61252 : checkPrefixCuts (2^48) 8032354305 10 Manual.Count131072.C061252.packed 64 cuts61252 = true := by
 decide +kernel
def cuts61253 : List PrefixCut := [⟨37,115603238,115603305⟩,
⟨64,202366278,202366395⟩]
theorem checked61253 : checkPrefixCuts (2^48) 8032485377 10 Manual.Count131072.C061253.packed 64 cuts61253 = true := by
 decide +kernel
def pointBounds61253 : List (Nat × Nat × Nat) := [(8032561152,114172020561456,114172409114586)]
theorem point_links_checked61253 : (cuts61253.take 1).map (fun c => (8032485377-1+2*2^10*c.k,114171904958218+c.lower,114172293511281+c.upper)) = pointBounds61253 := by
 decide +kernel
def cuts61254 : List PrefixCut := [⟨64,200225492,200225604⟩]
theorem checked61254 : checkPrefixCuts (2^48) 8032616449 10 Manual.Count131072.C061254.packed 64 cuts61254 = true := by
 decide +kernel
def cuts61255 : List PrefixCut := [⟨32,100461921,100461980⟩,
⟨64,201728951,201729064⟩]
theorem checked61255 : checkPrefixCuts (2^48) 8032747521 10 Manual.Count131072.C061255.packed 64 cuts61255 = true := by
 decide +kernel
def pointBounds61255 : List (Nat × Nat × Nat) := [(8032813056,114172408011909,114172796565260)]
theorem point_links_checked61255 : (cuts61255.take 1).map (fun c => (8032747521-1+2*2^10*c.k,114172307549988+c.lower,114172696103280+c.upper)) = pointBounds61255 := by
 decide +kernel
def cuts61256 : List PrefixCut := [⟨64,199518129,199518251⟩]
theorem checked61256 : checkPrefixCuts (2^48) 8032878593 10 Manual.Count131072.C061256.packed 64 cuts61256 = true := by
 decide +kernel
def cuts61257 : List PrefixCut := [⟨27,86197566,86197614⟩,
⟨64,200425922,200426033⟩]
theorem checked61257 : checkPrefixCuts (2^48) 8033009665 10 Manual.Count131072.C061257.packed 64 cuts61257 = true := by
 decide +kernel
def pointBounds61257 : List (Nat × Nat × Nat) := [(8033064960,114172794994634,114173183548209)]
theorem point_links_checked61257 : (cuts61257.take 1).map (fun c => (8033009665-1+2*2^10*c.k,114172708797068+c.lower,114173097350595+c.upper)) = pointBounds61257 := by
 decide +kernel
def cuts61258 : List PrefixCut := [⟨64,201859234,201859354⟩]
theorem checked61258 : checkPrefixCuts (2^48) 8033140737 10 Manual.Count131072.C061258.packed 64 cuts61258 = true := by
 decide +kernel
def cuts61259 : List PrefixCut := [⟨22,67904689,67904728⟩,
⟨64,200489437,200489554⟩]
theorem checked61259 : checkPrefixCuts (2^48) 8033271809 10 Manual.Count131072.C061259.packed 64 cuts61259 = true := by
 decide +kernel
def pointBounds61259 : List (Nat × Nat × Nat) := [(8033316864,114173178986913,114173567540710)]
theorem point_links_checked61259 : (cuts61259.take 1).map (fun c => (8033271809-1+2*2^10*c.k,114173111082224+c.lower,114173499635982+c.upper)) = pointBounds61259 := by
 decide +kernel
def cuts61260 : List PrefixCut := [⟨64,200381067,200381177⟩]
theorem checked61260 : checkPrefixCuts (2^48) 8033402881 10 Manual.Count131072.C061260.packed 64 cuts61260 = true := by
 decide +kernel
def cuts61261 : List PrefixCut := [⟨17,53852509,53852540⟩,
⟨64,201008463,201008580⟩]
theorem checked61261 : checkPrefixCuts (2^48) 8033533953 10 Manual.Count131072.C061261.packed 64 cuts61261 = true := by
 decide +kernel
def pointBounds61261 : List (Nat × Nat × Nat) := [(8033568768,114173565805237,114173954359253)]
theorem point_links_checked61261 : (cuts61261.take 1).map (fun c => (8033533953-1+2*2^10*c.k,114173511952728+c.lower,114173900506713+c.upper)) = pointBounds61261 := by
 decide +kernel
def cuts61262 : List PrefixCut := [⟨64,203107380,203107497⟩]
theorem checked61262 : checkPrefixCuts (2^48) 8033665025 10 Manual.Count131072.C061262.packed 64 cuts61262 = true := by
 decide +kernel
def cuts61263 : List PrefixCut := [⟨12,37138473,37138497⟩,
⟨64,198899737,198899856⟩]
theorem checked61263 : checkPrefixCuts (2^48) 8033796097 10 Manual.Count131072.C061263.packed 64 cuts61263 = true := by
 decide +kernel
def pointBounds61263 : List (Nat × Nat × Nat) := [(8033820672,114173953207044,114174341761287)]
theorem point_links_checked61263 : (cuts61263.take 1).map (fun c => (8033796097-1+2*2^10*c.k,114173916068571+c.lower,114174304622790+c.upper)) = pointBounds61263 := by
 decide +kernel
def cuts61264 : List PrefixCut := [⟨64,197214783,197214899⟩]
theorem checked61264 : checkPrefixCuts (2^48) 8033927169 10 Manual.Count131072.C061264.packed 64 cuts61264 = true := by
 decide +kernel
def cuts61265 : List PrefixCut := [⟨7,22002091,22002103⟩,
⟨64,203728068,203728176⟩]
theorem checked61265 : checkPrefixCuts (2^48) 8034058241 10 Manual.Count131072.C061265.packed 64 cuts61265 = true := by
 decide +kernel
def pointBounds61265 : List (Nat × Nat × Nat) := [(8034072576,114174334185182,114174722739648)]
theorem point_links_checked61265 : (cuts61265.take 1).map (fun c => (8034058241-1+2*2^10*c.k,114174312183091+c.lower,114174700737545+c.upper)) = pointBounds61265 := by
 decide +kernel
def cuts61266 : List PrefixCut := [⟨64,202708742,202708858⟩]
theorem checked61266 : checkPrefixCuts (2^48) 8034189313 10 Manual.Count131072.C061266.packed 64 cuts61266 = true := by
 decide +kernel
def cuts61267 : List PrefixCut := [⟨2,6901709,6901712⟩,
⟨64,202109875,202109989⟩]
theorem checked61267 : checkPrefixCuts (2^48) 8034320385 10 Manual.Count131072.C061267.packed 64 cuts61267 = true := by
 decide +kernel
def pointBounds61267 : List (Nat × Nat × Nat) := [(8034324480,114174725521610,114175114076291)]
theorem point_links_checked61267 : (cuts61267.take 1).map (fun c => (8034320385-1+2*2^10*c.k,114174718619901+c.lower,114175107174579+c.upper)) = pointBounds61267 := by
 decide +kernel
def cuts61268 : List PrefixCut := [⟨61,190265429,190265538⟩,
⟨64,199969553,199969666⟩]
theorem checked61268 : checkPrefixCuts (2^48) 8034451457 10 Manual.Count131072.C061268.packed 64 cuts61268 = true := by
 decide +kernel
def pointBounds61268 : List (Nat × Nat × Nat) := [(8034576384,114175110995205,114175499550106)]
theorem point_links_checked61268 : (cuts61268.take 1).map (fun c => (8034451457-1+2*2^10*c.k,114174920729776+c.lower,114175309284568+c.upper)) = pointBounds61268 := by
 decide +kernel
def cuts61269 : List PrefixCut := [⟨64,200842101,200842214⟩]
theorem checked61269 : checkPrefixCuts (2^48) 8034582529 10 Manual.Count131072.C061269.packed 64 cuts61269 = true := by
 decide +kernel
def cuts61270 : List PrefixCut := [⟨56,176421663,176421760⟩,
⟨64,201609537,201609648⟩]
theorem checked61270 : checkPrefixCuts (2^48) 8034713601 10 Manual.Count131072.C061270.packed 64 cuts61270 = true := by
 decide +kernel
def pointBounds61270 : List (Nat × Nat × Nat) := [(8034828288,114175497963093,114175886518208)]
theorem point_links_checked61270 : (cuts61270.take 1).map (fun c => (8034713601-1+2*2^10*c.k,114175321541430+c.lower,114175710096448+c.upper)) = pointBounds61270 := by
 decide +kernel
def cuts61271 : List PrefixCut := [⟨64,199048942,199049052⟩]
theorem checked61271 : checkPrefixCuts (2^48) 8034844673 10 Manual.Count131072.C061271.packed 64 cuts61271 = true := by
 decide +kernel
def cuts61272 : List PrefixCut := [⟨51,161948219,161948308⟩,
⟨64,202864069,202864180⟩]
theorem checked61272 : checkPrefixCuts (2^48) 8034975745 10 Manual.Count131072.C061272.packed 64 cuts61272 = true := by
 decide +kernel
def pointBounds61272 : List (Nat × Nat × Nat) := [(8035080192,114175884148128,114176272703456)]
theorem point_links_checked61272 : (cuts61272.take 1).map (fun c => (8034975745-1+2*2^10*c.k,114175722199909+c.lower,114176110755148+c.upper)) = pointBounds61272 := by
 decide +kernel
def cuts61273 : List PrefixCut := [⟨64,203141002,203141118⟩]
theorem checked61273 : checkPrefixCuts (2^48) 8035106817 10 Manual.Count131072.C061273.packed 64 cuts61273 = true := by
 decide +kernel
def cuts61274 : List PrefixCut := [⟨46,144848461,144848544⟩,
⟨64,201211046,201211160⟩]
theorem checked61274 : checkPrefixCuts (2^48) 8035237889 10 Manual.Count131072.C061274.packed 64 cuts61274 = true := by
 decide +kernel
def pointBounds61274 : List (Nat × Nat × Nat) := [(8035332096,114176273053441,114176661608990)]
theorem point_links_checked61274 : (cuts61274.take 1).map (fun c => (8035237889-1+2*2^10*c.k,114176128204980+c.lower,114176516760446+c.upper)) = pointBounds61274 := by
 decide +kernel
def cuts61275 : List PrefixCut := [⟨64,200016767,200016883⟩]
theorem checked61275 : checkPrefixCuts (2^48) 8035368961 10 Manual.Count131072.C061275.packed 64 cuts61275 = true := by
 decide +kernel
def cuts61276 : List PrefixCut := [⟨41,129501238,129501316⟩,
⟨64,202605617,202605736⟩]
theorem checked61276 : checkPrefixCuts (2^48) 8035500033 10 Manual.Count131072.C061276.packed 64 cuts61276 = true := by
 decide +kernel
def pointBounds61276 : List (Nat × Nat × Nat) := [(8035584000,114176658934031,114177047489805)]
theorem point_links_checked61276 : (cuts61276.take 1).map (fun c => (8035500033-1+2*2^10*c.k,114176529432793+c.lower,114176917988489+c.upper)) = pointBounds61276 := by
 decide +kernel
def cuts61277 : List PrefixCut := [⟨64,201201202,201201316⟩]
theorem checked61277 : checkPrefixCuts (2^48) 8035631105 10 Manual.Count131072.C061277.packed 64 cuts61277 = true := by
 decide +kernel
def cuts61278 : List PrefixCut := [⟨36,115591137,115591207⟩,
⟨64,203474708,203474830⟩]
theorem checked61278 : checkPrefixCuts (2^48) 8035762177 10 Manual.Count131072.C061278.packed 64 cuts61278 = true := by
 decide +kernel
def pointBounds61278 : List (Nat × Nat × Nat) := [(8035835904,114177048830749,114177437386748)]
theorem point_links_checked61278 : (cuts61278.take 1).map (fun c => (8035762177-1+2*2^10*c.k,114176933239612+c.lower,114177321795541+c.upper)) = pointBounds61278 := by
 decide +kernel
def cuts61279 : List PrefixCut := [⟨64,196571097,196571215⟩]
theorem checked61279 : checkPrefixCuts (2^48) 8035893249 10 Manual.Count131072.C061279.packed 64 cuts61279 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000039
