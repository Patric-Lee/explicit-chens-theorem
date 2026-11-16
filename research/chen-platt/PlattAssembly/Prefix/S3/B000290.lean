import PlattAssemblyKernel
import PlattCertificates.Count131072.C029280
import PlattCertificates.Count131072.C029281
import PlattCertificates.Count131072.C029282
import PlattCertificates.Count131072.C029283
import PlattCertificates.Count131072.C029284
import PlattCertificates.Count131072.C029285
import PlattCertificates.Count131072.C029286
import PlattCertificates.Count131072.C029287
import PlattCertificates.Count131072.C029288
import PlattCertificates.Count131072.C029289
import PlattCertificates.Count131072.C029290
import PlattCertificates.Count131072.C029291
import PlattCertificates.Count131072.C029292
import PlattCertificates.Count131072.C029293
import PlattCertificates.Count131072.C029294
import PlattCertificates.Count131072.C029295
import PlattCertificates.Count131072.C029296
import PlattCertificates.Count131072.C029297
import PlattCertificates.Count131072.C029298
import PlattCertificates.Count131072.C029299
import PlattCertificates.Count131072.C029300
import PlattCertificates.Count131072.C029301
import PlattCertificates.Count131072.C029302
import PlattCertificates.Count131072.C029303
import PlattCertificates.Count131072.C029304
import PlattCertificates.Count131072.C029305
import PlattCertificates.Count131072.C029306
import PlattCertificates.Count131072.C029307
import PlattCertificates.Count131072.C029308
import PlattCertificates.Count131072.C029309
import PlattCertificates.Count131072.C029310
import PlattCertificates.Count131072.C029311
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000290
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts29280 : List PrefixCut := [⟨54,186025960,186026067⟩,
⟨128,431687351,431687594⟩]
theorem checked29280 : checkPrefixCuts (2^48) 3841720321 9 Manual.Count131072.C029280.packed 128 cuts29280 = true := by
 decide +kernel
def pointBounds29280 : List (Nat × Nat × Nat) := [(3841775616,104918890586780,104919273734629)]
theorem point_links_checked29280 : (cuts29280.take 1).map (fun c => (3841720321-1+2*2^9*c.k,104918704560820+c.lower,104919087708562+c.upper)) = pointBounds29280 := by
 decide +kernel
def cuts29281 : List PrefixCut := [⟨44,151365487,151365576⟩,
⟨128,433797178,433797428⟩]
theorem checked29281 : checkPrefixCuts (2^48) 3841851393 9 Manual.Count131072.C029281.packed 128 cuts29281 = true := by
 decide +kernel
def pointBounds29281 : List (Nat × Nat × Nat) := [(3841896448,104919287613658,104919670761732)]
theorem point_links_checked29281 : (cuts29281.take 1).map (fun c => (3841851393-1+2*2^9*c.k,104919136248171+c.lower,104919519396156+c.upper)) = pointBounds29281 := by
 decide +kernel
def cuts29282 : List PrefixCut := [⟨34,117439949,117440012⟩,
⟨128,430778774,430779016⟩]
theorem checked29282 : checkPrefixCuts (2^48) 3841982465 9 Manual.Count131072.C029282.packed 128 cuts29282 = true := by
 decide +kernel
def pointBounds29282 : List (Nat × Nat × Nat) := [(3842017280,104919687485298,104920070633596)]
theorem point_links_checked29282 : (cuts29282.take 1).map (fun c => (3841982465-1+2*2^9*c.k,104919570045349+c.lower,104919953193584+c.upper)) = pointBounds29282 := by
 decide +kernel
def cuts29283 : List PrefixCut := [⟨24,83370104,83370154⟩,
⟨128,435672405,435672656⟩]
theorem checked29283 : checkPrefixCuts (2^48) 3842113537 9 Manual.Count131072.C029283.packed 128 cuts29283 = true := by
 decide +kernel
def pointBounds29283 : List (Nat × Nat × Nat) := [(3842138112,104920084194227,104920467342754)]
theorem point_links_checked29283 : (cuts29283.take 1).map (fun c => (3842113537-1+2*2^9*c.k,104920000824123+c.lower,104920383972600+c.upper)) = pointBounds29283 := by
 decide +kernel
def cuts29284 : List PrefixCut := [⟨14,44687254,44687279⟩,
⟨128,431555077,431555321⟩]
theorem checked29284 : checkPrefixCuts (2^48) 3842244609 9 Manual.Count131072.C029284.packed 128 cuts29284 = true := by
 decide +kernel
def pointBounds29284 : List (Nat × Nat × Nat) := [(3842258944,104920481183782,104920864332535)]
theorem point_links_checked29284 : (cuts29284.take 1).map (fun c => (3842244609-1+2*2^9*c.k,104920436496528+c.lower,104920819645256+c.upper)) = pointBounds29284 := by
 decide +kernel
def cuts29285 : List PrefixCut := [⟨4,13625504,13625512⟩,
⟨122,421358360,421358600⟩,
⟨128,441576186,441576437⟩]
theorem checked29285 : checkPrefixCuts (2^48) 3842375681 9 Manual.Count131072.C029285.packed 128 cuts29285 = true := by
 decide +kernel
def pointBounds29285 : List (Nat × Nat × Nat) := [(3842379776,104920881677109,104921264826089),(3842500608,104921289409965,104921672559177)]
theorem point_links_checked29285 : (cuts29285.take 2).map (fun c => (3842375681-1+2*2^9*c.k,104920868051605+c.lower,104921251200577+c.upper)) = pointBounds29285 := by
 decide +kernel
def cuts29286 : List PrefixCut := [⟨112,382887360,382887572⟩,
⟨128,438338059,438338303⟩]
theorem checked29286 : checkPrefixCuts (2^48) 3842506753 9 Manual.Count131072.C029286.packed 128 cuts29286 = true := by
 decide +kernel
def pointBounds29286 : List (Nat × Nat × Nat) := [(3842621440,104921692515151,104922075664586)]
theorem point_links_checked29286 : (cuts29286.take 1).map (fun c => (3842506753-1+2*2^9*c.k,104921309627791+c.lower,104921692777014+c.upper)) = pointBounds29286 := by
 decide +kernel
def cuts29287 : List PrefixCut := [⟨102,340683154,340683349⟩,
⟨128,428507737,428507979⟩]
theorem checked29287 : checkPrefixCuts (2^48) 3842637825 9 Manual.Count131072.C029287.packed 128 cuts29287 = true := by
 decide +kernel
def pointBounds29287 : List (Nat × Nat × Nat) := [(3842742272,104922088649004,104922471798666)]
theorem point_links_checked29287 : (cuts29287.take 1).map (fun c => (3842637825-1+2*2^9*c.k,104921747965850+c.lower,104922131115317+c.upper)) = pointBounds29287 := by
 decide +kernel
def cuts29288 : List PrefixCut := [⟨92,317232908,317233085⟩,
⟨128,437502488,437502733⟩]
theorem checked29288 : checkPrefixCuts (2^48) 3842768897 9 Manual.Count131072.C029288.packed 128 cuts29288 = true := by
 decide +kernel
def pointBounds29288 : List (Nat × Nat × Nat) := [(3842863104,104922493706495,104922876856381)]
theorem point_links_checked29288 : (cuts29288.take 1).map (fun c => (3842768897-1+2*2^9*c.k,104922176473587+c.lower,104922559623296+c.upper)) = pointBounds29288 := by
 decide +kernel
def cuts29289 : List PrefixCut := [⟨82,275473038,275473199⟩,
⟨128,429503885,429504136⟩]
theorem checked29289 : checkPrefixCuts (2^48) 3842899969 9 Manual.Count131072.C029289.packed 128 cuts29289 = true := by
 decide +kernel
def pointBounds29289 : List (Nat × Nat × Nat) := [(3842983936,104922889449113,104923272599228)]
theorem point_links_checked29289 : (cuts29289.take 1).map (fun c => (3842899969-1+2*2^9*c.k,104922613976075+c.lower,104922997126029+c.upper)) = pointBounds29289 := by
 decide +kernel
def cuts29290 : List PrefixCut := [⟨72,250488471,250488612⟩,
⟨128,438131903,438132150⟩]
theorem checked29290 : checkPrefixCuts (2^48) 3843031041 9 Manual.Count131072.C029290.packed 128 cuts29290 = true := by
 decide +kernel
def pointBounds29290 : List (Nat × Nat × Nat) := [(3843104768,104923293968431,104923677118777)]
theorem point_links_checked29290 : (cuts29290.take 1).map (fun c => (3843031041-1+2*2^9*c.k,104923043479960+c.lower,104923426630165+c.upper)) = pointBounds29290 := by
 decide +kernel
def cuts29291 : List PrefixCut := [⟨62,210857496,210857615⟩,
⟨128,429474681,429474927⟩]
theorem checked29291 : checkPrefixCuts (2^48) 3843162113 9 Manual.Count131072.C029291.packed 128 cuts29291 = true := by
 decide +kernel
def pointBounds29291 : List (Nat × Nat × Nat) := [(3843225600,104923692469359,104924075619930)]
theorem point_links_checked29291 : (cuts29291.take 1).map (fun c => (3843162113-1+2*2^9*c.k,104923481611863+c.lower,104923864762315+c.upper)) = pointBounds29291 := by
 decide +kernel
def cuts29292 : List PrefixCut := [⟨52,175989543,175989645⟩,
⟨128,438687745,438687991⟩]
theorem checked29292 : checkPrefixCuts (2^48) 3843293185 9 Manual.Count131072.C029292.packed 128 cuts29292 = true := by
 decide +kernel
def pointBounds29292 : List (Nat × Nat × Nat) := [(3843346432,104924087076087,104924470226887)]
theorem point_links_checked29292 : (cuts29292.take 1).map (fun c => (3843293185-1+2*2^9*c.k,104923911086544+c.lower,104924294237242+c.upper)) = pointBounds29292 := by
 decide +kernel
def cuts29293 : List PrefixCut := [⟨42,139805694,139805770⟩,
⟨128,433546433,433546672⟩]
theorem checked29293 : checkPrefixCuts (2^48) 3843424257 9 Manual.Count131072.C029293.packed 128 cuts29293 = true := by
 decide +kernel
def pointBounds29293 : List (Nat × Nat × Nat) := [(3843467264,104924489579983,104924872731003)]
theorem point_links_checked29293 : (cuts29293.take 1).map (fun c => (3843424257-1+2*2^9*c.k,104924349774289+c.lower,104924732925233+c.upper)) = pointBounds29293 := by
 decide +kernel
def cuts29294 : List PrefixCut := [⟨32,108384309,108384370⟩,
⟨128,429284287,429284529⟩]
theorem checked29294 : checkPrefixCuts (2^48) 3843555329 9 Manual.Count131072.C029294.packed 128 cuts29294 = true := by
 decide +kernel
def pointBounds29294 : List (Nat × Nat × Nat) := [(3843588096,104924891705031,104925274856275)]
theorem point_links_checked29294 : (cuts29294.take 1).map (fun c => (3843555329-1+2*2^9*c.k,104924783320722+c.lower,104925166471905+c.upper)) = pointBounds29294 := by
 decide +kernel
def cuts29295 : List PrefixCut := [⟨22,77990202,77990245⟩,
⟨128,435713828,435714080⟩]
theorem checked29295 : checkPrefixCuts (2^48) 3843686401 9 Manual.Count131072.C029295.packed 128 cuts29295 = true := by
 decide +kernel
def pointBounds29295 : List (Nat × Nat × Nat) := [(3843708928,104925290595211,104925673746679)]
theorem point_links_checked29295 : (cuts29295.take 1).map (fun c => (3843686401-1+2*2^9*c.k,104925212605009+c.lower,104925595756434+c.upper)) = pointBounds29295 := by
 decide +kernel
def cuts29296 : List PrefixCut := [⟨12,40275310,40275334⟩,
⟨128,435698907,435699148⟩]
theorem checked29296 : checkPrefixCuts (2^48) 3843817473 9 Manual.Count131072.C029296.packed 128 cuts29296 = true := by
 decide +kernel
def pointBounds29296 : List (Nat × Nat × Nat) := [(3843829760,104925688594147,104926071745848)]
theorem point_links_checked29296 : (cuts29296.take 1).map (fun c => (3843817473-1+2*2^9*c.k,104925648318837+c.lower,104926031470514+c.upper)) = pointBounds29296 := by
 decide +kernel
def cuts29297 : List PrefixCut := [⟨2,7029642,7029646⟩,
⟨120,404783923,404784154⟩,
⟨128,429386864,429387109⟩]
theorem checked29297 : checkPrefixCuts (2^48) 3843948545 9 Manual.Count131072.C029297.packed 128 cuts29297 = true := by
 decide +kernel
def pointBounds29297 : List (Nat × Nat × Nat) := [(3843950592,104926091047386,104926474199308),(3844071424,104926488801667,104926871953816)]
theorem point_links_checked29297 : (cuts29297.take 2).map (fun c => (3843948545-1+2*2^9*c.k,104926084017744+c.lower,104926467169662+c.upper)) = pointBounds29297 := by
 decide +kernel
def cuts29298 : List PrefixCut := [⟨110,377239141,377239356⟩,
⟨128,437206849,437207096⟩]
theorem checked29298 : checkPrefixCuts (2^48) 3844079617 9 Manual.Count131072.C029298.packed 128 cuts29298 = true := by
 decide +kernel
def pointBounds29298 : List (Nat × Nat × Nat) := [(3844192256,104926890643749,104927273796127)]
theorem point_links_checked29298 : (cuts29298.take 1).map (fun c => (3844079617-1+2*2^9*c.k,104926513404608+c.lower,104926896556771+c.upper)) = pointBounds29298 := by
 decide +kernel
def cuts29299 : List PrefixCut := [⟨100,338347280,338347468⟩,
⟨128,434189955,434190196⟩]
theorem checked29299 : checkPrefixCuts (2^48) 3844210689 9 Manual.Count131072.C029299.packed 128 cuts29299 = true := by
 decide +kernel
def pointBounds29299 : List (Nat × Nat × Nat) := [(3844313088,104927288958737,104927672111335)]
theorem point_links_checked29299 : (cuts29299.take 1).map (fun c => (3844210689-1+2*2^9*c.k,104926950611457+c.lower,104927333763867+c.upper)) = pointBounds29299 := by
 decide +kernel
def cuts29300 : List PrefixCut := [⟨90,296309567,296309731⟩,
⟨128,422899763,422899999⟩]
theorem checked29300 : checkPrefixCuts (2^48) 3844341761 9 Manual.Count131072.C029300.packed 128 cuts29300 = true := by
 decide +kernel
def pointBounds29300 : List (Nat × Nat × Nat) := [(3844433920,104927681110979,104928064263794)]
theorem point_links_checked29300 : (cuts29300.take 1).map (fun c => (3844341761-1+2*2^9*c.k,104927384801412+c.lower,104927767954063+c.upper)) = pointBounds29300 := by
 decide +kernel
def cuts29301 : List PrefixCut := [⟨80,270528290,270528444⟩,
⟨128,435038908,435039153⟩]
theorem checked29301 : checkPrefixCuts (2^48) 3844472833 9 Manual.Count131072.C029301.packed 128 cuts29301 = true := by
 decide +kernel
def pointBounds29301 : List (Nat × Nat × Nat) := [(3844554752,104928078229465,104928461382506)]
theorem point_links_checked29301 : (cuts29301.take 1).map (fun c => (3844472833-1+2*2^9*c.k,104927807701175+c.lower,104928190854062+c.upper)) = pointBounds29301 := by
 decide +kernel
def cuts29302 : List PrefixCut := [⟨70,239477417,239477551⟩,
⟨128,438172193,438172436⟩]
theorem checked29302 : checkPrefixCuts (2^48) 3844603905 9 Manual.Count131072.C029302.packed 128 cuts29302 = true := by
 decide +kernel
def pointBounds29302 : List (Nat × Nat × Nat) := [(3844675584,104928482217500,104928865370766)]
theorem point_links_checked29302 : (cuts29302.take 1).map (fun c => (3844603905-1+2*2^9*c.k,104928242740083+c.lower,104928625893215+c.upper)) = pointBounds29302 := by
 decide +kernel
def cuts29303 : List PrefixCut := [⟨60,204548464,204548574⟩,
⟨128,432300573,432300813⟩]
theorem checked29303 : checkPrefixCuts (2^48) 3844734977 9 Manual.Count131072.C029303.packed 128 cuts29303 = true := by
 decide +kernel
def pointBounds29303 : List (Nat × Nat × Nat) := [(3844796416,104928885460740,104929268614225)]
theorem point_links_checked29303 : (cuts29303.take 1).map (fun c => (3844734977-1+2*2^9*c.k,104928680912276+c.lower,104929064065651+c.upper)) = pointBounds29303 := by
 decide +kernel
def cuts29304 : List PrefixCut := [⟨50,166986298,166986391⟩,
⟨128,432798176,432798421⟩]
theorem checked29304 : checkPrefixCuts (2^48) 3844866049 9 Manual.Count131072.C029304.packed 128 cuts29304 = true := by
 decide +kernel
def pointBounds29304 : List (Nat × Nat × Nat) := [(3844917248,104929280199147,104929663352855)]
theorem point_links_checked29304 : (cuts29304.take 1).map (fun c => (3844866049-1+2*2^9*c.k,104929113212849+c.lower,104929496366464+c.upper)) = pointBounds29304 := by
 decide +kernel
def cuts29305 : List PrefixCut := [⟨40,135722246,135722322⟩,
⟨128,428757226,428757470⟩]
theorem checked29305 : checkPrefixCuts (2^48) 3844997121 9 Manual.Count131072.C029305.packed 128 cuts29305 = true := by
 decide +kernel
def pointBounds29305 : List (Nat × Nat × Nat) := [(3845038080,104929681733271,104930064887207)]
theorem point_links_checked29305 : (cuts29305.take 1).map (fun c => (3844997121-1+2*2^9*c.k,104929546011025+c.lower,104929929164885+c.upper)) = pointBounds29305 := by
 decide +kernel
def cuts29306 : List PrefixCut := [⟨30,103069408,103069463⟩,
⟨128,438698099,438698339⟩]
theorem checked29306 : checkPrefixCuts (2^48) 3845128193 9 Manual.Count131072.C029306.packed 128 cuts29306 = true := by
 decide +kernel
def pointBounds29306 : List (Nat × Nat × Nat) := [(3845158912,104930077837659,104930460991818)]
theorem point_links_checked29306 : (cuts29306.take 1).map (fun c => (3845128193-1+2*2^9*c.k,104929974768251+c.lower,104930357922355+c.upper)) = pointBounds29306 := by
 decide +kernel
def cuts29307 : List PrefixCut := [⟨20,67856686,67856723⟩,
⟨128,431655988,431656230⟩]
theorem checked29307 : checkPrefixCuts (2^48) 3845259265 9 Manual.Count131072.C029307.packed 128 cuts29307 = true := by
 decide +kernel
def pointBounds29307 : List (Nat × Nat × Nat) := [(3845279744,104930481323036,104930864477417)]
theorem point_links_checked29307 : (cuts29307.take 1).map (fun c => (3845259265-1+2*2^9*c.k,104930413466350+c.lower,104930796620694+c.upper)) = pointBounds29307 := by
 decide +kernel
def cuts29308 : List PrefixCut := [⟨10,33085454,33085473⟩,
⟨128,436984642,436984891⟩]
theorem checked29308 : checkPrefixCuts (2^48) 3845390337 9 Manual.Count131072.C029308.packed 128 cuts29308 = true := by
 decide +kernel
def pointBounds29308 : List (Nat × Nat × Nat) := [(3845400576,104930878207792,104931261362397),(3845521408,104931282106980,104931665261815)]
theorem point_links_checked29308 : (cuts29308.take 2).map (fun c => (3845390337-1+2*2^9*c.k,104930845122338+c.lower,104931228276924+c.upper)) = pointBounds29308 := by
 decide +kernel
def cuts29309 : List PrefixCut := [⟨118,402349374,402349602⟩,
⟨128,437189294,437189540⟩]
theorem checked29309 : checkPrefixCuts (2^48) 3845521409 9 Manual.Count131072.C029309.packed 128 cuts29309 = true := by
 decide +kernel
def pointBounds29309 : List (Nat × Nat × Nat) := [(3845642240,104931684456354,104932067611417)]
theorem point_links_checked29309 : (cuts29309.take 1).map (fun c => (3845521409-1+2*2^9*c.k,104931282106980+c.lower,104931665261815+c.upper)) = pointBounds29309 := by
 decide +kernel
def cuts29310 : List PrefixCut := [⟨108,364056828,364057033⟩,
⟨128,430806761,430807006⟩]
theorem checked29310 : checkPrefixCuts (2^48) 3845652481 9 Manual.Count131072.C029310.packed 128 cuts29310 = true := by
 decide +kernel
def pointBounds29310 : List (Nat × Nat × Nat) := [(3845763072,104932083353102,104932466508388)]
theorem point_links_checked29310 : (cuts29310.take 1).map (fun c => (3845652481-1+2*2^9*c.k,104931719296274+c.lower,104932102451355+c.upper)) = pointBounds29310 := by
 decide +kernel
def cuts29311 : List PrefixCut := [⟨98,335647357,335647543⟩,
⟨128,433866073,433866314⟩]
theorem checked29311 : checkPrefixCuts (2^48) 3845783553 9 Manual.Count131072.C029311.packed 128 cuts29311 = true := by
 decide +kernel
def pointBounds29311 : List (Nat × Nat × Nat) := [(3845883904,104932485750392,104932868905904)]
theorem point_links_checked29311 : (cuts29311.take 1).map (fun c => (3845783553-1+2*2^9*c.k,104932150103035+c.lower,104932533258361+c.upper)) = pointBounds29311 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000290
